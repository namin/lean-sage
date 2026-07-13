/-
  FexprSmoke — the CE / β dividing line, run.

  A top-level syntax-sensitive observation extension. Demonstrates on
  concrete evaluation that adding a syntactic-reflection observer leaves old
  programs delegated to the base evaluator, yet separates — at *ground*
  type — a β pair (`(λx.x) 0` vs `let x = 0 in x`) that is contextually
  equivalent for every operative-free context (`wand_beta_ctx_pure_at_start`).

  This is a Wand-style β counterexample: it shows the operative-free
  restriction on `contextual_beta_pure`'s context class is load-bearing. It
  is *not* a refutation of `CE_weak_strong` (the operative is not a
  `base-apply` modification) and *not* Wand's full triviality theorem.

  Run: `lake exe fexprSmoke`  (expect only `OK` lines).
-/

import LeanBlack.Fexpr

open LeanBlack

def check (label : String) (b : Bool) : IO Unit :=
  IO.println s!"{if b then "OK" else "XX"} {label}"

def main : IO Unit := do
  IO.println "── FexprSmoke: same base result, separated by a syntax observer ──"

  -- The β pair has the same result under the *base* evaluator.
  let mRedex := evalProgram 100 [acceptAllPolicy] betaRedex        -- (λx.x) 0
  let mContr := evalProgram 100 [acceptAllPolicy] betaContractum   -- let x = 0 in x
  check "base: ((λx.x) 0) ⇓ 0"           (mRedex == some (.num 0))
  check "base: (let x = 0 in x) ⇓ 0"     (mContr == some (.num 0))
  check "base: β pair has same result"   (mRedex == mContr)

  -- The operative form is meaningless in the base language (additive).
  check "base: (syntax-tag ((λx.x) 0)) undefined"
    (evalProgram 100 [acceptAllPolicy] (observe betaRedex) == none)

  -- Off the operative root, the extended evaluator IS the base evaluator.
  check "evalF agrees off operative root: ((λx.x) 0)"
    (evalF 100 [acceptAllPolicy] betaRedex == mRedex)
  check "evalF agrees off operative root: (let x = 0 in x)"
    (evalF 100 [acceptAllPolicy] betaContractum == mContr)

  -- But the operative context separates the pair — at ground type.
  let oRedex := evalF 100 [acceptAllPolicy] (observe betaRedex)
  let oContr := evalF 100 [acceptAllPolicy] (observe betaContractum)
  IO.println s!"   (syntax-tag ((λx.x) 0))      ⇓ {repr oRedex}"
  IO.println s!"   (syntax-tag (let x = 0 in x)) ⇓ {repr oContr}"
  check "operative separates the pair (ground)" (oRedex != oContr)
