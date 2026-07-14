/-
  SyntaxObserverSmoke — the syntax-observation / β dividing line, run.

  A top-level syntax-sensitive observation extension. Demonstrates on
  concrete evaluation that the *same* syntactic context `(syntax-tag [-])` —
  an ordinary lean-sage `Ctx` — equates the β pair (`(λx.x) 0` vs
  `let x = 0 in x`) under the base evaluator (`wand_beta_ctx_pure_at_start`),
  yet separates it — with distinct ground observations — under `evalF`.

  The load-bearing thing is the **semantic index**, not any restriction on
  `Ctx`: a previously-stuck context (`syntax-tag` unbound in the base) gains
  syntax-inspecting power under `evalF`. A Wand-style counterexample; *not* a
  refutation of `CE_weak_strong` and *not* Wand's full triviality theorem.

  Run: `lake exe syntaxObserverSmoke`  (expect only `OK` lines).
-/

import LeanBlack.SyntaxObserver

open LeanBlack

def check (label : String) (b : Bool) : IO Unit :=
  IO.println s!"{if b then "OK" else "XX"} {label}"

def main : IO Unit := do
  IO.println "── SyntaxObserverSmoke: same Ctx — equated by eval, separated by evalF ──"

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
  check "observer separates the pair (distinct ground observations)" (oRedex != oContr)
