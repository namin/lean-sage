/-
  FexprSmoke — the CE / β dividing line, run.

  Demonstrates, on concrete evaluation, that lean-sage's *operational*
  conservative extension (behavioral CE) does not imply *equational* CE:
  adding a single syntactic-reflection operative leaves every old program
  unchanged, yet a new operative context distinguishes a β-equal pair —
  Wand 1998 localized in lean-sage's calculus.

  Run: `lake exe fexprSmoke`  (expect only `OK` lines).
-/

import LeanBlack.Fexpr

open LeanBlack

def check (label : String) (b : Bool) : IO Unit :=
  IO.println s!"{if b then "OK" else "XX"} {label}"

def main : IO Unit := do
  IO.println "── FexprSmoke: behavioral CE holds, equational CE fails ──"

  -- The β pair converges to the same value under the *base* evaluator.
  let mRedex := evalProgram 100 [acceptAllPolicy] betaRedex        -- (λx.x) 0
  let mValue := evalProgram 100 [acceptAllPolicy] betaValue        -- 0
  check "base: ((λx.x) 0) ⇓ 0"        (mRedex == some (.num 0))
  check "base: 0 ⇓ 0"                 (mValue == some (.num 0))
  check "base: β pair observationally equal" (mRedex == mValue)

  -- The operative form is meaningless in the base language (additive).
  check "base: (syntax-tag …) undefined"
    (evalProgram 100 [acceptAllPolicy] (observe betaValue) == none)

  -- Under the extended evaluator, old programs are byte-for-byte unchanged.
  check "evalF conservative on ((λx.x) 0)"
    (evalF 100 [acceptAllPolicy] betaRedex == mRedex)
  check "evalF conservative on 0"
    (evalF 100 [acceptAllPolicy] betaValue == mValue)

  -- But the single operative context distinguishes the β-equal pair.
  let oRedex := evalF 100 [acceptAllPolicy] (observe betaRedex)
  let oValue := evalF 100 [acceptAllPolicy] (observe betaValue)
  IO.println s!"   (syntax-tag ((λx.x) 0)) ⇓ {repr oRedex}"
  IO.println s!"   (syntax-tag 0)          ⇓ {repr oValue}"
  check "operative distinguishes the β-equal pair" (oRedex != oValue)
