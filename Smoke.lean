/-
  Smoke tests for lean-black.

  Three scenes that exercise what the synthesis is supposed to give:

  1. **Level 0 baseline.** Plain arithmetic, no reflection. Sanity
     check that the interpreter still works for non-reflective
     programs.

  2. **Single-level reflection (lean-green parity).** From level 0,
     `(em ...)` shifts to level 1 and `set!`s `base-apply` there to
     install multn. Subsequent level-0 application of `(2 3 4)`
     dispatches through level 1's mutated `base-apply` and returns
     `24`. `(+ 1 2)` still returns `3`.

  3. **Two-level reflection (the lean-grey thing lean-green
     couldn't do).** From level 0, `(em (em ...))` shifts to level 2
     and `set!`s level 2's `base-apply` to install multn at level 1
     (because level 1's `applyVia` reads from level 2). Then a level-0
     application of `(+ 1 2)` first goes through level 1's apply
     (still `builtinBaseApply`), which dispatches as before — so
     level 1's behavior is unchanged. But an `(em ...)` from level 0
     to level 1 followed by `(2 3 4)` evaluated at level 1 routes
     through level 2's installed multn, returning `24`. This exercises
     the full cross-level cascade — multn-at-level-1 was installed
     from level 2.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval

def fuel : Nat := 10000

/-! ## Policy table for the demo

    `materializeStep` defaults newly-materialized levels to
    `rejectAllPolicy` (UnivSoundAt by vacuity). To demonstrate
    behaviors that require a permissive gate (multn install,
    ungoverned bad-mod), tests explicitly install
    `acceptAllPolicy` (= ptable[0]) at the relevant level via
    `(em ... (installPolicy 0))`. -/

def smokeTable : PolicyTable := [acceptAllPolicy]

/-- Install acceptAllPolicy at level 1 (from level 0). -/
def acceptAtLevel1 : Expr := .em (.installPolicy 0)

/-- Install acceptAllPolicy at level 2 (from level 0). -/
def acceptAtLevel2 : Expr := .em (.em (.installPolicy 0))

/-! ## Programs (shared) -/

/-- The multn wrapper, identical to lean-green's. Detects `num?`
    in operator position and returns a foldl-* of (op :: args). -/
def multnWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.primApp (.var "mul-list")
        [.primApp (.var "cons") [.var "op", .var "args"]])
      (.primApp (.var "orig") [.var "op", .var "args"])

/-- Install multn at the *next* level (one `em` up):
    `(em (let ((orig base-apply)) (set! base-apply <wrapper>)))`. -/
def installMultnOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" multnWrapper

/-- Install multn *two levels up*: same shape but wrapped in an
    extra `em`. From level 0, this installs at level 2 (which
    governs how level 1 apply-dispatches). -/
def installMultnTwoUp : Expr :=
  .em installMultnOneUp

/-! ## Scene 1: level 0 baseline -/

def test_plus : Option Val :=
  evalProgram fuel [] (.app [.var "+", .num 1, .num 2])

def test_no_multn : Option Val :=
  evalProgram fuel [] (.app [.num 2, .num 3, .num 4])

/-! ## Scene 2: single-level reflection -/

def test_multn_oneup : Option Val :=
  evalProgram fuel smokeTable <|
    .seq [acceptAtLevel1, installMultnOneUp, .app [.num 2, .num 3, .num 4]]

def test_oneup_preserves_plus : Option Val :=
  evalProgram fuel smokeTable <|
    .seq [acceptAtLevel1, installMultnOneUp, .app [.var "+", .num 1, .num 2]]

/-! ## Scene 3: two-level reflection (the new thing) -/

/-- Install multn at level 2 (from level 0). Level 1's apply rule is
    now multn-at-level-1. To observe this, we need to do an
    application at level 1 — which we do by `(em ...)`. -/
def test_multn_twoup : Option Val :=
  evalProgram fuel smokeTable <|
    .seq [acceptAtLevel2, installMultnTwoUp,
          .em (.app [.num 2, .num 3, .num 4])]

/-- Two-level multn install does NOT change level 0's apply
    behavior, because level 0 dispatches through level 1's
    `base-apply` (still `builtinBaseApply` — only level 2's was
    rewired). -/
def test_twoup_preserves_level0 : Option Val :=
  evalProgram fuel smokeTable <|
    .seq [acceptAtLevel2, installMultnTwoUp, .app [.num 2, .num 3, .num 4]]

/-! ## Scene 4: governance gates set! at the level it happens

    A malicious `(em (set! base-apply <bad>))` under
    `acceptAllPolicy` (default) succeeds and breaks `+` at level 0.
    Under `rejectAllPolicy` installed at level 1 (via
    `(em (installPolicy ...))`), the same `set!` is refused and
    `+` is preserved. -/

/-- A malicious closure: ignores its arguments and returns `0`. -/
def badModWrapper : Expr :=
  .lam ["op", "args"] (.num 0)

def installBadModOneUp : Expr :=
  .em <| .set "base-apply" badModWrapper

/-- Un-governed: explicit `acceptAllPolicy` admits bad-mod,
    level-0 `(+ 1 2)` returns `0`. -/
def test_badmod_breaks_plus_ungoverned : Option Val :=
  evalProgram fuel smokeTable <|
    .seq [acceptAtLevel1, installBadModOneUp,
          .app [.var "+", .num 1, .num 2]]

/-- Governed: `materializeStep`'s default `rejectAllPolicy` at level 1
    refuses the bad-mod. `(+ 1 2)` returns `3`. Demonstrates that
    the safe default protects level 0 from un-installed `.set`s. -/
def test_badmod_refused_governed : Option Val :=
  evalProgram fuel [] <|
    .seq [installBadModOneUp,
          .app [.var "+", .num 1, .num 2]]

/-! ## Runner -/

/-- Render the option-Val outcome as a short string. -/
def shortRepr : Option Val → String
  | none            => "<none>"
  | some (.num n)   => s!"num({n})"
  | some (.bool b)  => s!"bool({b})"
  | some .nilV      => "nilV"
  | some (.cons _ _) => "cons(...)"
  | some (.sym s)   => s!"sym({s})"
  | some (.prim s)  => s!"prim({s})"
  | some (.closure _ _ _) => "<closure>"
  | some .builtinBaseApply => "<builtinBaseApply>"

def runOne (label : String) (expected : String) (actual : Option Val) : IO Unit := do
  let got := shortRepr actual
  let mark := if got == expected then "OK " else "XX "
  IO.println s!"  {mark} {label}: expected {expected}, got {got}"

def main : IO Unit := do
  IO.println "Scene 1: level 0 baseline"
  runOne "(+ 1 2)"     "num(3)"  test_plus
  runOne "(2 3 4)"     "<none>"  test_no_multn
  IO.println ""
  IO.println "Scene 2: single-level reflection (lean-green parity)"
  runOne "install + (2 3 4)"    "num(24)" test_multn_oneup
  runOne "install + (+ 1 2)"    "num(3)"  test_oneup_preserves_plus
  IO.println ""
  IO.println "Scene 3: two-level reflection (the new thing)"
  runOne "install-2up + (em (2 3 4))" "num(24)" test_multn_twoup
  runOne "install-2up + (2 3 4)"      "<none>"  test_twoup_preserves_level0
  IO.println ""
  IO.println "Scene 4: governance"
  runOne "ungoverned bad-mod breaks +" "num(0)" test_badmod_breaks_plus_ungoverned
  runOne "rejectAll @ level 1 saves +" "num(3)" test_badmod_refused_governed
