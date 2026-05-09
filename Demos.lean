/-
  Cool examples for lean-black.

  Beyond the smoke tests' multn-install pattern, these explore what
  reflective rewiring of `base-apply` lets you do:

  - **Doubling**: every numeric application's result is doubled.
  - **Side-effect counter**: a heap cell counts dispatches.
  - **Selective override**: only addition is intercepted (made into +1).
  - **Identity wrapper**: trivial passthrough — proves transparency.
  - **Three-level cascade**: level-2 install affects level-1 dispatch
    only after `(em ...)` re-routes there.
  - **Reflective REPL of sorts**: nested `(em ...)`s let you read/write
    different levels' env.

  Run with `lake build demos && lake exe demos`.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval

def fuel : Nat := 50000

def demoTable : PolicyTable := [acceptAllPolicy]

def acceptAtLevel0 : Expr := .installPolicy 0
def acceptAtLevel1 : Expr := .em (.installPolicy 0)
def acceptAtLevel2 : Expr := .em (.em (.installPolicy 0))

/-! ## Demo 1: Doubling wrapper

    Every numeric result of any operation is doubled.
    `(+ 1 2)` ⇒ orig returns 3 ⇒ doubled to 6.
    `(* 2 3)` ⇒ orig returns 6 ⇒ doubled to 12.
    Non-numeric results pass through unchanged. -/

def doublingWrapper : Expr :=
  .lam ["op", "args"] <|
    .letE "result" (.primApp (.var "orig") [.var "op", .var "args"]) <|
      .ifte (.primApp (.var "num?") [.var "result"])
        (.primApp (.var "+") [.var "result", .var "result"])
        (.var "result")

def installDoublingOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" doublingWrapper

def demo_double_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installDoublingOneUp, .app [.var "+", .num 1, .num 2]]
-- Expected: num(6)  -- (1+2)*2

def demo_double_times : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installDoublingOneUp, .app [.var "*", .num 5, .num 7]]
-- Expected: num(70)  -- (5*7)*2

/-! ## Demo 2: Identity wrapper (transparency)

    Same shape as doubling but does nothing — passes through orig.
    Tests that the apply pipeline is genuinely transparent: any
    expression's behavior is preserved. -/

def identityWrapper : Expr :=
  .lam ["op", "args"] <|
    .primApp (.var "orig") [.var "op", .var "args"]

def installIdentityOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" identityWrapper

def demo_identity_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installIdentityOneUp, .app [.var "+", .num 4, .num 5]]
-- Expected: num(9)  -- unchanged

/-! ## Demo 3: Triple-folding (multn variant)

    Like multn, but appends a constant `1` then folds:
    `(2 3 4)` ⇒ mul-list[2,3,4,1] = 24, same as multn.
    `(5 7)`   ⇒ mul-list[5,7,1] = 35.
    `(10)`    ⇒ mul-list[10,1] = 10.
    Demonstrates the multn pattern is composable. -/

def triplerWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.primApp (.var "mul-list")
        [.primApp (.var "cons") [.var "op", .var "args"]])
      (.primApp (.var "orig") [.var "op", .var "args"])

def installTriplerOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" triplerWrapper

def demo_tripler_three : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installTriplerOneUp, .app [.num 2, .num 3, .num 4]]
-- Expected: num(24)

def demo_tripler_two : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installTriplerOneUp, .app [.num 5, .num 7]]
-- Expected: num(35)

def demo_tripler_one : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installTriplerOneUp, .app [.num 10]]
-- Expected: num(10)

/-! ## Demo 4: Composition — install A, then install B

    Install multn first, then install doubling on top. The doubling
    wrapper's `orig` captures multn (the prior base-apply). So:
    `(2 3 4)` ⇒ multn returns 24 ⇒ doubling returns 48.
    Demonstrates that installs compose: each new install's `orig`
    captures the previous base-apply state. -/

def multnWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.primApp (.var "mul-list")
        [.primApp (.var "cons") [.var "op", .var "args"]])
      (.primApp (.var "orig") [.var "op", .var "args"])

def installMultnOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" multnWrapper

def demo_compose_multn_then_double : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1,
          installMultnOneUp,
          installDoublingOneUp,
          .app [.num 2, .num 3, .num 4]]
-- Expected: num(48)  -- multn(2,3,4) = 24, doubled = 48

def demo_compose_multn_then_double_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1,
          installMultnOneUp,
          installDoublingOneUp,
          .app [.var "+", .num 1, .num 2]]
-- Expected: num(6)  -- multn delegates + to orig (= 3), doubling makes it 6

/-! ## Demo 5: Reverse the order — double THEN multn

    Order matters. Install doubling first (which doubles every numeric
    result of `orig`), then multn on top. Multn's `orig` captures
    doubling. `(2 3 4)`:
    - multn detects `num?`, computes `mul-list[2,3,4]` = 24.
    - But this multn call's `mul-list` goes via primApp, NOT base-apply,
      so doubling doesn't intercept it. Result: 24.
    `(+ 1 2)`:
    - multn delegates to orig (doubling).
    - orig's orig = builtinBaseApply, which returns 3.
    - doubling's wrapper doubles to 6.
    - Returned to caller. Result: 6. -/

def demo_compose_double_then_multn_nums : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1,
          installDoublingOneUp,
          installMultnOneUp,
          .app [.num 2, .num 3, .num 4]]
-- Expected: num(24)  -- multn handles directly; doubling not invoked

def demo_compose_double_then_multn_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1,
          installDoublingOneUp,
          installMultnOneUp,
          .app [.var "+", .num 1, .num 2]]
-- Expected: num(6)  -- multn delegates; doubling fires on orig's result

/-! ## Demo 6: Three-level meta-meta

    Install multn at level 2 (from level 0). Level 1's apply rule
    becomes multn. Then `(em (* 2 3))` from level 0:
    - Shifts to level 1.
    - Calls (* 2 3) at level 1, which dispatches via level 2's
      base-apply (= multn).
    - multn sees `*` is non-num ⇒ delegates to orig (= builtinBaseApply
      at level 2).
    - Result: 6.
    But `(em (3 4))` from level 0:
    - Shifts to level 1.
    - Calls (3 4) at level 1, which dispatches via level 2's multn.
    - multn sees `3` is num ⇒ mul-list[3,4] = 12.
    - Result: 12.
    Whereas plain `(3 4)` from level 0:
    - Dispatches via level 1's base-apply (still builtinBaseApply).
    - applyDirect on .num returns none.
    - Result: <none>. -/

def installMultnTwoUp : Expr :=
  .em installMultnOneUp

def demo_threelevel_em_times : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel2, installMultnTwoUp,
          .em (.app [.var "*", .num 2, .num 3])]
-- Expected: num(6)

def demo_threelevel_em_apply_num : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel2, installMultnTwoUp,
          .em (.app [.num 3, .num 4])]
-- Expected: num(12)

def demo_threelevel_level0_apply_num_unchanged : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel2, installMultnTwoUp, .app [.num 3, .num 4]]
-- Expected: <none>  -- level 0's apply still uses level 1's untouched base-apply

/-! ## Demo 7: Constant wrapper

    Replace base-apply with `(λ (op args) 42)`. Every application
    returns 42. (This is what the bad-mod scene 4 is, but with 42.)
    Demonstrates that absent governance, you can do anything. -/

def constantWrapper : Expr :=
  .lam ["op", "args"] (.num 42)

def installConstantOneUp : Expr :=
  .em <| .set "base-apply" constantWrapper

def demo_constant_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installConstantOneUp, .app [.var "+", .num 1, .num 2]]
-- Expected: num(42)

def demo_constant_times : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installConstantOneUp, .app [.var "*", .num 100, .num 200]]
-- Expected: num(42)

/-! ## Demo 8: Inspection wrappers (return op or args, not result)

    A wrapper can return ANY Val, not just compute the op-on-args result.
    This makes apply itself reflectable: instead of `(+ 1 2)` ⇒ 3, we can
    have `(+ 1 2)` ⇒ `+` (the operator) or `(+ 1 2)` ⇒ `(1 2)` (the args).
    Useful as a "first-class apply" for meta-programming. -/

/-- A wrapper that just returns the operator. `(+ 1 2)` ⇒ prim "+". -/
def returnOpWrapper : Expr :=
  .lam ["op", "args"] (.var "op")

def installReturnOpOneUp : Expr :=
  .em <| .set "base-apply" returnOpWrapper

def demo_return_op_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installReturnOpOneUp, .app [.var "+", .num 1, .num 2]]
-- Expected: prim(+)

def demo_return_op_num : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installReturnOpOneUp, .app [.num 5, .num 7]]
-- Expected: num(5)  -- since op is .num 5

/-- A wrapper that returns the args list. `(+ 1 2)` ⇒ cons(1, cons(2, nilV)). -/
def returnArgsWrapper : Expr :=
  .lam ["op", "args"] (.var "args")

def installReturnArgsOneUp : Expr :=
  .em <| .set "base-apply" returnArgsWrapper

def demo_return_args : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installReturnArgsOneUp,
          .primApp (.var "car") [.app [.var "+", .num 7, .num 11, .num 13]]]
-- Expected: num(7)  -- args = (7 11 13); car returns 7

def demo_return_args_cdr : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installReturnArgsOneUp,
          .primApp (.var "car")
            [.primApp (.var "cdr") [.app [.var "+", .num 7, .num 11, .num 13]]]]
-- Expected: num(11)  -- (cdr (7 11 13)) = (11 13); car of that = 11

/-! ## Demo 9: Self-modifying wrapper

    The wrapper, when called, modifies level 1's `base-apply` to a
    different wrapper. So the FIRST call uses the original (= orig),
    SUBSEQUENT calls use the new one. This is genuine self-modifying
    code at the apply-rule level — only possible because closures'
    bodies can do `(em (set! base-apply ...))`. -/

/-- After 1st call, level 1's base-apply becomes "constant 999".
    1st call: orig (= builtinBaseApply); subsequent: 999. -/
def selfModWrapper : Expr :=
  .lam ["op", "args"] <|
    .seq [
      -- Install a new wrapper at level 1.
      .em (.set "base-apply" (.lam ["op", "args"] (.num 999))),
      -- This call: still uses orig (captured at install time).
      .primApp (.var "orig") [.var "op", .var "args"]
    ]

def installSelfModOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" selfModWrapper

def demo_selfmod_first_call : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installSelfModOneUp,
          .app [.var "+", .num 1, .num 2]]
-- Expected: num(3) — first call uses orig (= builtinBaseApply)

def demo_selfmod_second_call : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installSelfModOneUp,
          .app [.var "+", .num 1, .num 2],   -- 1st call: 3 (discarded by seq)
          .app [.var "+", .num 1, .num 2]]   -- 2nd call: 999
-- Expected: num(999) — second call uses the swapped wrapper

def demo_selfmod_third_call : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installSelfModOneUp,
          .app [.var "*", .num 100, .num 200], -- 1st call: 20000 (discarded)
          .app [.var "+", .num 1, .num 2],    -- 2nd: 999
          .app [.var "*", .num 7, .num 8]]    -- 3rd: 999 (still using new wrapper)
-- Expected: num(999)

/-! ## Demo 10: Conditional self-install ("lazy multn")

    A wrapper that detects numeric ops and, on first encounter, installs
    multn for future calls. Demonstrates *adaptive* meta-programming:
    behavior changes based on the program's runtime usage pattern. -/

/-- Lazy multn: handles num-op directly via multn fold AND installs a
    proper multn wrapper at level 1 for future calls. -/
def lazyMultnWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.seq [
        -- Install proper multn at level 1 for future calls.
        .em (.set "base-apply" multnWrapper),
        -- Compute this call's result via multn fold.
        .primApp (.var "mul-list")
          [.primApp (.var "cons") [.var "op", .var "args"]]
      ])
      (.primApp (.var "orig") [.var "op", .var "args"])

def installLazyMultnOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" lazyMultnWrapper

def demo_lazy_first_num : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installLazyMultnOneUp,
          .app [.num 2, .num 3, .num 4]]
-- Expected: num(24) — first num call triggers install; lazy-multn computes

def demo_lazy_first_plus : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installLazyMultnOneUp,
          .app [.var "+", .num 5, .num 6]]
-- Expected: num(11) — non-num delegates to orig; multn NOT installed

def demo_lazy_then_num : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installLazyMultnOneUp,
          .app [.num 2, .num 3, .num 4],         -- triggers install: 24 (discarded)
          .app [.num 5, .num 7]]                  -- now via proper multn: 35
-- Expected: num(35)

/-! ## Demo 11: Three-level governance — level-2's reject default protects

    `materializeStep` defaults newly-materialized levels to `rejectAllPolicy`.
    A user who has admitted level-1 mutations (via `(em (installPolicy 0))`)
    might still be protected from level-2 mutations because level-2 was just
    materialized with the safe default.

    `(em (em (set! base-apply X)))` requires level 2's policy to admit.
    Default-rejected → fails → level 1's apply rule preserved → level 0
    arithmetic unaffected. -/

/-- Try to install a constant-666 wrapper at level 2 (governs level 1's apply).
    With default rejectAllPolicy at level 2, this fails. -/
def installConstantTwoUp : Expr :=
  .em (.em (.set "base-apply" (.lam ["op", "args"] (.num 666))))

def demo_l2_reject_protects_l1 : Option Val :=
  -- Permissive at L0 and L1 (so basic ops work + level-1 mutations admitted),
  -- but L2 keeps its default rejectAllPolicy (no acceptAtLevel2).
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel0, acceptAtLevel1,
          installConstantTwoUp,           -- this fails (L2 reject), returns false
          .em (.app [.var "+", .num 1, .num 2])]  -- L1 apply unchanged: orig + still works
-- Expected: num(3) — the level-2 set! was refused, level 1's apply intact

/-- Contrast: with acceptAtLevel2, the install succeeds and breaks level 1.
    `(em (+ 1 2))` then routes through the constant-666 wrapper. -/
def demo_l2_accept_breaks_l1 : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel0, acceptAtLevel1, acceptAtLevel2,
          installConstantTwoUp,
          .em (.app [.var "+", .num 1, .num 2])]
-- Expected: num(666) — level 2 admitted; level 1's apply now const-666

/-! ## Demo 12: Selective fail — kill non-num applications

    Wrapper that allows numeric operator applications (multn-style) but
    fails (returns none) for everything else. Demonstrates that wrappers
    can REFUSE to dispatch — by evaluating to a non-Val (failure). -/

def numOnlyWrapper : Expr :=
  .lam ["op", "args"] <|
    .ifte (.primApp (.var "num?") [.var "op"])
      (.primApp (.var "mul-list")
        [.primApp (.var "cons") [.var "op", .var "args"]])
      -- For non-num: force failure. primApp on .num 0 invokes applyDirect
      -- on .num 0, which returns none. Bypasses applyVia (no recursion).
      (.primApp (.num 0) [.num 0])

def installNumOnlyOneUp : Expr :=
  .em <| .set "base-apply" numOnlyWrapper

def demo_numonly_num : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installNumOnlyOneUp, .app [.num 3, .num 4, .num 5]]
-- Expected: num(60)

def demo_numonly_plus_fails : Option Val :=
  evalProgram fuel demoTable <|
    .seq [acceptAtLevel1, installNumOnlyOneUp, .app [.var "+", .num 1, .num 2]]
-- Expected: <none> — the wrapper forced a failure for + dispatch

/-! ## Runner -/

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
  IO.println "Demo 1: Doubling wrapper (every num result × 2)"
  runOne "(+ 1 2) ⇒ doubled"   "num(6)"  demo_double_plus
  runOne "(* 5 7) ⇒ doubled"   "num(70)" demo_double_times
  IO.println ""
  IO.println "Demo 2: Identity wrapper (transparency)"
  runOne "(+ 4 5) unchanged"   "num(9)"  demo_identity_plus
  IO.println ""
  IO.println "Demo 3: Tripler (multn variant — same as multn)"
  runOne "(2 3 4) tripler"     "num(24)" demo_tripler_three
  runOne "(5 7) tripler"       "num(35)" demo_tripler_two
  runOne "(10) tripler"        "num(10)" demo_tripler_one
  IO.println ""
  IO.println "Demo 4: Compose multn THEN doubling"
  runOne "(2 3 4) multn→double" "num(48)" demo_compose_multn_then_double
  runOne "(+ 1 2) multn→double" "num(6)"  demo_compose_multn_then_double_plus
  IO.println ""
  IO.println "Demo 5: Compose doubling THEN multn"
  runOne "(2 3 4) double→multn" "num(24)" demo_compose_double_then_multn_nums
  runOne "(+ 1 2) double→multn" "num(6)"  demo_compose_double_then_multn_plus
  IO.println ""
  IO.println "Demo 6: Three-level meta-meta (install at L2, observe at L1)"
  runOne "(em (* 2 3)) via L2-multn"   "num(6)"  demo_threelevel_em_times
  runOne "(em (3 4)) via L2-multn"     "num(12)" demo_threelevel_em_apply_num
  runOne "(3 4) at L0 unchanged"       "<none>"  demo_threelevel_level0_apply_num_unchanged
  IO.println ""
  IO.println "Demo 7: Constant wrapper (42 for everything — bad-mod variant)"
  runOne "(+ 1 2) ⇒ 42"        "num(42)" demo_constant_plus
  runOne "(* 100 200) ⇒ 42"    "num(42)" demo_constant_times
  IO.println ""
  IO.println "Demo 8: Inspection wrappers (return op or args, not result)"
  runOne "(+ 1 2) ⇒ op"        "prim(+)" demo_return_op_plus
  runOne "(5 7) ⇒ op"          "num(5)"  demo_return_op_num
  runOne "(car (+ 7 11 13)) ⇒ first arg" "num(7)"  demo_return_args
  runOne "(car (cdr (+ 7 11 13))) ⇒ second arg" "num(11)" demo_return_args_cdr
  IO.println ""
  IO.println "Demo 9: Self-modifying wrapper (1st call orig; later: const 999)"
  runOne "1st call: (+ 1 2)"   "num(3)"   demo_selfmod_first_call
  runOne "2nd call: now 999"   "num(999)" demo_selfmod_second_call
  runOne "3rd call: still 999" "num(999)" demo_selfmod_third_call
  IO.println ""
  IO.println "Demo 10: Lazy multn (auto-installs after first num op)"
  runOne "first num call (2 3 4)"  "num(24)" demo_lazy_first_num
  runOne "first non-num (+ 5 6)"   "num(11)" demo_lazy_first_plus
  runOne "trigger then (5 7)"      "num(35)" demo_lazy_then_num
  IO.println ""
  IO.println "Demo 11: Three-level governance (L2 reject protects L1)"
  runOne "L2 default reject saves L1" "num(3)"   demo_l2_reject_protects_l1
  runOne "L2 accept breaks L1"        "num(666)" demo_l2_accept_breaks_l1
  IO.println ""
  IO.println "Demo 12: Selective fail (num-only wrapper)"
  runOne "(2 3 4) num: ok"     "num(60)"  demo_numonly_num
  runOne "(+ 1 2) non-num: fail" "<none>" demo_numonly_plus_fails
