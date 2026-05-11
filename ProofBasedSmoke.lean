/-
  Smoke tests for proof-based admission.

  Demonstrates the integration of `approvedPolicy` with the tower
  runtime. The key claim is that `approvedPolicy : BlackPolicy` —
  it slots into `PolicyTable`, gets installed at a level via
  `(installPolicy n)`, and gates `(set! ...)` during evaluation
  exactly like any other `BlackPolicy`. The novelty is in *how*
  the policy was constructed: from a list of `ApprovedModification`s,
  each carrying a Lean term of type `CE_weak_strong`.

  Two scenes:

  1. **Approved identity mod admitted.** Install
     `approvedPolicy [identityApproval 1 [] .builtinBaseApply]` at
     level 1, then run `(em (set! base-apply base-apply))` — an
     identity modification (RHS evaluates to the current value,
     which is `.builtinBaseApply`). The gate consults the approval
     list, the match succeeds, the `.set` returns `.bool true`.
     A subsequent `(+ 1 2)` still returns `3` because the
     modification was identity.

  2. **Non-matching mod refused.** Same setup, but the mutation is
     `(em (set! base-apply (lam (op args) 42)))` — a constant-42
     wrapper. The approval list has only the identity approval; the
     `newVal` mismatch means no approval matches; the gate refuses;
     `.set` returns `.bool false`. The heap is *not* updated, so
     `(+ 1 2)` still returns `3`.

  Run with `lake build proofBasedSmoke && lake exe proofBasedSmoke`.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.ProofBased

open LeanBlack

def fuel : Nat := 10000

/-! ## Approvals + policy table

    One approval: the identity modification on `.builtinBaseApply`
    at level 1, with the admission heap `[]` (trivially a prefix
    of anything). The `proof` field is `CE_weak_to_strong`-widened
    from `CE_weak_refl`.

    Policy table entry index 0 is `approvedPolicy [identity]`;
    `(installPolicy 0)` installs it. -/

def identityApprovals : List ApprovedModification :=
  [identityApproval 1 [] .builtinBaseApply]

def proofBasedTable : PolicyTable :=
  [approvedPolicy identityApprovals]

/-- `(em (installPolicy 0))` at level 0 installs `proofBasedTable[0]`
    at level 1. From level 1's perspective, future `.set` ops will
    consult `approvedPolicy identityApprovals`. -/
def installApprovedAt1 : Expr := .em (.installPolicy 0)

/-! ## Scene 1: admit (identity mod)

    `(em (set! base-apply base-apply))` at level 0:
      - Shift to level 1.
      - At level 1, evaluate `.set "base-apply" (.var "base-apply")`.
      - RHS lookup: `.var "base-apply"` resolves to the current
        cell value `.builtinBaseApply`.
      - `.set` gates: `approvedPolicy identityApprovals ctx
        .builtinBaseApply .builtinBaseApply`. The approval's
        `(level=1, heap=[], oldVal=.builtinBaseApply,
        newVal=.builtinBaseApply)` matches. Gate returns `true`.
      - `.set` returns `.bool true`. Heap cell updated (to the same
        value).

    After: `(+ 1 2)` still returns `3` (identity mod preserves
    arithmetic). -/

def identityModExpr : Expr := .em (.set "base-apply" (.var "base-apply"))

def test_identity_admitted : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, identityModExpr]

def test_identity_preserves_plus : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, identityModExpr,
          .app [.var "+", .num 1, .num 2]]

/-! ## Scene 2: refuse (non-matching mod)

    `(em (set! base-apply (lam (op args) 42)))`:
      - At level 1, evaluate `.set "base-apply" (lam ["op","args"] 42)`.
      - RHS evaluates to a closure value (constant-42).
      - `.set` gates: `approvedPolicy identityApprovals ctx
        .builtinBaseApply <closure>`. No approval matches (newVal
        differs from `.builtinBaseApply`). Gate returns `false`.
      - `.set` returns `.bool false`. Heap *not* updated.

    After: `(+ 1 2)` still returns `3` (no modification in effect). -/

def badModExpr : Expr :=
  .em (.set "base-apply" (.lam ["op", "args"] (.num 42)))

def test_badmod_refused : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, badModExpr]

def test_badmod_preserves_plus : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, badModExpr,
          .app [.var "+", .num 1, .num 2]]

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

/-! ## Scene 3: multn approval constructs and matches

    Build a minimal admission state for the multn shape:
      heap     = [.builtinBaseApply, .prim "num?"]      -- indices 0, 1
      cenv     = orig→0, num?→1                          -- closure env
      newClosure = (λ (op args). if num? op then mul-list (cons op args) else orig op args)

    `multnExactPolicy` admits this combo (verified by `decide`).
    `multnApproval` constructs the `ApprovedModification` (the Lean
    kernel type-checks the `CE_weak_strong` proof). Its `matches`
    returns `true` on the corresponding context.

    This is the keynote-grade artifact: a proof-bearing approval for
    a non-trivial modification (not just identity), with the soundness
    witness piping through `multnExact_soundForCE_first_install_tower`. -/

def sampleAdmitHeap : Heap :=
  [.builtinBaseApply, .prim "num?"]

def sampleAdmitCenv : Env :=
  .cons "orig" 0 (.cons "num?" 1 .nil)

def sampleMultnClosure : Val :=
  .closure ["op", "args"]
    (.ifte (.primApp (.var "num?") [.var "op"])
      (.primApp (.var "mul-list")
        [.primApp (.var "cons") [.var "op", .var "args"]])
      (.primApp (.var "orig") [.var "op", .var "args"]))
    sampleAdmitCenv

def sampleAdmitCtx : MutationCtx :=
  { target := "base-apply", heap := sampleAdmitHeap,
    env := sampleAdmitCenv, metaEnv := .nil, index := 0, level := 1 }

theorem sample_multn_admit :
    multnExactPolicy sampleAdmitCtx .builtinBaseApply sampleMultnClosure = true := by
  native_decide

/-- The multn approval, fully constructed. The kernel accepts the
    `CE_weak_strong` proof field (which threads through fuel splits +
    `multnExact_soundForCE_first_install_tower`). -/
def sampleMultnApproval : ApprovedModification :=
  multnApproval 1 sampleAdmitHeap sampleAdmitCenv .nil 0
    sampleMultnClosure sample_multn_admit

def sampleMultnApprovals : List ApprovedModification :=
  [sampleMultnApproval]

/-- Test: `approvedPolicy [sampleMultnApproval]` admits the multn
    modification on the matching context. -/
def test_multn_admitted : Bool :=
  approvedPolicy sampleMultnApprovals sampleAdmitCtx
    .builtinBaseApply sampleMultnClosure

/-- Test: rejects a different newVal at the same context. -/
def test_multn_refuses_other : Bool :=
  approvedPolicy sampleMultnApprovals sampleAdmitCtx
    .builtinBaseApply (.num 0)

/-! ## Scene 4: disaster demo — doubling wrapper REFUSED

    The doubling wrapper (from `Demos.lean`'s Demo 1) modifies
    observable semantics: every numeric result is doubled. That's
    **not** CE_weak-conservative: `(+ 1 2)` evaluates to `3` under
    `.builtinBaseApply` but `6` under the doubling wrapper.

    Two levels of refusal:

    1. **Runtime refusal.** Install `approvedPolicy [identityApproval]`
       (which only admits the identity modification), then attempt
       `(em (let ((orig base-apply)) (set! base-apply doublingWrapper)))`.
       The gate consults the approval list, finds no match for the
       doubling closure, returns `false`. The `.set` returns
       `bool(false)`. `(+ 1 2)` still returns `3`.

    2. **Compile-time refusal.** Trying to construct an
       `ApprovedModification` for the doubling wrapper requires a
       `CE_weak_strong` proof — which is *unprovable* because doubling
       changes observable behavior. See the commented-out attempt
       below; replacing the `sorry` with any term that type-checks is
       impossible. The kernel refuses the construction. -/

def doublingWrapperExpr : Expr :=
  .lam ["op", "args"] <|
    .letE "result" (.primApp (.var "orig") [.var "op", .var "args"]) <|
      .ifte (.primApp (.var "num?") [.var "result"])
        (.primApp (.var "+") [.var "result", .var "result"])
        (.var "result")

/-- `(em (let ((orig base-apply)) (set! base-apply <doubling>)))` —
    the standard install pattern, but for the doubling wrapper. -/
def installDoublingOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" doublingWrapperExpr

def test_doubling_refused : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, installDoublingOneUp]
-- Expected: bool(false) — approvedPolicy refuses; doubling not in approval list.

def test_doubling_refused_preserves_plus : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, installDoublingOneUp,
          .app [.var "+", .num 1, .num 2]]
-- Expected: num(3) — heap unchanged; base-apply still .builtinBaseApply.

/-!
**Compile-time refusal: a documented unprovable construction.**

The following block sketches what someone trying to admit doubling
would write. The `sorry` is the heart of the disaster: no term of
type `CE_weak_strong level heap .builtinBaseApply doublingWrapperClosure`
exists, because doubling provably changes observable behavior on
numeric operators (see `test_doubling_changes_result` below — without
proof-based admission, doubling makes `(+ 1 2)` return `6`).

```lean
-- This would NOT compile (cannot be made `sorry`-free):
def doublingApproval (heap : Heap) (doublingClosure : Val) :
    ApprovedModification :=
  { level   := 1
    heap    := heap
    oldVal  := .builtinBaseApply
    newVal  := doublingClosure
    proof   := sorry  -- ⟵ unprovable: CE_weak_strong requires
                       --    ValVis_weak between (.num k) and (.num 2k)
                       --    for arithmetic results, but those are
                       --    unrelated under Val.beq.
  }
```

Compare against the runtime-refusal test above: the runtime gate
refuses doubling because *no valid `ApprovedModification` for doubling
can be added to the approval list*. The two refusals are two sides of
the same coin — proof-based admission is fail-closed at construction.
-/

/-- Sanity check: with NO governance (acceptAllPolicy), doubling
    installs and `(+ 1 2)` returns `6`. This is the behavior
    proof-based admission **prevents**. -/
def test_doubling_changes_result : Option Val :=
  evalProgram fuel [acceptAllPolicy] <|
    .seq [.em (.installPolicy 0), installDoublingOneUp,
          .app [.var "+", .num 1, .num 2]]
-- Expected: num(6) — doubled. Diverges from base-apply's num(3).

def main : IO Unit := do
  IO.println "Scene 1: proof-bearing admission — identity mod ADMITTED"
  runOne "(em (set! base-apply base-apply)) ⇒ bool(true)"
         "bool(true)" test_identity_admitted
  runOne "post-admit, (+ 1 2) still 3"
         "num(3)"     test_identity_preserves_plus
  IO.println ""
  IO.println "Scene 2: proof-bearing admission — non-matching mod REFUSED"
  runOne "(em (set! base-apply (lam … 42))) ⇒ bool(false)"
         "bool(false)" test_badmod_refused
  runOne "post-refuse, (+ 1 2) still 3 (no mod in effect)"
         "num(3)"      test_badmod_preserves_plus
  IO.println ""
  IO.println "Scene 3: multn approval constructs + matches"
  IO.println s!"  {if test_multn_admitted then "OK " else "XX "} multnApproval admits multn ctx: expected true, got {test_multn_admitted}"
  IO.println s!"  {if test_multn_refuses_other then "XX " else "OK "} multnApproval refuses non-multn newVal: expected false, got {test_multn_refuses_other}"
  IO.println ""
  IO.println "Scene 4: disaster demo — doubling wrapper REFUSED"
  runOne "doubling refused at level 1: ⇒ bool(false)"
         "bool(false)" test_doubling_refused
  runOne "post-refuse, (+ 1 2) still 3"
         "num(3)"      test_doubling_refused_preserves_plus
  runOne "WITHOUT proof-based gate, doubling changes (+ 1 2) to 6"
         "num(6)"      test_doubling_changes_result
