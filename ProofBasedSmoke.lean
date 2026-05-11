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

/-! ## Scene 5: verified compose — multiple approvals in one list

    `approvedPolicy_soundForCE_weak_strong` doesn't care about list
    structure: as long as every approval in the list binds to the
    queried level, the resulting policy is `SoundForCE_weak_strong`.
    So we can compose a list with multiple independent approvals —
    each individually proved — and the runtime gate admits any
    `.set` matching any of them.

    Here we combine:
    - `identityApproval 1 [] .builtinBaseApply` (the level-1 identity
      mod, proved via `CE_weak_refl`).
    - `sampleMultnApproval` (the multn install at level 1, proved via
      `multnExact_soundForCE_first_install_tower`).

    Both approvals are at level 1; the combined list is sound at
    level 1. The runtime gate admits an identity `.set` (matched by
    the first approval) and a multn-shape `.set` (matched by the
    second), each independently. -/

def composedApprovals : List ApprovedModification :=
  [identityApproval 1 [] .builtinBaseApply, sampleMultnApproval]

/-- The combined approvedPolicy is sound for CE_weak_strong at
    level 1. Follows from `approvedPolicy_soundForCE_weak_strong`
    once we verify all approvals bind to level 1. -/
example :
    BlackPolicy.SoundForCE_weak_strong 1 (approvedPolicy composedApprovals) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  -- composedApprovals = [identity, multn]; check each.
  simp [composedApprovals, identityApproval, sampleMultnApproval,
        multnApproval] at h_mem
  rcases h_mem with h | h <;> subst h <;> rfl

def test_composed_admits_identity : Bool :=
  approvedPolicy composedApprovals smokeIdentityCtx
    .builtinBaseApply .builtinBaseApply
-- Expected: true — matched by identity approval (am.heap = [] is prefix).
-- NOTE: smokeIdentityCtx has level := 0; we need level 1 for this match.
-- Use a level-1 context.

def composedTestCtx : MutationCtx :=
  { target := "base-apply", heap := sampleAdmitHeap,
    env := sampleAdmitCenv, metaEnv := .nil, index := 0, level := 1 }

def test_composed_admits_identity_at_1 : Bool :=
  approvedPolicy composedApprovals composedTestCtx
    .builtinBaseApply .builtinBaseApply

def test_composed_admits_multn : Bool :=
  approvedPolicy composedApprovals composedTestCtx
    .builtinBaseApply sampleMultnClosure

def test_composed_refuses_doubling : Bool :=
  approvedPolicy composedApprovals composedTestCtx
    .builtinBaseApply (.closure ["op", "args"] (.var "op") .nil)
-- Different newVal (not identity, not multn) — refused.

/-! ## Scene 6: a custom modification (Scene B)

    Same `multnApproval` proof template, but applied to a *different*
    modification: a multn-variant that allocates a "log cell" on each
    numeric dispatch. The closure body retains the multn-required
    shape (`.lam ["op","args"] (.ifte (num? op) _ (orig op args))`)
    but the then-branch is rewritten:

      .letE "_log" (.num 1)
        (.primApp (.var "mul-list")
          [.primApp (.var "cons") [.var "op", .var "args"]])

    The `.letE` allocates a heap cell holding `.num 1` before the
    multn fold. The cell is unreachable after the let goes out of
    scope, but it's still in the heap — a *side effect*. Behaviorally
    this differs from canonical multn only by the heap-growth on
    numeric dispatches.

    Why this still admits via `multnApproval`: the multn proof
    template constrains only the closure SHAPE (the `.ifte` outer,
    the else-branch `(orig op args)`, and the cenv lookups). The
    then-branch is unconstrained. The CE_weak_strong premise
    (`callAsBaseApply ... .builtinBaseApply ... = some (r, T')`)
    is vacuous on numeric operators (builtinBaseApply returns `none`
    for `.num` ops), so whatever the then-branch does — multn fold,
    constant 42, log-then-fold — is irrelevant to soundness.

    Concrete payoff: a *novel modification* (with observable side
    effects on the heap) admitted by the existing proof template.
    No bespoke CE_weak_strong proof needed; the multn theorem is the
    proof template, and `multnApproval` packages it for any
    multn-shape closure. -/

def loggingMultnExpr : Expr :=
  .lam ["op", "args"]
    (.ifte (.primApp (.var "num?") [.var "op"])
      (.letE "_log" (.num 1)
        (.primApp (.var "mul-list")
          [.primApp (.var "cons") [.var "op", .var "args"]]))
      (.primApp (.var "orig") [.var "op", .var "args"]))

def loggingMultnClosure : Val :=
  .closure ["op", "args"]
    (.ifte (.primApp (.var "num?") [.var "op"])
      (.letE "_log" (.num 1)
        (.primApp (.var "mul-list")
          [.primApp (.var "cons") [.var "op", .var "args"]]))
      (.primApp (.var "orig") [.var "op", .var "args"]))
    sampleAdmitCenv

theorem logging_multn_admit :
    multnExactPolicy sampleAdmitCtx .builtinBaseApply loggingMultnClosure
      = true := by
  native_decide

/-- The logging-multn approval. Same proof template as
    `sampleMultnApproval`, applied to a different closure. -/
def loggingMultnApproval : ApprovedModification :=
  multnApproval 1 sampleAdmitHeap sampleAdmitCenv .nil 0
    loggingMultnClosure logging_multn_admit

def test_logging_admitted : Bool :=
  approvedPolicy [loggingMultnApproval] sampleAdmitCtx
    .builtinBaseApply loggingMultnClosure

def test_logging_distinct_from_multn : Bool :=
  -- The logging closure is structurally distinct from the canonical
  -- multn closure (different then-branch). Confirm `Val.beq`-distinct.
  ! Val.beq loggingMultnClosure sampleMultnClosure

/-! ## Scene 7: cross-level approval — proof-based at level 2

    `multnApproval` parameterizes on `level`, so the same proof
    template works at any tower level. Here we instantiate the
    approval at **level 2** — gating a `.set` that mutates level-2's
    `base-apply` (which in turn affects level-1's apply-dispatch via
    the cross-level cascade).

    The architectural claim: proof-based admission is uniform across
    the tower. The soundness theorem applies at every level. A
    policy table can hold multiple `approvedPolicy`s — one per level —
    each gating modifications at the level it's installed at.

    We demonstrate:
    - `multnApproval 2 ...` constructs (the kernel accepts the
      `CE_weak_strong 2` proof).
    - `approvedPolicy_soundForCE_weak_strong 2` applies to the
      level-2 approval list.
    - The runtime gate matches a level-2 multn `.set`.

    A natural multi-level table — index 0 admits at level 1, index 1
    admits at level 2 — is also exercised. A real tower run wiring
    both gates would need approvals matching the runtime heap state
    precisely; here we verify the static admission logic. -/

/-- Same sample state, but level := 2. -/
def sampleAdmitCtxLevel2 : MutationCtx :=
  { target := "base-apply", heap := sampleAdmitHeap,
    env := sampleAdmitCenv, metaEnv := .nil, index := 0, level := 2 }

theorem sample_multn_admit_level2 :
    multnExactPolicy sampleAdmitCtxLevel2 .builtinBaseApply sampleMultnClosure
      = true := by
  native_decide

/-- The multn approval at level 2. Same proof template as
    `sampleMultnApproval`, instantiated at a different level. The
    kernel accepts `CE_weak_strong 2 sampleAdmitHeap .builtinBaseApply
    sampleMultnClosure`. -/
def sampleMultnApprovalLevel2 : ApprovedModification :=
  multnApproval 2 sampleAdmitHeap sampleAdmitCenv .nil 0
    sampleMultnClosure sample_multn_admit_level2

def sampleMultnApprovalsLevel2 : List ApprovedModification :=
  [sampleMultnApprovalLevel2]

/-- The level-2 approval list is sound at level 2. -/
example :
    BlackPolicy.SoundForCE_weak_strong 2
      (approvedPolicy sampleMultnApprovalsLevel2) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp [sampleMultnApprovalsLevel2, sampleMultnApprovalLevel2,
        multnApproval] at h_mem
  subst h_mem; rfl

def test_multn_admitted_at_level2 : Bool :=
  approvedPolicy sampleMultnApprovalsLevel2 sampleAdmitCtxLevel2
    .builtinBaseApply sampleMultnClosure

/-- A level-1 ctx is NOT admitted by the level-2 approval list (level
    mismatch — `matches` checks `am.level = ctx.level`). -/
def test_level2_approval_refuses_level1_ctx : Bool :=
  approvedPolicy sampleMultnApprovalsLevel2 sampleAdmitCtx
    .builtinBaseApply sampleMultnClosure

/-! ### Multi-level policy table

    A policy table with one `approvedPolicy` per level. Index 0
    admits at level 1; index 1 admits at level 2. Installed in the
    tower via `(em (installPolicy 0))` and
    `(em (em (installPolicy 1)))`. -/

def crossLevelTable : PolicyTable :=
  [approvedPolicy sampleMultnApprovals,       -- level 1
   approvedPolicy sampleMultnApprovalsLevel2] -- level 2

/-- The level-1 entry is sound at level 1; the level-2 entry is
    sound at level 2. Each composed independently. -/
example :
    BlackPolicy.SoundForCE_weak_strong 1
      (crossLevelTable[0]'(by simp [crossLevelTable])) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp [sampleMultnApprovals, sampleMultnApproval, multnApproval] at h_mem
  subst h_mem; rfl

example :
    BlackPolicy.SoundForCE_weak_strong 2
      (crossLevelTable[1]'(by simp [crossLevelTable])) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp [sampleMultnApprovalsLevel2, sampleMultnApprovalLevel2,
        multnApproval] at h_mem
  subst h_mem; rfl

def test_crosslevel_level1_admits : Bool :=
  approvedPolicy sampleMultnApprovals sampleAdmitCtx
    .builtinBaseApply sampleMultnClosure

def test_crosslevel_level2_admits : Bool :=
  approvedPolicy sampleMultnApprovalsLevel2 sampleAdmitCtxLevel2
    .builtinBaseApply sampleMultnClosure

/-! ## Scene 8: end-to-end multn under proof-based admission (level 1)

    Where Scene 3 verifies the gate function on a hand-crafted ctx,
    this scene runs the full pipeline through `evalProgram`:

      (seq (em (installPolicy 0))                   -- install gate at level 1
           (em (let ((orig base-apply))
                 (set! base-apply <multn>)))         -- gated set! at level 1
           (2 3 4))                                  -- post-admission, level 0

    For the gate to admit the runtime-produced `.set`, the approval's
    `newVal` must `Val.beq`-equal what eval actually constructs at the
    `.lam` rule. Since `freshLevelEnv` is a deterministic Lean function,
    we just re-run it here in pure code to obtain the same cenv that
    the evaluator captures — no instrumentation needed. -/

/-- Body of the multn wrapper — identical to `Smoke.lean`'s. -/
def multnWrapperBody : Expr :=
  .ifte (.primApp (.var "num?") [.var "op"])
    (.primApp (.var "mul-list")
      [.primApp (.var "cons") [.var "op", .var "args"]])
    (.primApp (.var "orig") [.var "op", .var "args"])

def multnWrapper : Expr := .lam ["op", "args"] multnWrapperBody

def installMultnOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" multnWrapper

def installMultnTwoUp : Expr := .em installMultnOneUp

def installApprovedAt2 : Expr := .em (.em (.installPolicy 0))

/-- Re-derive runtime state by re-running `freshLevelEnv`. -/
def level0Heap : Heap := (freshLevelEnv []).1
def level1Heap : Heap := (freshLevelEnv level0Heap).1
def level1Env  : Env  := (freshLevelEnv level0Heap).2
def level2Heap : Heap := (freshLevelEnv level1Heap).1
def level2Env  : Env  := (freshLevelEnv level1Heap).2

/-- Heap after the level-1 `letE` alloc'd a `.builtinBaseApply` cell
    for `orig`. The cell sits at `level1Heap.length` (= 28). -/
def runtimeHeapLevel1 : Heap := level1Heap ++ [.builtinBaseApply]

/-- The cenv captured by the multn lambda at level 1: `orig` →
    `level1Heap.length`, then the rest of level 1's env. -/
def runtimeCenvLevel1 : Env := .cons "orig" level1Heap.length level1Env

/-- The runtime-elaborated multn closure at level 1, byte-identical
    to what `eval` produces. -/
def runtimeMultnClosureLevel1 : Val :=
  .closure ["op", "args"] multnWrapperBody runtimeCenvLevel1

theorem h_admit_multn_level1 :
    multnExactPolicy
        { target := "base-apply", heap := runtimeHeapLevel1, env := .nil,
          metaEnv := .nil, index := 27, level := 1 }
        .builtinBaseApply runtimeMultnClosureLevel1 = true := by
  native_decide

def runtimeMultnApprovalLevel1 : ApprovedModification :=
  multnApproval 1 runtimeHeapLevel1 .nil .nil 27
    runtimeMultnClosureLevel1 h_admit_multn_level1

def proofBasedMultnTableLevel1 : PolicyTable :=
  [approvedPolicy [runtimeMultnApprovalLevel1]]

def test_sceneA_admit : Option Val :=
  evalProgram fuel proofBasedMultnTableLevel1 <|
    .seq [installApprovedAt1, installMultnOneUp]

def test_sceneA_compute : Option Val :=
  evalProgram fuel proofBasedMultnTableLevel1 <|
    .seq [installApprovedAt1, installMultnOneUp,
          .app [.num 2, .num 3, .num 4]]

def test_sceneA_preserves_plus : Option Val :=
  evalProgram fuel proofBasedMultnTableLevel1 <|
    .seq [installApprovedAt1, installMultnOneUp,
          .app [.var "+", .num 1, .num 2]]

/-! ## Scene 9: end-to-end multn under proof-based admission (level 2)

    Same shape as Scene 8, but the `set!` happens at level 2 (via
    `(em (em ...))`). The modification at level 2 affects how level 1
    dispatches; we observe this by evaluating `(em (2 3 4))`, which
    triggers a level-1 application that routes through level 2's
    (now-multn) base-apply, returning `24`. -/

/-- Heap after letE alloc at level 2: cell at `level2Heap.length` (= 42). -/
def runtimeHeapLevel2 : Heap := level2Heap ++ [.builtinBaseApply]

def runtimeCenvLevel2 : Env := .cons "orig" level2Heap.length level2Env

def runtimeMultnClosureLevel2 : Val :=
  .closure ["op", "args"] multnWrapperBody runtimeCenvLevel2

theorem h_admit_multn_level2 :
    multnExactPolicy
        { target := "base-apply", heap := runtimeHeapLevel2, env := .nil,
          metaEnv := .nil, index := 41, level := 2 }
        .builtinBaseApply runtimeMultnClosureLevel2 = true := by
  native_decide

def runtimeMultnApprovalLevel2 : ApprovedModification :=
  multnApproval 2 runtimeHeapLevel2 .nil .nil 41
    runtimeMultnClosureLevel2 h_admit_multn_level2

def proofBasedMultnTableLevel2 : PolicyTable :=
  [approvedPolicy [runtimeMultnApprovalLevel2]]

def test_sceneB_admit : Option Val :=
  evalProgram fuel proofBasedMultnTableLevel2 <|
    .seq [installApprovedAt2, installMultnTwoUp]

def test_sceneB_compute : Option Val :=
  evalProgram fuel proofBasedMultnTableLevel2 <|
    .seq [installApprovedAt2, installMultnTwoUp,
          .em (.app [.num 2, .num 3, .num 4])]

def test_sceneB_preserves_level0 : Option Val :=
  evalProgram fuel proofBasedMultnTableLevel2 <|
    .seq [installApprovedAt2, installMultnTwoUp,
          .app [.num 2, .num 3, .num 4]]

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
  IO.println ""
  IO.println "Scene 5: verified compose — [identity, multn] coexist"
  IO.println s!"  {if test_composed_admits_identity_at_1 then "OK " else "XX "} composed list admits identity at level 1: expected true, got {test_composed_admits_identity_at_1}"
  IO.println s!"  {if test_composed_admits_multn then "OK " else "XX "} composed list admits multn at level 1: expected true, got {test_composed_admits_multn}"
  IO.println s!"  {if test_composed_refuses_doubling then "XX " else "OK "} composed list refuses doubling: expected false, got {test_composed_refuses_doubling}"
  IO.println ""
  IO.println "Scene 6: custom modification (logging-multn) — same template, novel mod"
  IO.println s!"  {if test_logging_admitted then "OK " else "XX "} logging-multn admits via multnApproval: expected true, got {test_logging_admitted}"
  IO.println s!"  {if test_logging_distinct_from_multn then "OK " else "XX "} logging closure distinct from canonical multn (Val.beq false): expected true, got {test_logging_distinct_from_multn}"
  IO.println ""
  IO.println "Scene 7: cross-level — proof-based admission at level 2"
  IO.println s!"  {if test_multn_admitted_at_level2 then "OK " else "XX "} multn approval at level 2 admits level-2 ctx: expected true, got {test_multn_admitted_at_level2}"
  IO.println s!"  {if test_level2_approval_refuses_level1_ctx then "XX " else "OK "} level-2 approval REFUSES level-1 ctx (level mismatch): expected false, got {test_level2_approval_refuses_level1_ctx}"
  IO.println s!"  {if test_crosslevel_level1_admits then "OK " else "XX "} multi-level table index 0 admits at level 1: expected true, got {test_crosslevel_level1_admits}"
  IO.println s!"  {if test_crosslevel_level2_admits then "OK " else "XX "} multi-level table index 1 admits at level 2: expected true, got {test_crosslevel_level2_admits}"
  IO.println ""
  IO.println "Scene 8: end-to-end multn at level 1 (gate fires, (2 3 4) ⇒ 24)"
  runOne "(em (set! base-apply <multn>)) ⇒ bool(true)"
         "bool(true)" test_sceneA_admit
  runOne "post-admit, (2 3 4) ⇒ num(24)"
         "num(24)"    test_sceneA_compute
  runOne "post-admit, (+ 1 2) still num(3)"
         "num(3)"     test_sceneA_preserves_plus
  IO.println ""
  IO.println "Scene 9: end-to-end multn at level 2 (gate fires, (em (2 3 4)) ⇒ 24)"
  runOne "(em (em (set! base-apply <multn>))) ⇒ bool(true)"
         "bool(true)" test_sceneB_admit
  runOne "post-admit, (em (2 3 4)) ⇒ num(24) via level-1 dispatch"
         "num(24)"    test_sceneB_compute
  runOne "post-admit, level-0 (2 3 4) still <none> (unchanged)"
         "<none>"     test_sceneB_preserves_level0
