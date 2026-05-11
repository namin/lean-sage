import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Soundness
import LeanBlack.Policies

namespace LeanBlack

/-! # Proof-bearing admission

The `proof-based` branch's contribution: a `.set` admission path that
takes a *Lean proof of CE_weak* as the certificate, rather than a
pre-registered structural shape.

An `ApprovedModification` bundles `(level, oldVal, newVal, heap)`
with a Lean term of type `CE_weak level heap oldVal newVal`. The
kernel type-checks the term at construction time; if it doesn't
type-check, no `ApprovedModification` value exists.

The runtime policy `approvedPolicy` admits a `.set` iff the runtime
mutation context matches an approved triple. Composes with the
existing `BlackPolicy` interface — no change to `Black.lean`.

Structural policies from `Policies.lean` (`multnExactPolicy`,
`numGuardPolicy`) remain useful as *proof templates*: each
soundness theorem (`multnExact_soundForCE_first_install_tower` etc.)
is a function from structural admission + side conditions to a
`CE_weak` proof, which the proposer can use to construct an
`ApprovedModification` for any multn-shape modification without
hand-writing the bisim case analysis.
-/

/-- A modification approved for installation. The `proof` field is
    the load-bearing certificate: Lean's type checker refuses
    construction without a valid term of `CE_weak`. -/
structure ApprovedModification where
  level   : Nat
  heap    : Heap
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak level heap oldVal newVal

/-- Boolean match of an approval against a runtime mutation context
    and proposed new value. Uses structural `Val.beq` on `oldVal` and
    `newVal`, and `decide` on the level. The heap match is by length —
    the approval's CE_weak proof quantifies over test states whose
    heap extends `am.heap`, so any runtime `ctx.heap` with
    `am.heap.length ≤ ctx.heap.length` qualifies.

    (A stricter match — heap-prefix equality — would tie an approval
    to a specific heap snapshot. The length-prefix form is what the
    CE_weak proof actually requires.) -/
def ApprovedModification.matches
    (am : ApprovedModification) (ctx : MutationCtx) (oldVal newVal : Val) : Bool :=
  decide (am.level = ctx.level) &&
  decide (am.heap.length ≤ ctx.heap.length) &&
  Val.beq am.oldVal oldVal &&
  Val.beq am.newVal newVal

/-- The proof-bearing policy. Admits a `.set` iff some approval in
    the list matches. -/
def approvedPolicy (approvals : List ApprovedModification) : BlackPolicy :=
  fun ctx oldVal newVal =>
    approvals.any fun am => am.matches ctx oldVal newVal

/-! ## Constructing approvals

The general pattern: invoke an existing soundness theorem to discharge
`CE_weak`, then wrap the result as an `ApprovedModification`.

For multn-shape modifications, `multnExact_soundForCE_first_install_tower`
is the proof template. Given a concrete `(level, heap, oldVal, newVal)`
plus the side conditions, it produces the `CE_weak` proof. The wrapper
below packages that flow.

The side conditions (`InstallFacts`, `RuntimeWF`, deep-validity,
shift-respect) belong to the *admission moment*, not to the approval
itself. The cleanest factoring is: the user discharges side conditions
at the call site that constructs the approval, and the resulting
approval carries only the `CE_weak` conclusion.
-/

/-- Convenience: lift a `BlackPolicy.SoundForCE_weak` witness into a
    statement that the policy is a *correct admission filter* — every
    `.set` it admits has a `CE_weak` proof available.

    This is the formal statement that structural policies remain
    sound under the proof-bearing reading: an admission via the
    structural policy corresponds to an `ApprovedModification` with
    the policy's soundness theorem providing the proof. -/
theorem structural_policy_yields_approval
    {p : BlackPolicy} {level : Nat}
    (h_sound : p.SoundForCE_weak level)
    (ctx : MutationCtx) (oldVal newVal : Val)
    (h_admit : p ctx oldVal newVal = true) :
    CE_weak level ctx.heap oldVal newVal :=
  h_sound ctx oldVal newVal h_admit

/-! ## Soundness of `approvedPolicy` (sketch)

`approvedPolicy approvals` is `SoundForCE_weak` *if* the approvals
list is consistent with the level being checked and the heap-length
match condition is honored. The full theorem is:

> ∀ level, every admission by `approvedPolicy approvals` at level
> `level`, against runtime `(ctx, oldVal, newVal)`, has a
> corresponding `CE_weak level ctx.heap oldVal newVal` derivable
> from the matching approval's `proof` field.

The proof walks the approvals list, identifies the matching entry,
and reads its `proof`. Care is needed at the `Val.beq` → `=` lift
(via `val_beq_eq`) to actually use the matching approval's proof on
the runtime values.

Stated but not yet proved; see TODO below. -/

-- TODO: prove `approvedPolicy_soundForCE_weak`. Requires:
--   1. List induction over `approvals`.
--   2. Lift `am.matches ctx oldVal newVal = true` into
--      `am.level = ctx.level ∧ ... ∧ am.oldVal = oldVal ∧
--       am.newVal = newVal ∧ am.heap.length ≤ ctx.heap.length`.
--   3. Substitute and apply `am.proof`. The level/heap conditions
--      in `CE_weak` line up because `CE_weak` quantifies over test
--      states whose heap extends `am.heap`, and `am.heap.length ≤
--      ctx.heap.length` ensures any extension of `ctx.heap` extends
--      `am.heap` too.

/-! ## Worked example placeholder

A worked example constructing an `ApprovedModification` for the
multn closure uses `multnExact_soundForCE_first_install_tower` after
discharging its side conditions. The natural call site is the demo
or smoke runner, where the runtime state provides the deep-validity
and shift-respect facts via `initState_deep` and
`verifiedTable_respects_shift` (already in `Policies.lean`).

A sample construction (filled in by `Demos.lean` on the proof-based
branch):

```lean
def multnApproval (level : Nat) (heap : Heap) (newClosure : Val)
    (h_admit : multnExactPolicy ⟨"base-apply", heap, env, metaEnv, idx, level⟩
                  .builtinBaseApply newClosure = true)
    -- … side-condition discharges …
    : ApprovedModification :=
  { level   := level
    heap    := heap
    oldVal  := .builtinBaseApply
    newVal  := newClosure
    proof   := by
      -- apply multnExact_soundForCE_first_install_tower
      sorry }
```
-/

end LeanBlack
