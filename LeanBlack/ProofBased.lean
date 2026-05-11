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

/-! ## Soundness of `approvedPolicy`

`approvedPolicy approvals` is `SoundForCE_weak` provided all approvals
are at the level being checked. The match condition ensures the
approval's heap is a length-prefix of the runtime heap; the resulting
`CE_weak` proof is monotone in the reference-heap parameter, so we
can lift the approval's CE_weak (over `am.heap`) to a CE_weak over
`ctx.heap`.
-/

/-- `CE_weak` is monotone in the reference heap: shrinking `h_ref` to
    any earlier point (heap of equal or shorter length) gives a
    weaker hypothesis, so the conclusion still holds. Used to lift an
    approval's CE_weak proof (over `am.heap`, the heap snapshot the
    proof was constructed against) to a CE_weak over the current
    runtime heap `ctx.heap`, which is at least as long. -/
theorem CE_weak_heap_mono
    {level : Nat} {h₁ h₂ : Heap} {old new : Val}
    (h_le : h₁.length ≤ h₂.length)
    (h : CE_weak level h₁ old new) :
    CE_weak level h₂ old new := by
  intro fuel ptable op operands T r T' h_T_len
  exact h fuel ptable op operands T r T' (Nat.le_trans h_le h_T_len)

/-- The headline: `approvedPolicy approvals` is sound for `CE_weak`
    at any level whose approvals all bind to that level. The matching
    approval's `proof` field supplies the CE_weak witness; the
    heap-length match plus `CE_weak_heap_mono` shifts the reference
    heap from the approval's snapshot to the runtime heap. -/
theorem approvedPolicy_soundForCE_weak
    (approvals : List ApprovedModification) (level : Nat)
    (h_levels : ∀ am ∈ approvals, am.level = level) :
    (approvedPolicy approvals).SoundForCE_weak level := by
  intro ctx old new h_admit
  unfold approvedPolicy at h_admit
  rw [List.any_eq_true] at h_admit
  obtain ⟨am, h_mem, h_match⟩ := h_admit
  unfold ApprovedModification.matches at h_match
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_match
  obtain ⟨⟨⟨_h_lvl_eq, h_heap_len⟩, h_old_beq⟩, h_new_beq⟩ := h_match
  have h_old_eq : am.oldVal = old := val_beq_eq _ _ h_old_beq
  have h_new_eq : am.newVal = new := val_beq_eq _ _ h_new_beq
  have h_level : am.level = level := h_levels am h_mem
  subst h_old_eq
  subst h_new_eq
  subst h_level
  exact CE_weak_heap_mono h_heap_len am.proof

/-! ## A trivially-CE_weak identity case

The cleanest hand-built `CE_weak` proof: the identity modification at
a `.num n` value. `callAsBaseApply` on a non-builtin, non-closure
`baseApply` reduces to `applyDirect ... [op, listToVal operands] T`
with `baseApply` in the operator slot; for `baseApply = .num n` that
returns `none` by `applyDirect_num_returns_none`. So the premise of
`CE_weak` is unsatisfiable, and the conclusion follows vacuously.

This isn't load-bearing for any real demo, but it validates the
plumbing: the kernel really does accept a hand-built `CE_weak` term
and pipe it through `ApprovedModification` and `approvedPolicy`. -/

theorem CE_weak_num_identity (level : Nat) (h_ref : Heap) (n : Int) :
    CE_weak level h_ref (.num n) (.num n) := by
  intro fuel ptable op operands T r T'
    _h_T_len _h_heap _h_op _h_operands _h_old _h_new
    _h_ptable _h_lvl_pol _h_env _h_pol _h_env_bisim h_call
  unfold callAsBaseApply at h_call
  rw [applyDirect_num_returns_none] at h_call
  exact Option.noConfusion h_call

/-- An `ApprovedModification` for the vacuous identity case. -/
def numIdentityApproval (level : Nat) (heap : Heap) (n : Int) :
    ApprovedModification :=
  { level   := level
    heap    := heap
    oldVal  := .num n
    newVal  := .num n
    proof   := CE_weak_num_identity level heap n }

/-! ## End-to-end plumbing smoke

A static `MutationCtx` with a matching `.num` value; the matching
approval admits it, and the soundness theorem produces a `CE_weak`
witness on demand. No tower runtime needed — this exercises the
admission gate's logic in isolation. -/

/-- A toy mutation context matching `numIdentityApproval`. -/
def smokeIdentityCtx : MutationCtx :=
  { target  := "x"
    heap    := []
    env     := .nil
    metaEnv := .nil
    index   := 0
    level   := 0 }

/-- The approval list with one identity approval at level 0, heap `[]`,
    value `.num 42`. -/
def smokeIdentityApprovals : List ApprovedModification :=
  [numIdentityApproval 0 [] 42]

/-- The policy admits the matching mutation. Decidable boolean check;
    the proof is `rfl` (or `by decide` if `rfl` doesn't quite close
    the `Val.beq` reduction). -/
example :
    approvedPolicy smokeIdentityApprovals
        smokeIdentityCtx (.num 42) (.num 42) = true := by
  decide

/-- The policy refuses a non-matching mutation (wrong `newVal`). -/
example :
    approvedPolicy smokeIdentityApprovals
        smokeIdentityCtx (.num 42) (.num 7) = false := by
  decide

/-- The policy's soundness follows from `approvedPolicy_soundForCE_weak`
    once we verify all approvals bind to level 0 — which they do, by
    construction. -/
example : (approvedPolicy smokeIdentityApprovals).SoundForCE_weak 0 :=
  approvedPolicy_soundForCE_weak smokeIdentityApprovals 0
    (by intro am h_mem
        simp [smokeIdentityApprovals, numIdentityApproval] at h_mem
        subst h_mem; rfl)

/-! ## Worked example placeholder (multn)

The next step is to construct an `ApprovedModification` for the multn
closure using `multnExact_soundForCE_first_install_tower` after
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
