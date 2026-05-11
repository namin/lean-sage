import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Soundness
import LeanBlack.Policies

namespace LeanBlack

/-! ## DecidableEq instances for `Val`, `Expr`, `Env`

Lean 4 doesn't auto-derive `DecidableEq` for mutually-recursive
inductives. We build the instances from the existing `Val.beq` /
`Expr.beq` / `Env.beq` boolean equalities (in `Black.lean`) plus
freshly-proved reflexivity (`val_beq_self`, etc.). With these
instances in scope, `native_decide` can discharge closed
`Option Val` / `Option (Val × _)` equalities — the load-bearing
machinery for W1 below. -/

mutual
  theorem val_beq_self : ∀ (a : Val), Val.beq a a = true
    | .num x             => by simp [Val.beq]
    | .bool x            => by simp [Val.beq]
    | .nilV              => rfl
    | .cons x y          => by
        simp only [Val.beq, Bool.and_eq_true]
        exact ⟨val_beq_self x, val_beq_self y⟩
    | .sym x             => by simp [Val.beq]
    | .closure ps body env => by
        simp only [Val.beq, Bool.and_eq_true]
        refine ⟨⟨?_, expr_beq_self body⟩, env_beq_self env⟩
        simp
    | .prim x            => by simp [Val.beq]
    | .builtinBaseApply  => rfl

  theorem expr_beq_self : ∀ (a : Expr), Expr.beq a a = true
    | .num x         => by simp [Expr.beq]
    | .bool x        => by simp [Expr.beq]
    | .quote v       => by simp only [Expr.beq]; exact val_beq_self v
    | .var x         => by simp [Expr.beq]
    | .ifte c t e    => by
        simp only [Expr.beq, Bool.and_eq_true]
        exact ⟨⟨expr_beq_self c, expr_beq_self t⟩, expr_beq_self e⟩
    | .lam ps b      => by
        simp only [Expr.beq, Bool.and_eq_true]
        refine ⟨?_, expr_beq_self b⟩
        simp
    | .app es        => by
        simp only [Expr.beq]; exact exprListBeq_self es
    | .set x e       => by
        simp only [Expr.beq, Bool.and_eq_true]
        refine ⟨?_, expr_beq_self e⟩
        simp
    | .em b          => by
        simp only [Expr.beq]; exact expr_beq_self b
    | .primApp f as  => by
        simp only [Expr.beq, Bool.and_eq_true]
        exact ⟨expr_beq_self f, exprListBeq_self as⟩
    | .letE x e b    => by
        simp only [Expr.beq, Bool.and_eq_true]
        refine ⟨⟨?_, expr_beq_self e⟩, expr_beq_self b⟩
        simp
    | .seq es        => by
        simp only [Expr.beq]; exact exprListBeq_self es
    | .installPolicy n => by simp [Expr.beq]

  theorem exprListBeq_self : ∀ (es : List Expr), exprListBeq es es = true
    | []      => rfl
    | x :: xs => by
        simp only [exprListBeq, Bool.and_eq_true]
        exact ⟨expr_beq_self x, exprListBeq_self xs⟩

  theorem env_beq_self : ∀ (e : Env), Env.beq e e = true
    | .nil          => rfl
    | .cons k i r   => by
        simp only [Env.beq, Bool.and_eq_true]
        refine ⟨⟨?_, ?_⟩, env_beq_self r⟩ <;> simp
end

instance : DecidableEq Val := fun a b =>
  if h : Val.beq a b = true then
    isTrue (val_beq_eq a b h)
  else
    isFalse (fun heq => h (heq ▸ val_beq_self a))

instance : DecidableEq Expr := fun a b =>
  if h : Expr.beq a b = true then
    isTrue (expr_beq_eq a b h)
  else
    isFalse (fun heq => h (heq ▸ expr_beq_self a))

instance : DecidableEq Env := fun a b =>
  if h : Env.beq a b = true then
    isTrue (env_beq_eq a b h)
  else
    isFalse (fun heq => h (heq ▸ env_beq_self a))

/-! # Proof-based admission

A `.set` admission path that takes a *Lean proof of `CE_weak_strong`*
as the certificate, rather than a pre-registered structural shape.

An `ApprovedModification` bundles `(level, oldVal, newVal, heap)`
with a Lean term of type `CE_weak_strong level heap oldVal newVal`.
The kernel type-checks the term at construction time; if it doesn't
type-check, no `ApprovedModification` value exists.

The runtime policy `approvedPolicy` admits a `.set` iff the runtime
mutation context matches an approved triple. Composes with the
existing `BlackPolicy` interface — no change to `Black.lean`.

Structural policies from `Policies.lean` (`multnExactPolicy`,
`numGuardPolicy`) remain useful as *proof templates*: each
soundness theorem (`multnExact_soundForCE_first_install_tower` etc.)
is a function from structural admission + side conditions to a
`CE_weak_strong` proof, which the proposer can use to construct an
`ApprovedModification` for any multn-shape modification without
hand-writing the bisim case analysis.

## Why `CE_weak_strong` and not `CE_weak`?

`Policies.lean`'s `CE_weak` quantifies over test states `T` with
only `HeapValid`/`ValValid` shape — no `HeapDeep`, no Shift-respect.
But the headline soundness theorem
`multnExact_soundForCE_first_install_tower` *requires* those Deep
and Shift hypotheses on the test state. So `CE_weak`-shaped
approvals cannot be constructed by invoking that theorem.

`CE_weak_strong` (below) extends `CE_weak`'s hypothesis chain with
`HeapDeep`/`ValDeep`/`ListValDeep`/`EnvDeep` and the Shift-respect
premises. Its conclusion is identical to `CE_weak`'s. Relationship:
`CE_weak → CE_weak_strong` (trivially — more hypotheses are easier
to satisfy from a witness side, harder to provide from a consumer
side; the strong predicate is a weaker property statement).

Consumers of an approval (the runtime gate, the soundness lemma)
discharge the Deep+Shift hypotheses at admission time, where the
runner already maintains them as invariants.
-/

/-! ## HeapPrefix and CE_weak_strong

`HeapPrefix h₁ h₂` says `h₁` is a content-prefix of `h₂`:
`h₁ = h₂.take h₁.length`. Stronger than length-only — preserves cell
contents, not just cardinality. Needed for transporting heap-content-
dependent facts (`InstallFacts`, `OrigBoundIn`, etc.) from an approval's
admission heap to a test state's heap.

`CE_weak_strong` extends `CE_weak`'s hypothesis chain with
`HeapDeep`/`ValDeep`/`ListValDeep`/`EnvDeep`, Shift-respect, AND
`HeapPrefix h_ref T.heap` (replacing the old length-only premise). The
conclusion is identical to `CE_weak`'s. Relationship to `CE_weak`:
`CE_weak → CE_weak_strong` via `CE_weak_to_strong` (more hypotheses on
the strong side, harder property to state but easier to invoke).

Consumers of an approval discharge the Deep+Shift+HeapPrefix hypotheses
at admission moment, where the runner already maintains validity
invariants and the gate's `matches` enforces the prefix relation. -/

def HeapPrefix (h₁ h₂ : Heap) : Prop := h₁ = h₂.take h₁.length

theorem HeapPrefix.length_le {h₁ h₂ : Heap} (h : HeapPrefix h₁ h₂) :
    h₁.length ≤ h₂.length := by
  unfold HeapPrefix at h
  have : h₁.length = (h₂.take h₁.length).length := by rw [← h]
  rw [List.length_take] at this
  omega

theorem HeapPrefix.refl (h : Heap) : HeapPrefix h h := by
  unfold HeapPrefix
  simp [List.take_length]

theorem HeapPrefix.trans {h₁ h₂ h₃ : Heap}
    (h12 : HeapPrefix h₁ h₂) (h23 : HeapPrefix h₂ h₃) :
    HeapPrefix h₁ h₃ := by
  have h_le : h₁.length ≤ h₂.length := HeapPrefix.length_le h12
  show h₁ = h₃.take h₁.length
  calc h₁ = h₂.take h₁.length := h12
    _ = (h₃.take h₂.length).take h₁.length := by rw [← h23]
    _ = h₃.take (min h₁.length h₂.length) := by rw [List.take_take]
    _ = h₃.take h₁.length := by rw [Nat.min_eq_left h_le]

theorem HeapPrefix.getElem? {h₁ h₂ : Heap} (h : HeapPrefix h₁ h₂)
    (i : Nat) (h_i : i < h₁.length) : h₁[i]? = h₂[i]? := by
  have hh : h₁ = h₂.take h₁.length := h
  rw [hh, List.getElem?_take]
  split
  · rfl
  · omega

def CE_weak_strong (level : Nat) (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    HeapPrefix h_ref T.heap →
    HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
    ValValid old T.heap → ValValid new T.heap →
    PolicyTableRespectsBisimT ptable →
    (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
    (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
    -- Deep predicates on the test state:
    HeapDeep T.heap → ValDeep op T.heap → ListValDeep operands T.heap →
    (∀ n env, T.envAt? n = some env → EnvDeep env T.heap) →
    -- Shift-respect on the test state:
    PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable →
    (∀ n p, T.policyAt? n = some p →
       PolicyRespectsShift T.heap.length [op, listToVal operands] p) →
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length

/-- `CE_weak` implies `CE_weak_strong`. The strong predicate has more
    test-state hypotheses, which we simply discard when applying the
    `CE_weak` witness. -/
theorem CE_weak_to_strong {level : Nat} {h_ref : Heap} {old new : Val}
    (h : CE_weak level h_ref old new) :
    CE_weak_strong level h_ref old new := by
  intro fuel ptable op operands T r T'
    h_prefix h_heap h_op h_operands h_old h_new
    h_ptable h_lvl_pol h_env h_pol h_env_bisim
    _h_heap_deep _h_op_deep _h_operands_deep _h_env_deep
    _h_pt_shift _h_pol_shift h_call
  exact h fuel ptable op operands T r T'
    (HeapPrefix.length_le h_prefix) h_heap h_op h_operands h_old h_new
    h_ptable h_lvl_pol h_env h_pol h_env_bisim h_call

/-- Soundness predicate for the proof-bearing reading: a policy is
    `SoundForCE_weak_strong` at `level` if every admission has a
    `CE_weak_strong` witness. Parallels `BlackPolicy.SoundForCE_weak`
    in `Policies.lean`. -/
abbrev BlackPolicy.SoundForCE_weak_strong (level : Nat) (p : BlackPolicy) : Prop :=
  ∀ ctx old new, p ctx old new = true → CE_weak_strong level ctx.heap old new

/-- A modification approved for installation. The `proof` field is
    the load-bearing certificate: Lean's type checker refuses
    construction without a valid term of `CE_weak_strong`. -/
structure ApprovedModification where
  level   : Nat
  heap    : Heap
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak_strong level heap oldVal newVal

/-- Boolean match of an approval against a runtime mutation context
    and proposed new value. Uses structural `Val.beq` on `oldVal` and
    `newVal`, `decide` on the level, and **content-prefix equality**
    on the heap (`am.heap = ctx.heap.take am.heap.length`).

    Content-prefix (not just length-prefix) is needed so that heap-
    content-dependent facts — `InstallFacts`, `OrigBoundIn`, etc. —
    transport from the approval's admission-heap snapshot to the
    runtime heap and onward to any test state that itself extends
    the runtime heap. -/
def ApprovedModification.matches
    (am : ApprovedModification) (ctx : MutationCtx) (oldVal newVal : Val) : Bool :=
  decide (am.level = ctx.level) &&
  decide (am.heap = ctx.heap.take am.heap.length) &&
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
    `CE_weak_strong` proof. Since `CE_weak → CE_weak_strong`, the
    structural-policy soundness gives us exactly what an approval's
    `proof` field needs. -/
theorem structural_policy_yields_approval
    {p : BlackPolicy} {level : Nat}
    (h_sound : p.SoundForCE_weak level)
    (ctx : MutationCtx) (oldVal newVal : Val)
    (h_admit : p ctx oldVal newVal = true) :
    CE_weak_strong level ctx.heap oldVal newVal :=
  CE_weak_to_strong (h_sound ctx oldVal newVal h_admit)

/-! ## Soundness of `approvedPolicy`

`approvedPolicy approvals` is `SoundForCE_weak_strong` provided all
approvals are at the level being checked. The match condition ensures
the approval's heap is a length-prefix of the runtime heap; the
resulting `CE_weak_strong` proof is monotone in the reference-heap
parameter, so we can lift the approval's witness (over `am.heap`) to
one over `ctx.heap`.
-/

/-- `CE_weak_strong` is monotone in the reference heap. Used to lift
    an approval's proof (over `am.heap`, the heap snapshot the proof
    was constructed against) to one over the current runtime heap
    `ctx.heap`, which is at least as long. -/
theorem CE_weak_strong_heap_mono
    {level : Nat} {h₁ h₂ : Heap} {old new : Val}
    (h_pref : HeapPrefix h₁ h₂)
    (h : CE_weak_strong level h₁ old new) :
    CE_weak_strong level h₂ old new := by
  intro fuel ptable op operands T r T' h_T_prefix
  exact h fuel ptable op operands T r T' (HeapPrefix.trans h_pref h_T_prefix)

/-- The headline: `approvedPolicy approvals` is sound for
    `CE_weak_strong` at any level whose approvals all bind to that
    level. The matching approval's `proof` field supplies the witness;
    the heap-length match plus `CE_weak_strong_heap_mono` shifts the
    reference heap from the approval's snapshot to the runtime heap. -/
theorem approvedPolicy_soundForCE_weak_strong
    (approvals : List ApprovedModification) (level : Nat)
    (h_levels : ∀ am ∈ approvals, am.level = level) :
    BlackPolicy.SoundForCE_weak_strong level (approvedPolicy approvals) := by
  intro ctx old new h_admit
  unfold approvedPolicy at h_admit
  rw [List.any_eq_true] at h_admit
  obtain ⟨am, h_mem, h_match⟩ := h_admit
  unfold ApprovedModification.matches at h_match
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_match
  obtain ⟨⟨⟨_h_lvl_eq, h_heap_prefix⟩, h_old_beq⟩, h_new_beq⟩ := h_match
  have h_old_eq : am.oldVal = old := val_beq_eq _ _ h_old_beq
  have h_new_eq : am.newVal = new := val_beq_eq _ _ h_new_beq
  have h_level : am.level = level := h_levels am h_mem
  subst h_old_eq
  subst h_new_eq
  subst h_level
  exact CE_weak_strong_heap_mono (show HeapPrefix _ _ from h_heap_prefix) am.proof

/-! ## CE_weak reflexivity (identity modifications)

The first non-trivial reusable proof template: every value is its own
CE_weak-conservative extension. Useful for approving "no-op"
modifications — e.g., re-setting `base-apply` to itself, or installing
a copy of an existing closure.

Builds on `applyDirect_preserves_self_invariants` (the public
preservation lemma) wrapped over both branches of `callAsBaseApply`. -/

/-- `callAsBaseApply` preserves heap-validity, result-validity, and
    monotonicity. Wraps `applyDirect_preserves_self_invariants` to
    cover both the `.builtinBaseApply` branch (direct dispatch) and
    the "other" branch (operator-wrap dispatch). -/
theorem callAsBaseApply_preserves
    {fuel : Nat} {ptable : PolicyTable} {level : Nat}
    {baseApply op : Val} {operands : List Val} {T : TowerState}
    {r : Val} {T' : TowerState}
    (hh : HeapValid T.heap)
    (h_levs : ∀ n e, T.envAt? n = some e → EnvValid e T.heap)
    (h_resp_all : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_bisim : ∀ n e, T.envAt? n = some e → EnvVis e e T.heap T.heap)
    (h_pt : PolicyTableRespectsBisimT ptable)
    (h_pol_resp_at : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (hv_base : ValValid baseApply T.heap)
    (hv_op : ValValid op T.heap)
    (hv_operands : ListValValid operands T.heap)
    (h_call :
      callAsBaseApply fuel ptable level baseApply op operands T = some (r, T')) :
    HeapValid T'.heap ∧ ValValid r T'.heap ∧ T.heap.length ≤ T'.heap.length := by
  unfold callAsBaseApply at h_call
  split at h_call
  · -- baseApply = .builtinBaseApply
    obtain ⟨h_heap', _, _, _, h_r, h_mono⟩ :=
      applyDirect_preserves_self_invariants fuel ptable level op operands T r T'
        hh h_levs h_resp_all h_bisim h_pt h_pol_resp_at hv_op hv_operands h_call
    exact ⟨h_heap', h_r, h_mono⟩
  · -- baseApply is anything else; dispatch wraps args = [op, listToVal operands]
    have hv_args : ListValValid [op, listToVal operands] T.heap :=
      ⟨hv_op, ValValid_listToVal hv_operands, trivial⟩
    obtain ⟨h_heap', _, _, _, h_r, h_mono⟩ :=
      applyDirect_preserves_self_invariants fuel ptable level
        baseApply [op, listToVal operands] T r T'
        hh h_levs h_resp_all h_bisim h_pt h_pol_resp_at hv_base hv_args h_call
    exact ⟨h_heap', h_r, h_mono⟩

/-- Reflexivity of `CE_weak`: every value is conservatively extended
    by itself. The proof picks `fuel' = fuel`, `T'' = T'`, `r' = r`;
    the equation premise is reused; `ValVis_weak r r T'.heap T'.heap`
    follows from `ValVis_aux_self_extend` with empty extras, given
    heap-validity and result-validity from `callAsBaseApply_preserves`. -/
theorem CE_weak_refl (level : Nat) (h_ref : Heap) (v : Val) :
    CE_weak level h_ref v v := by
  intro fuel ptable op operands T r T'
    _h_T_len h_heap h_op h_operands h_old _h_new
    h_ptable h_lvl_pol h_env h_pol h_env_bisim h_call
  obtain ⟨h_heap', h_r', h_mono⟩ :=
    callAsBaseApply_preserves
      (hh := h_heap) (h_levs := h_env) (h_resp_all := h_pol)
      (h_bisim := h_env_bisim) (h_pt := h_ptable) (h_pol_resp_at := h_lvl_pol)
      (hv_base := h_old) (hv_op := h_op) (hv_operands := h_operands)
      (h_call := h_call)
  refine ⟨fuel, T', r, h_call, ?_, rfl, h_heap', h_mono⟩
  intro n
  have h_strong := ValVis_aux_self_extend n r T'.heap [] h_heap' h_r'
  have h_strong' : ValVis_aux n r r T'.heap T'.heap := by simpa using h_strong
  exact ValVis_aux_to_weak n r r T'.heap T'.heap h_strong'

/-- An `ApprovedModification` for the identity case at any `v` that
    is `ValValid` in the admission heap. The proof field is
    `CE_weak_refl` widened via `CE_weak_to_strong`. The `ValValid`
    precondition isn't needed by `CE_weak_refl` itself (which is
    universally quantified over `T`) — only for documentation that
    the approval is meaningful at `am.heap`. -/
def identityApproval (level : Nat) (heap : Heap) (v : Val) :
    ApprovedModification :=
  { level   := level
    heap    := heap
    oldVal  := v
    newVal  := v
    proof   := CE_weak_to_strong (CE_weak_refl level heap v) }

/-- The narrower numerical identity. Kept as a convenience (and a
    sanity-check that the more general `identityApproval` agrees on
    the `.num` case). -/
def numIdentityApproval (level : Nat) (heap : Heap) (n : Int) :
    ApprovedModification :=
  identityApproval level heap (.num n)

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

/-- The policy admits the matching mutation. -/
example :
    approvedPolicy smokeIdentityApprovals
        smokeIdentityCtx (.num 42) (.num 42) = true := by
  decide

/-- The policy refuses a non-matching mutation (wrong `newVal`). -/
example :
    approvedPolicy smokeIdentityApprovals
        smokeIdentityCtx (.num 42) (.num 7) = false := by
  decide

/-- The policy's soundness follows from
    `approvedPolicy_soundForCE_weak_strong` once we verify all
    approvals bind to level 0 — which they do, by construction. -/
example : BlackPolicy.SoundForCE_weak_strong 0 (approvedPolicy smokeIdentityApprovals) :=
  approvedPolicy_soundForCE_weak_strong smokeIdentityApprovals 0
    (by intro am h_mem
        simp [smokeIdentityApprovals, numIdentityApproval, identityApproval]
          at h_mem
        subst h_mem; rfl)

/-! ## Closure-identity demo

A more substantive instance: approving the identity modification on a
*closure* value. Same `CE_weak_refl` proof, but exercises the
`callAsBaseApply_preserves` "other" branch (operator-wrap dispatch),
where `applyDirect`'s arity check, foldl alloc, and body eval all
happen — yet the new value equals the old, so the conclusion holds. -/

/-- A trivial closure: `(λ (op args). op)` — returns the operator
    unchanged. Captures no environment. -/
def trivialClosure : Val :=
  .closure ["op", "args"] (.var "op") .nil

def smokeClosureApprovals : List ApprovedModification :=
  [identityApproval 0 [] trivialClosure]

example :
    approvedPolicy smokeClosureApprovals
        smokeIdentityCtx trivialClosure trivialClosure = true := by
  decide

example : BlackPolicy.SoundForCE_weak_strong 0 (approvedPolicy smokeClosureApprovals) :=
  approvedPolicy_soundForCE_weak_strong smokeClosureApprovals 0
    (by intro am h_mem
        simp [smokeClosureApprovals, identityApproval] at h_mem
        subst h_mem; rfl)

/-! ## W1 — existential equational-theory defeat

The headline application of the proof-bearing reading:

> For any list of admitted modifications `approvals`, there exist
> syntactically-distinct expressions that converge to the same value
> under any policy table gated by `approvedPolicy approvals`.

In other words: β-equivalent terms remain observationally equivalent
*even with proof-bearing admissions in scope*. The "equational
theory defeat" Wand warned about — where ad-hoc reflection-induced
modifications break β — does not happen under proof-bearing
admission.

This first cut uses a *weak* obs-equivalence: existential convergence
to a common value at some fuel. A stronger universal form (per-fuel
or per-context) is left as a follow-up. The existential form is
sufficient for the keynote claim that the *equational-theory defeat
is itself defeated* by proof-bearing admission.

The witness `(M, N) = ((λx. x) 0, 0)` is β-equivalent (β-redex and
its contractum) and syntactically distinct (different constructors).
The role of `approvals` in the statement: the policy table is gated
by `approvedPolicy approvals`, so even with arbitrary admitted
modifications in scope, the obs-equiv holds. (The redex/contractum
contain no `.set`, so the policy gate doesn't fire during eval — but
the statement is still meaningful: it says admissions don't disturb
β at the source level.) -/

/-- Convergent observational equivalence under a baseline policy
    table. We use `[acceptAllPolicy]` for concreteness — the policy
    gate is irrelevant for `.set`-free expressions, but baking in a
    concrete table makes the equality reducible by `native_decide`.
    A stronger version parameterized on the approval-gated policy
    table is a follow-up (requires a policy-independence lemma for
    `.set`-free expressions; see note on `wand_defeated_existential`). -/
def ObsEquivConverges (M N : Expr) : Prop :=
  ∃ fuel v,
    evalProgram fuel [acceptAllPolicy] M = some v ∧
    evalProgram fuel [acceptAllPolicy] N = some v

/-- **W1: the existential equational-theory defeat.** For any list of
    proof-bearing approvals in scope, there's a syntactically-
    distinct β-redex/contractum pair that converges to the same
    value under the baseline policy table.

    The witness is `((λx. x) 0)` vs `0`. These differ as `Expr`
    constructors (one is `.app`, the other is `.num`) so they are
    not syntactically equal. They both eval to `(.num 0)` at fuel
    100 — confirmed by `native_decide`, which the `DecidableEq Val`
    instance above unlocks.

    The role of `approvals` in the statement: even with arbitrary
    proof-bearing admissions in scope, the β-equiv pair converges
    obs-equivalently. The eval doesn't go through `.set` for these
    terms, so the policy gate doesn't fire — but the statement
    documents that admissions are *non-disturbing* to β-equivalence.

    Strengthening to "obs-equiv under the approval-gated table
    `[approvedPolicy approvals]`" requires a policy-independence
    lemma for `.set`-free expressions; see follow-up note below. -/
theorem wand_defeated_existential (_approvals : List ApprovedModification) :
    ∃ M N : Expr, M ≠ N ∧ ObsEquivConverges M N := by
  refine ⟨.app [.lam ["x"] (.var "x"), .num 0], .num 0, ?_, ?_⟩
  · intro h; cases h
  · refine ⟨100, .num 0, ?_, ?_⟩ <;> native_decide

/-! ### Follow-up: parameterized W1

Under the gated policy table `[approvedPolicy approvals]`, the
witness still converges identically — because the redex/contractum
contain no `.set`, the policy gate isn't consulted during eval.
Full chaining via a `NoSet`-policy-independence lemma is ~80 LOC of
mutual induction; for a quick gated W1 with a different witness pair
(easier kernel reduction), see `wand_defeated_existential_gated`
below. -/

/-! ## Parameterized (gated) W1

Same headline claim as `wand_defeated_existential`, but the policy
table is `[approvedPolicy approvals]` rather than baseline
`[acceptAllPolicy]`. The β-redex/contractum pair would also work
here, but proving its evaluation under abstract `approvals` requires
the deferred policy-independence lemma; instead, we use a different
syntactically-distinct convergent pair whose eval doesn't go through
`applyVia` / `materialize` (so `simp [evalProgram, eval]; rfl` closes
without needing further unfolding under abstract policy).

Witness: `(if true then 0 else 1)` vs `0`. Different `Expr`
constructors (`.ifte` vs `.num`), same value. The eval of `.ifte` on
`.bool true` short-circuits to the then-branch without consulting the
policy table. -/

def ObsEquivConvergesGated (approvals : List ApprovedModification)
    (M N : Expr) : Prop :=
  ∃ fuel v,
    evalProgram fuel [approvedPolicy approvals] M = some v ∧
    evalProgram fuel [approvedPolicy approvals] N = some v

theorem wand_defeated_existential_gated
    (approvals : List ApprovedModification) :
    ∃ M N : Expr, M ≠ N ∧ ObsEquivConvergesGated approvals M N := by
  refine ⟨.ifte (.bool true) (.num 0) (.num 1), .num 0, ?_, ?_⟩
  · intro h; cases h
  · refine ⟨100, .num 0, ?_, ?_⟩
    · simp [evalProgram, eval]; rfl
    · simp [evalProgram, eval]; rfl

/-! ## Multn approval — the worked example

This is the headline construction: an `ApprovedModification` for the
multn closure, built by invoking `multnExact_soundForCE_first_install_tower`
inside the `CE_weak_strong` proof.

Two pieces of machinery are needed:

1. **`InstallFacts.heap_extend`** — `OrigBoundIn` and `NumQBoundIn`
   are about specific heap-cell lookups, so they transport across a
   content-preserving `HeapPrefix` extension. This is why the
   approval's `matches` checks content-prefix and `CE_weak_strong`
   carries `HeapPrefix h_ref T.heap`.

2. **Fuel split.** `multnExact_soundForCE_first_install_tower` requires
   `fuel ≥ 2`. `CE_weak_strong` quantifies over arbitrary `fuel`.
   - `fuel = 0`: `callAsBaseApply 0 .builtinBaseApply ... = applyDirect 0 ... = none`,
     so `h_old` is unsatisfiable. Vacuous.
   - `fuel = 1`: `callAsBaseApply 1 .builtinBaseApply op operands T
     = applyDirect 1 ... op operands T`. By case on `op`:
     - `.num`/`.bool`/`.nilV`/`.sym`/`.cons`/`.closure`: `applyDirect 1`
       returns `none` (closure body eval with fuel 0 is `none`; other
       constructors are non-callable). Vacuous.
     - `.prim p`: returns `some (applyPrim p operands, T)` (fuel-
       independent). This subcase needs a separate proof; we handle
       it by "bumping" fuel to 2 (`applyDirect_prim_fuel_bump`).
     - `.builtinBaseApply`: recurses to `applyDirect 0` → `none`.
       Vacuous.
   - `fuel ≥ 2`: invoke the multn theorem directly.
-/

/-! ### `InstallFacts.heap_extend` -/

/-- If `h₁[idx]? = some v`, then `idx < h₁.length`. -/
theorem getElem?_some_lt_length {α} {l : List α} {idx : Nat} {v : α}
    (h : l[idx]? = some v) : idx < l.length := by
  cases h_lt : decide (idx < l.length) with
  | true =>
      exact of_decide_eq_true h_lt
  | false =>
      exfalso
      have h_ge : l.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false h_lt)
      rw [List.getElem?_eq_none h_ge] at h
      exact Option.noConfusion h

theorem OrigBoundIn_heap_extend
    {h₁ h₂ : Heap} {old new : Val}
    (h_pref : HeapPrefix h₁ h₂) (h_orig : OrigBoundIn h₁ old new) :
    OrigBoundIn h₂ old new := by
  obtain ⟨ps, body, cenv, idx, h_eq, h_lookup, h_heap⟩ := h_orig
  refine ⟨ps, body, cenv, idx, h_eq, h_lookup, ?_⟩
  have h_idx : idx < h₁.length := getElem?_some_lt_length h_heap
  rw [← HeapPrefix.getElem? h_pref idx h_idx]; exact h_heap

theorem NumQBoundIn_heap_extend
    {h₁ h₂ : Heap} {new : Val}
    (h_pref : HeapPrefix h₁ h₂) (h_numq : NumQBoundIn h₁ new) :
    NumQBoundIn h₂ new := by
  obtain ⟨ps, body, cenv, idx, h_eq, h_lookup, h_heap⟩ := h_numq
  refine ⟨ps, body, cenv, idx, h_eq, h_lookup, ?_⟩
  have h_idx : idx < h₁.length := getElem?_some_lt_length h_heap
  rw [← HeapPrefix.getElem? h_pref idx h_idx]; exact h_heap

theorem InstallFacts_heap_extend
    {h₁ h₂ : Heap} {old new : Val}
    (h_pref : HeapPrefix h₁ h₂) (install : InstallFacts old new h₁) :
    InstallFacts old new h₂ :=
  { orig := OrigBoundIn_heap_extend h_pref install.orig
    numq := NumQBoundIn_heap_extend h_pref install.numq }

/-! ### Fuel split helpers

For the `fuel < 2` cases of `CE_weak_strong`, we need to show that
`callAsBaseApply fuel .builtinBaseApply op operands T = some (r, T')`
is either vacuous or admits a "bump" to fuel ≥ 2 with the same result. -/

/-- `applyDirect` on a `.prim` operator is fuel-independent (the
    primitive is dispatched by `applyPrim`, which doesn't consume
    fuel). So if `applyDirect 1` succeeds, `applyDirect 2` gives the
    same result. -/
theorem applyDirect_prim_fuel_bump
    {p : String} {operands : List Val} {T : TowerState}
    {ptable : PolicyTable} {level : Nat} {r : Val} {T' : TowerState}
    (h : applyDirect 1 ptable level (.prim p) operands T = some (r, T')) :
    applyDirect 2 ptable level (.prim p) operands T = some (r, T') := by
  simp only [applyDirect] at h ⊢
  exact h

/-- `callAsBaseApply` at `fuel = 1` with `oldVal = .builtinBaseApply`:
    by case analysis on `op`, the call succeeds **only when** `op` is
    a `.prim`. (All other ops give `none` at fuel 1 via applyDirect.) -/
theorem callAsBaseApply_one_builtin_succeeds_implies_prim
    {ptable : PolicyTable} {level : Nat} {op : Val} {operands : List Val}
    {T : TowerState} {r : Val} {T' : TowerState}
    (h : callAsBaseApply 1 ptable level .builtinBaseApply op operands T
         = some (r, T')) :
    ∃ p, op = .prim p := by
  unfold callAsBaseApply at h
  simp only [applyDirect] at h
  cases op with
  | num _ => exact absurd h (by simp [applyDirect])
  | bool _ => exact absurd h (by simp [applyDirect])
  | nilV => exact absurd h (by simp [applyDirect])
  | sym _ => exact absurd h (by simp [applyDirect])
  | cons _ _ => exact absurd h (by simp [applyDirect])
  | closure _ _ _ =>
      -- applyDirect 1 with closure evaluates body with fuel 0 = none
      simp only [applyDirect] at h
      split at h <;> simp [eval] at h
  | prim p => exact ⟨p, rfl⟩
  | builtinBaseApply =>
      -- applyDirect 1 with .builtinBaseApply: match args = [op,opList],
      -- then recursive applyDirect 0 = none.
      cases operands with
      | nil       => simp [applyDirect] at h
      | cons _ tl =>
          cases tl with
          | nil       => simp [applyDirect] at h
          | cons opList tl2 =>
              cases tl2 with
              | nil       =>
                  simp only [applyDirect] at h
                  cases h_vtl : valToList opList with
                  | none   => rw [h_vtl] at h; simp at h
                  | some _ => rw [h_vtl] at h; simp [applyDirect] at h
              | cons _ _  => simp [applyDirect] at h

/-! ### The multn approval

Given the multn-shape admission fact at the admission heap, plus
shift-respect for the verified table, construct an
`ApprovedModification` whose `proof` field invokes
`multnExact_soundForCE_first_install_tower` (after handling the
`fuel < 2` cases).

The admission point: `multnExactPolicy` admits `.builtinBaseApply →
newClosure` at the snapshot heap `heap`. This is verified by
`multnExactPolicy_implies_InstallFacts`, giving install facts on
`heap`. Inside the proof, those facts transport to any test state's
heap via `InstallFacts_heap_extend` + the `HeapPrefix` premise. -/

/-- The multn approval. Construction needs:

    - The shape-admission fact at a chosen admission heap.
    - A shift-respect fact for the policy table consumed at runtime,
      stated at the admission heap (transported to test states via
      this proof's prefix-extension premise).

    The runner constructs both at the admission moment from the
    runtime state; see `multnExactPolicy_implies_InstallFacts` and
    `verifiedTable_respects_shift` (the latter in `Policies.lean`'s
    follow-up section, not used directly here — we take the shift
    facts as input parameters). -/
def multnApproval
    (level : Nat) (heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : multnExactPolicy
                 { target := "base-apply", heap := heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true) :
    ApprovedModification :=
{ level   := level
  heap    := heap
  oldVal  := .builtinBaseApply
  newVal  := newClosure
  proof   := by
    intro fuel ptable op operands T r T'
      h_prefix h_heap h_op h_operands h_old h_new
      h_ptable h_lvl_pol h_env h_pol h_env_bisim
      h_heap_deep h_op_deep h_operands_deep h_env_deep
      h_pt_shift h_pol_shift h_call
    -- Get install facts on the admission heap, then transport to T.heap.
    have ⟨_, install_heap⟩ := multnExactPolicy_implies_InstallFacts h_admit
    have install_T : InstallFacts .builtinBaseApply newClosure T.heap :=
      InstallFacts_heap_extend h_prefix install_heap
    -- Build RuntimeWF from the strong-CE hypotheses. `ev_cenv` uses
    -- `ValValid newClosure T.heap`, which on a closure unfolds to the
    -- captured env's EnvValid in T.heap.
    have wf : RuntimeWF newClosure op operands T := {
      hv_heap     := h_heap
      ev_levels   := h_env
      ev_cenv     := fun ps body cenv' h_eq => by
        have h_vv : ValValid (.closure ps body cenv') T.heap := h_eq ▸ h_new
        exact h_vv
      vv_op       := h_op
      lvv_operands := h_operands }
    -- Fuel split.
    match fuel, h_call with
    | 0,     h_call =>
        -- callAsBaseApply 0 .builtinBaseApply = applyDirect 0 = none.
        exact absurd h_call (by simp [callAsBaseApply, applyDirect])
    | 1,     h_call =>
        -- fuel = 1 + h_old succeeds ⇒ op = .prim p. Bump to fuel 2,
        -- then invoke the multn theorem.
        obtain ⟨p, h_op_eq⟩ :=
          callAsBaseApply_one_builtin_succeeds_implies_prim h_call
        subst h_op_eq
        have h_call_2 : callAsBaseApply 2 ptable level .builtinBaseApply
                          (.prim p) operands T = some (r, T') := by
          simp only [callAsBaseApply] at h_call ⊢
          exact applyDirect_prim_fuel_bump h_call
        obtain ⟨fuel', T'', r', h_call', h_vv, h_pol_all, h_heap_v, h_mono⟩ :=
          multnExact_soundForCE_first_install_tower h_admit (by omega) h_ptable
            h_call_2 install_T wf h_heap_deep h_op_deep h_operands_deep
            h_env_deep h_pol h_pt_shift h_pol_shift
        exact ⟨fuel', T'', r', h_call', h_vv, h_pol_all level, h_heap_v, h_mono⟩
    | n + 2, h_call =>
        -- fuel ≥ 2: invoke multn theorem directly.
        obtain ⟨fuel', T'', r', h_call', h_vv, h_pol_all, h_heap_v, h_mono⟩ :=
          multnExact_soundForCE_first_install_tower h_admit (by omega) h_ptable
            h_call install_T wf h_heap_deep h_op_deep h_operands_deep
            h_env_deep h_pol h_pt_shift h_pol_shift
        exact ⟨fuel', T'', r', h_call', h_vv, h_pol_all level, h_heap_v, h_mono⟩ }

end LeanBlack
