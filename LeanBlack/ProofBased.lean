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
instances in scope, `decide +kernel` can discharge closed
`Option Val` / `Option (Val × _)` equalities by kernel evaluation
(no trusted-compiler axiom) — the load-bearing machinery for W1
below. -/

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
    concrete table makes the equality kernel-reducible (`decide +kernel`).
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
    100 — confirmed by `decide +kernel` (kernel evaluation; no
    trusted-compiler axiom), which the `DecidableEq Val` instance
    above unlocks.

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
  · -- `decide +kernel`: the kernel evaluates the witness directly,
    -- avoiding `native_decide`'s trusted-compiler axiom (and the
    -- elaborator-level `primPairs` irreducibility block).
    refine ⟨100, .num 0, ?_, ?_⟩ <;> decide +kernel

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

/-! ## `Pure` policy-independence

An `Expr` is `Pure` if it contains no `.set` and no `.installPolicy`
(neither at its top level nor nested in any subexpression, closure
body, or `.quote v`-quoted value). The mutually-defined `PureVal`
predicate on `Val` requires any embedded closure body to be `Pure`.

The headline claim, proved below: for `Pure` `Expr`s with a `Pure`-
heap context, `eval` (and the mutually-recursive
`evalList`/`applyVia`/`applyDirect`) is policy-independent — the
final result depends only on the inputs, never on the `PolicyTable`
argument.

Why we want it: lets us upgrade `wand_defeated_existential` to use
the gated policy table `[approvedPolicy approvals]` while keeping
the β-redex witness `((λx. x) 0)`. -/

mutual
  def Pure : Expr → Bool
    | .num _           => true
    | .bool _          => true
    | .quote v         => PureVal v
    | .var _           => true
    | .ifte c t e      => Pure c && Pure t && Pure e
    | .lam _ b         => Pure b
    | .app es          => PureList es
    | .set _ _         => false
    | .em b            => Pure b
    | .primApp f as    => Pure f && PureList as
    | .letE _ e b      => Pure e && Pure b
    | .seq es          => PureList es
    | .installPolicy _ => false

  def PureList : List Expr → Bool
    | []      => true
    | x :: xs => Pure x && PureList xs

  def PureVal : Val → Bool
    | .closure _ body _ => Pure body
    | .cons x y         => PureVal x && PureVal y
    | _                 => true
end

def PureValList : List Val → Bool
  | []      => true
  | x :: xs => PureVal x && PureValList xs

/-- A heap is `Pure` if every cell holds a `PureVal`. -/
def PureHeap (h : Heap) : Prop :=
  ∀ (i : Nat) (v : Val), h[i]? = some v → PureVal v = true

/-! ### Proof structure

The joint claim with preservation. The four mutual functions
preserve `PureVal`/`PureHeap` and are policy-independent. -/

def AllPureIndep (fuel : Nat) : Prop :=
  (∀ (level : Nat) (M : Expr) (env : Env) (T : TowerState),
       Pure M = true → PureHeap T.heap →
       (∀ (p₁ p₂ : PolicyTable),
         eval fuel p₁ level M env T = eval fuel p₂ level M env T) ∧
       (∀ (p : PolicyTable) (v : Val) (T' : TowerState),
         eval fuel p level M env T = some (v, T') →
         PureVal v = true ∧ PureHeap T'.heap)) ∧
  (∀ (level : Nat) (Ms : List Expr) (env : Env) (T : TowerState),
       PureList Ms = true → PureHeap T.heap →
       (∀ (p₁ p₂ : PolicyTable),
         evalList fuel p₁ level Ms env T = evalList fuel p₂ level Ms env T) ∧
       (∀ (p : PolicyTable) (vs : List Val) (T' : TowerState),
         evalList fuel p level Ms env T = some (vs, T') →
         PureValList vs = true ∧ PureHeap T'.heap)) ∧
  (∀ (level : Nat) (op : Val) (args : List Val) (T : TowerState),
       PureVal op = true → PureValList args = true → PureHeap T.heap →
       (∀ (p₁ p₂ : PolicyTable),
         applyVia fuel p₁ level op args T = applyVia fuel p₂ level op args T) ∧
       (∀ (p : PolicyTable) (v : Val) (T' : TowerState),
         applyVia fuel p level op args T = some (v, T') →
         PureVal v = true ∧ PureHeap T'.heap)) ∧
  (∀ (level : Nat) (op : Val) (args : List Val) (T : TowerState),
       PureVal op = true → PureValList args = true → PureHeap T.heap →
       (∀ (p₁ p₂ : PolicyTable),
         applyDirect fuel p₁ level op args T = applyDirect fuel p₂ level op args T) ∧
       (∀ (p : PolicyTable) (v : Val) (T' : TowerState),
         applyDirect fuel p level op args T = some (v, T') →
         PureVal v = true ∧ PureHeap T'.heap))

/-! ### The proof

Joint induction on `fuel` with extensive case analysis on the
`Expr`/`Val` constructor at each function. The auxiliary lemmas
(below) handle preservation of `PureHeap` across `materialize` and
`alloc`, and preservation of `PureVal` through `applyPrim`,
`listToVal`, `valToList`. -/

theorem allPureIndep_zero : AllPureIndep 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro level M env T _h_M _h_T
    refine ⟨?_, ?_⟩
    · intro _ _; simp [eval]
    · intro _ _ _ h; simp [eval] at h
  · intro level Ms env T _h_Ms _h_T
    refine ⟨?_, ?_⟩
    · intro _ _; simp [evalList]
    · intro _ _ _ h; simp [evalList] at h
  · intro level op args T _h_op _h_args _h_T
    refine ⟨?_, ?_⟩
    · intro _ _; simp [applyVia]
    · intro _ _ _ h; simp [applyVia] at h
  · intro level op args T _h_op _h_args _h_T
    refine ⟨?_, ?_⟩
    · intro _ _; simp [applyDirect]
    · intro _ _ _ h; simp [applyDirect] at h

/-! Inductive step — auxiliary preservation lemmas + the main 4-way
mutual induction. All cases proved. -/

-- The auxiliary lemma: PureHeap heap → heap[i]? = some v → PureVal v
theorem PureHeap_getElem? {h : Heap} (h_pure : PureHeap h)
    {i : Nat} {v : Val} (h_some : h[i]? = some v) : PureVal v = true :=
  h_pure i v h_some

/-- Appending PureVal cells to a `PureHeap` preserves `PureHeap`. -/
theorem PureHeap_append (h extras : Heap)
    (h_h : PureHeap h) (h_ext : ∀ v ∈ extras, PureVal v = true) :
    PureHeap (h ++ extras) := by
  intro i v h_some
  by_cases h_lt : i < h.length
  · rw [List.getElem?_append_left h_lt] at h_some
    exact h_h i v h_some
  · have h_ge : h.length ≤ i := Nat.le_of_not_lt h_lt
    rw [List.getElem?_append_right h_ge] at h_some
    exact h_ext v (List.mem_of_getElem? h_some)

theorem primPairs_values_PureVal :
    ∀ v ∈ primPairs.map (·.2), PureVal v = true := by
  intro v hv
  unfold primPairs at hv
  simp [List.map] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  all_goals rfl

theorem freshLevelEnv_preserves_PureHeap (h : Heap) (h_pure : PureHeap h) :
    PureHeap (freshLevelEnv h).1 := by
  rw [freshLevelEnv_heap_eq]
  apply PureHeap_append
  · exact PureHeap_append h _ h_pure primPairs_values_PureVal
  · intro v hv
    simp at hv
    subst hv; rfl

theorem materializeStep_preserves_PureHeap {T : TowerState}
    (h_T : PureHeap T.heap) : PureHeap (materializeStep T).heap := by
  unfold materializeStep
  exact freshLevelEnv_preserves_PureHeap T.heap h_T

theorem materialize_fold_preserves_PureHeap (T : TowerState) (k : Nat)
    (h_T : PureHeap T.heap) :
    PureHeap (Nat.fold k (fun _ _ T' => materializeStep T') T).heap := by
  induction k with
  | zero => simpa using h_T
  | succ m IH =>
      rw [Nat.fold_succ]
      exact materializeStep_preserves_PureHeap IH

theorem materialize_preserves_PureHeap {T T' : TowerState} {n : Nat}
    (h_mat : T.materialize n = some T') (h_T : PureHeap T.heap) :
    PureHeap T'.heap := by
  unfold TowerState.materialize at h_mat
  split at h_mat
  · cases h_mat
  · split at h_mat
    · injection h_mat with h_eq
      subst h_eq; exact h_T
    · injection h_mat with h_eq
      subst h_eq
      exact materialize_fold_preserves_PureHeap T _ h_T

theorem Heap_alloc_preserves_PureHeap (h : Heap) (v : Val)
    (h_h : PureHeap h) (h_v : PureVal v = true) :
    PureHeap (h.alloc v).1 := by
  unfold Heap.alloc
  apply PureHeap_append _ _ h_h
  intro v' hv'
  simp at hv'; subst hv'; exact h_v

theorem TowerState_alloc_preserves_PureHeap {T : TowerState} {v : Val}
    (h_T : PureHeap T.heap) (h_v : PureVal v = true) :
    PureHeap (T.alloc v).1.heap := by
  unfold TowerState.alloc
  exact Heap_alloc_preserves_PureHeap T.heap v h_T h_v

/-- `foldl allocStep` preserves `PureHeap` if every value being
    allocated is `PureVal`. -/
theorem foldl_allocStep_preserves_PureHeap (pairs : List (Val × String))
    (h : Heap) (env : Env) (h_pure : PureHeap h)
    (h_pairs : ∀ p ∈ pairs, PureVal p.1 = true) :
    PureHeap (pairs.foldl allocStep (h, env)).1 := by
  induction pairs generalizing h env with
  | nil => exact h_pure
  | cons p ps IH =>
      simp only [List.foldl]
      apply IH
      · -- PureHeap of intermediate (allocStep applied once)
        show PureHeap (allocStep (h, env) p).1
        unfold allocStep
        exact Heap_alloc_preserves_PureHeap h p.1 h_pure (h_pairs p (by simp))
      · intro p' hp'
        exact h_pairs p' (by simp [hp'])

/-- `listToVal` on a `PureValList` produces a `PureVal`. -/
theorem PureVal_listToVal : ∀ {args : List Val},
    PureValList args = true → PureVal (listToVal args) = true
  | [], _ => rfl
  | _ :: _, h => by
      simp only [PureValList, Bool.and_eq_true] at h
      simp only [listToVal, PureVal, Bool.and_eq_true]
      exact ⟨h.1, PureVal_listToVal h.2⟩

/-- `valToList` on a `PureVal` cons-list produces a `PureValList`. -/
theorem valToList_PureValList : ∀ {v : Val} {operands : List Val},
    PureVal v = true → valToList v = some operands → PureValList operands = true
  | .nilV, _, _, h => by simp [valToList] at h; subst h; rfl
  | .cons x xs, _, h_pure, h => by
      simp [valToList] at h
      cases h_rec : valToList xs with
      | none => simp [h_rec] at h
      | some xs_l =>
          simp [h_rec] at h
          subst h
          simp only [PureVal, Bool.and_eq_true] at h_pure
          have h_xs_pure := valToList_PureValList h_pure.2 h_rec
          simp [PureValList]
          exact ⟨h_pure.1, h_xs_pure⟩

/-- Values in a zip with a `PureValList` first component are `PureVal`. -/
theorem PureValList_zip_left {args : List Val} {ps : List String}
    (h_args : PureValList args = true) :
    ∀ p ∈ args.zip ps, PureVal p.1 = true := by
  intro p hp
  induction args generalizing ps with
  | nil => simp [List.zip, List.zipWith] at hp
  | cons a as IH =>
      cases ps with
      | nil => simp [List.zip, List.zipWith] at hp
      | cons s ss =>
          simp [List.zip, List.zipWith] at hp
          simp only [PureValList, Bool.and_eq_true] at h_args
          rcases hp with ⟨rfl, rfl⟩ | h_rest
          · exact h_args.1
          · exact IH h_args.2 h_rest

/-- `applyPrim` preserves `PureVal`: if args are `PureValList`, the
    result is `PureVal`. -/
theorem applyPrim_PureVal {name : String} {args : List Val} {v : Val}
    (h_args : PureValList args = true) (h : applyPrim name args = some v) :
    PureVal v = true := by
  unfold applyPrim at h
  -- 13 name branches. Each unfolds to a specific applyPrim_* call.
  -- For each, the result is either a constructor-fixed Val (trivially
  -- PureVal in most cases) or a sub-Val from args (PureVal by precond).
  by_cases h₁ : name = "+"
  · rw [if_pos h₁] at h
    unfold applyPrim_plus at h
    match args, h with
    | [.num _, .num _], h => obtain rfl := Option.some.inj h; rfl
  · rw [if_neg h₁] at h
    by_cases h₂ : name = "-"
    · rw [if_pos h₂] at h
      unfold applyPrim_minus at h
      match args, h with
      | [.num _, .num _], h => obtain rfl := Option.some.inj h; rfl
    · rw [if_neg h₂] at h
      by_cases h₃ : name = "*"
      · rw [if_pos h₃] at h
        unfold applyPrim_times at h
        match args, h with
        | [.num _, .num _], h => obtain rfl := Option.some.inj h; rfl
      · rw [if_neg h₃] at h
        by_cases h₄ : name = "mul-list"
        · rw [if_pos h₄] at h
          unfold applyPrim_mulList at h
          match args, h with
          | [w], h =>
              simp at h
              obtain ⟨k, _, rfl⟩ := h
              rfl
        · rw [if_neg h₄] at h
          by_cases h₅ : name = "="
          · rw [if_pos h₅] at h
            unfold applyPrim_eq at h
            match args, h with
            | [.num _, .num _], h => obtain rfl := Option.some.inj h; rfl
          · rw [if_neg h₅] at h
            by_cases h₆ : name = "num?"
            · rw [if_pos h₆] at h
              unfold applyPrim_numQ at h
              match args, h with
              | [.num _], h | [.bool _], h | [.nilV], h | [.cons _ _], h
              | [.sym _], h | [.closure _ _ _], h | [.prim _], h
              | [.builtinBaseApply], h =>
                obtain rfl := Option.some.inj h; rfl
            · rw [if_neg h₆] at h
              by_cases h₇ : name = "bool?"
              · rw [if_pos h₇] at h
                unfold applyPrim_boolQ at h
                match args, h with
                | [.num _], h | [.bool _], h | [.nilV], h | [.cons _ _], h
                | [.sym _], h | [.closure _ _ _], h | [.prim _], h
                | [.builtinBaseApply], h =>
                  obtain rfl := Option.some.inj h; rfl
              · rw [if_neg h₇] at h
                by_cases h₈ : name = "closure?"
                · rw [if_pos h₈] at h
                  unfold applyPrim_closureQ at h
                  match args, h with
                  | [.num _], h | [.bool _], h | [.nilV], h | [.cons _ _], h
                  | [.sym _], h | [.closure _ _ _], h | [.prim _], h
                  | [.builtinBaseApply], h =>
                    obtain rfl := Option.some.inj h; rfl
                · rw [if_neg h₈] at h
                  by_cases h₉ : name = "prim?"
                  · rw [if_pos h₉] at h
                    unfold applyPrim_primQ at h
                    match args, h with
                    | [.num _], h | [.bool _], h | [.nilV], h | [.cons _ _], h
                    | [.sym _], h | [.closure _ _ _], h | [.prim _], h
                    | [.builtinBaseApply], h =>
                      obtain rfl := Option.some.inj h; rfl
                  · rw [if_neg h₉] at h
                    by_cases h₁₀ : name = "cons"
                    · rw [if_pos h₁₀] at h
                      unfold applyPrim_cons at h
                      match args, h with
                      | [a, b], h =>
                          obtain rfl := Option.some.inj h
                          simp only [PureValList, Bool.and_eq_true] at h_args
                          simp [PureVal]
                          exact ⟨h_args.1, h_args.2.1⟩
                    · rw [if_neg h₁₀] at h
                      by_cases h₁₁ : name = "car"
                      · rw [if_pos h₁₁] at h
                        unfold applyPrim_car at h
                        match args, h with
                        | [.cons a b], h =>
                            obtain rfl := Option.some.inj h
                            simp only [PureValList, Bool.and_eq_true,
                                       PureVal] at h_args
                            exact h_args.1.1
                      · rw [if_neg h₁₁] at h
                        by_cases h₁₂ : name = "cdr"
                        · rw [if_pos h₁₂] at h
                          unfold applyPrim_cdr at h
                          match args, h with
                          | [.cons a b], h =>
                              obtain rfl := Option.some.inj h
                              simp only [PureValList, Bool.and_eq_true,
                                         PureVal] at h_args
                              exact h_args.1.2
                        · rw [if_neg h₁₂] at h
                          by_cases h₁₃ : name = "null?"
                          · rw [if_pos h₁₃] at h
                            unfold applyPrim_nullQ at h
                            match args, h with
                            | [.num _], h | [.bool _], h | [.nilV], h
                            | [.cons _ _], h | [.sym _], h
                            | [.closure _ _ _], h | [.prim _], h
                            | [.builtinBaseApply], h =>
                              obtain rfl := Option.some.inj h; rfl
                          · rw [if_neg h₁₃] at h
                            by_cases h₁₄ : name = "sym?"
                            · rw [if_pos h₁₄] at h
                              unfold applyPrim_symQ at h
                              match args, h with
                              | [.num _], h | [.bool _], h | [.nilV], h
                              | [.cons _ _], h | [.sym _], h
                              | [.closure _ _ _], h | [.prim _], h
                              | [.builtinBaseApply], h =>
                                obtain rfl := Option.some.inj h; rfl
                            · rw [if_neg h₁₄] at h
                              by_cases h₁₅ : name = "pair?"
                              · rw [if_pos h₁₅] at h
                                unfold applyPrim_pairQ at h
                                match args, h with
                                | [.num _], h | [.bool _], h | [.nilV], h
                                | [.cons _ _], h | [.sym _], h
                                | [.closure _ _ _], h | [.prim _], h
                                | [.builtinBaseApply], h =>
                                  obtain rfl := Option.some.inj h; rfl
                              · rw [if_neg h₁₅] at h
                                cases h

/-! ### Inductive step

The full proof of `AllPureIndep (n+1)` assuming `AllPureIndep n`.
Leaf eval cases (.num, .bool, .lam, .var, .quote) close mechanically;
recursive cases (.ifte, .app, .em, .primApp, .letE, .seq) thread the
IH; vacuous cases (.set, .installPolicy) use `Pure = false`. Each
function (eval, evalList, applyVia, applyDirect) gets both
policy-independence and the preservation clauses
(PureVal of result, PureHeap of post-state). -/

theorem allPureIndep_succ (n : Nat) (IH : AllPureIndep n) :
    AllPureIndep (n + 1) := by
  obtain ⟨IH_eval, IH_evalList, IH_applyVia, IH_applyDirect⟩ := IH
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- eval clause
    intro level M env T h_M h_T
    refine ⟨?_, ?_⟩
    · -- Policy-independence: ∀ p₁ p₂, eval ... p₁ = eval ... p₂.
      intro p₁ p₂
      cases M with
      | num i => simp [eval]
      | bool b => simp [eval]
      | quote v => simp [eval]
      | var x => simp [eval]
      | lam ps b => simp [eval]
      | ifte c t e =>
          simp only [Pure, Bool.and_eq_true] at h_M
          obtain ⟨⟨h_c, h_t⟩, h_e⟩ := h_M
          show eval (n+1) p₁ level (.ifte c t e) env T
                = eval (n+1) p₂ level (.ifte c t e) env T
          simp only [eval]
          rw [(IH_eval level c env T h_c h_T).1 p₁ p₂]
          generalize h_ec : eval n p₂ level c env T = ec
          match ec with
          | none => rfl
          | some (.bool false, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level e env T' h_e h_T').1 p₁ p₂
          | some (.bool true, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.num _, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.nilV, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.sym _, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.cons _ _, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.closure _ _ _, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.prim _, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
          | some (.builtinBaseApply, T') =>
              have ⟨_, h_T'⟩ := (IH_eval level c env T h_c h_T).2 p₂ _ T' h_ec
              exact (IH_eval level t env T' h_t h_T').1 p₁ p₂
      | app exps =>
          cases exps with
          | nil => simp [eval]
          | cons f args =>
              simp only [Pure, PureList, Bool.and_eq_true] at h_M
              obtain ⟨h_f, h_args⟩ := h_M
              show eval (n+1) p₁ level (.app (f :: args)) env T
                    = eval (n+1) p₂ level (.app (f :: args)) env T
              simp only [eval]
              rw [(IH_eval level f env T h_f h_T).1 p₁ p₂]
              generalize h_ef : eval n p₂ level f env T = ef
              cases ef with
              | none => rfl
              | some result =>
                  obtain ⟨fv, T'⟩ := result
                  have ⟨h_fv, h_T'⟩ :=
                    (IH_eval level f env T h_f h_T).2 p₂ fv T' h_ef
                  show (match evalList n p₁ level args env T' with
                        | none => none
                        | some (avs, T'') => applyVia n p₁ level fv avs T'')
                      = (match evalList n p₂ level args env T' with
                          | none => none
                          | some (avs, T'') => applyVia n p₂ level fv avs T'')
                  rw [(IH_evalList level args env T' h_args h_T').1 p₁ p₂]
                  generalize h_el : evalList n p₂ level args env T' = el
                  cases el with
                  | none => rfl
                  | some result' =>
                      obtain ⟨avs, T''⟩ := result'
                      have ⟨h_avs, h_T''⟩ :=
                        (IH_evalList level args env T' h_args h_T').2 p₂ avs T'' h_el
                      show applyVia n p₁ level fv avs T''
                            = applyVia n p₂ level fv avs T''
                      exact (IH_applyVia level fv avs T'' h_fv h_avs h_T'').1 p₁ p₂
      | set x e => simp [Pure] at h_M
      | em b =>
          simp only [Pure] at h_M
          show eval (n+1) p₁ level (.em b) env T = eval (n+1) p₂ level (.em b) env T
          simp only [eval]
          cases h_mat : T.materialize (level + 1) with
          | none => simp [h_mat]
          | some T' =>
              simp [h_mat]
              have h_T' := materialize_preserves_PureHeap h_mat h_T
              cases h_env : T'.envAt? (level + 1) with
              | none => simp [h_env]
              | some upEnv =>
                  simp [h_env]
                  exact (IH_eval (level + 1) b upEnv T' h_M h_T').1 p₁ p₂
      | primApp f args =>
          simp only [Pure, Bool.and_eq_true] at h_M
          obtain ⟨h_f, h_args⟩ := h_M
          show eval (n+1) p₁ level (.primApp f args) env T
                = eval (n+1) p₂ level (.primApp f args) env T
          simp only [eval]
          rw [(IH_eval level f env T h_f h_T).1 p₁ p₂]
          generalize h_ef : eval n p₂ level f env T = ef
          cases ef with
          | none => rfl
          | some result =>
              obtain ⟨fv, T'⟩ := result
              have ⟨h_fv, h_T'⟩ :=
                (IH_eval level f env T h_f h_T).2 p₂ fv T' h_ef
              show (match evalList n p₁ level args env T' with
                    | none => none
                    | some (avs, T'') => applyDirect n p₁ level fv avs T'')
                  = (match evalList n p₂ level args env T' with
                      | none => none
                      | some (avs, T'') => applyDirect n p₂ level fv avs T'')
              rw [(IH_evalList level args env T' h_args h_T').1 p₁ p₂]
              generalize h_el : evalList n p₂ level args env T' = el
              cases el with
              | none => rfl
              | some result' =>
                  obtain ⟨avs, T''⟩ := result'
                  have ⟨h_avs, h_T''⟩ :=
                    (IH_evalList level args env T' h_args h_T').2 p₂ avs T'' h_el
                  show applyDirect n p₁ level fv avs T''
                        = applyDirect n p₂ level fv avs T''
                  exact (IH_applyDirect level fv avs T'' h_fv h_avs h_T'').1 p₁ p₂
      | letE x e body =>
          simp only [Pure, Bool.and_eq_true] at h_M
          obtain ⟨h_e, h_body⟩ := h_M
          show eval (n+1) p₁ level (.letE x e body) env T
                = eval (n+1) p₂ level (.letE x e body) env T
          simp only [eval]
          rw [(IH_eval level e env T h_e h_T).1 p₁ p₂]
          generalize h_ee : eval n p₂ level e env T = ee
          cases ee with
          | none => rfl
          | some result =>
              obtain ⟨v_e, T'⟩ := result
              have ⟨h_v_e, h_T'⟩ :=
                (IH_eval level e env T h_e h_T).2 p₂ v_e T' h_ee
              have h_T_alloc :=
                TowerState_alloc_preserves_PureHeap h_T' h_v_e
              exact (IH_eval level body _ _ h_body h_T_alloc).1 p₁ p₂
      | seq exps =>
          cases exps with
          | nil => simp [eval]
          | cons e rest =>
              cases rest with
              | nil =>
                  simp only [Pure, PureList, Bool.and_eq_true] at h_M
                  obtain ⟨h_e, _⟩ := h_M
                  show eval (n+1) p₁ level (.seq [e]) env T
                        = eval (n+1) p₂ level (.seq [e]) env T
                  simp only [eval]
                  exact (IH_eval level e env T h_e h_T).1 p₁ p₂
              | cons e2 rest2 =>
                  simp only [Pure, PureList, Bool.and_eq_true] at h_M
                  obtain ⟨h_e, h_rest⟩ := h_M
                  show eval (n+1) p₁ level (.seq (e :: e2 :: rest2)) env T
                        = eval (n+1) p₂ level (.seq (e :: e2 :: rest2)) env T
                  simp only [eval]
                  rw [(IH_eval level e env T h_e h_T).1 p₁ p₂]
                  generalize h_ee : eval n p₂ level e env T = ee
                  cases ee with
                  | none => rfl
                  | some result =>
                      obtain ⟨_, T'⟩ := result
                      have ⟨_, h_T'⟩ :=
                        (IH_eval level e env T h_e h_T).2 p₂ _ T' h_ee
                      have h_seq_pure : Pure (.seq (e2 :: rest2)) = true := by
                        simp [Pure, PureList]; exact h_rest
                      exact (IH_eval level (.seq (e2 :: rest2)) env T'
                              h_seq_pure h_T').1 p₁ p₂
      | installPolicy idx => simp [Pure] at h_M
    · -- Preservation.
      intro p v T' h_some
      cases M with
      | num i =>
          simp [eval] at h_some
          obtain ⟨rfl, rfl⟩ := h_some
          exact ⟨by simp [PureVal], h_T⟩
      | bool b =>
          simp [eval] at h_some
          obtain ⟨rfl, rfl⟩ := h_some
          exact ⟨by simp [PureVal], h_T⟩
      | quote v_q =>
          simp [eval] at h_some
          cases h_cl : closedValB v_q
          · simp [h_cl] at h_some
          · simp [h_cl] at h_some
            obtain ⟨rfl, rfl⟩ := h_some
            refine ⟨?_, h_T⟩
            simp [Pure] at h_M; exact h_M
      | var x =>
          simp [eval] at h_some
          split at h_some
          · split at h_some
            · obtain ⟨rfl, rfl⟩ := h_some
              refine ⟨?_, h_T⟩
              exact PureHeap_getElem? h_T (by assumption)
            · cases h_some
          · cases h_some
      | lam ps body =>
          simp [eval] at h_some
          obtain ⟨rfl, rfl⟩ := h_some
          refine ⟨?_, h_T⟩
          simp [Pure] at h_M
          simp [PureVal]; exact h_M
      | ifte c t e =>
          simp only [Pure, Bool.and_eq_true] at h_M
          obtain ⟨⟨h_c, h_t⟩, h_e⟩ := h_M
          simp only [eval] at h_some
          match h_ec : eval n p level c env T, h_some with
          | none, h_s => simp [h_ec] at h_s
          | some (.bool false, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level e env T'' h_e h_T'').2 p v T' h_s
          | some (.bool true, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.num _, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.nilV, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.sym _, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.cons _ _, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.closure _ _ _, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.prim _, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
          | some (.builtinBaseApply, T''), h_s =>
              simp [h_ec] at h_s
              have ⟨_, h_T''⟩ := (IH_eval level c env T h_c h_T).2 p _ T'' h_ec
              exact (IH_eval level t env T'' h_t h_T'').2 p v T' h_s
      | app exps =>
          cases exps with
          | nil => simp [eval] at h_some
          | cons f args =>
              simp only [Pure, PureList, Bool.and_eq_true] at h_M
              obtain ⟨h_f, h_args⟩ := h_M
              simp only [eval] at h_some
              match h_ef : eval n p level f env T, h_some with
              | none, h_s => simp [h_ef] at h_s
              | some (fv, T''), h_s =>
                  simp [h_ef] at h_s
                  have ⟨h_fv, h_T''⟩ :=
                    (IH_eval level f env T h_f h_T).2 p fv T'' h_ef
                  match h_el : evalList n p level args env T'', h_s with
                  | none, h_s' => simp [h_el] at h_s'
                  | some (avs, T'''), h_s' =>
                      simp [h_el] at h_s'
                      have ⟨h_avs, h_T'''⟩ :=
                        (IH_evalList level args env T'' h_args h_T'').2 p avs T''' h_el
                      exact (IH_applyVia level fv avs T''' h_fv h_avs h_T''').2 p v T' h_s'
      | set x e => simp [Pure] at h_M
      | em b =>
          simp only [Pure] at h_M
          simp only [eval] at h_some
          match h_mat : T.materialize (level + 1), h_some with
          | none, h_s => simp [h_mat] at h_s
          | some T'', h_s =>
              simp [h_mat] at h_s
              have h_T'' := materialize_preserves_PureHeap h_mat h_T
              match h_env : T''.envAt? (level + 1), h_s with
              | none, h_s' => simp [h_env] at h_s'
              | some upEnv, h_s' =>
                  simp [h_env] at h_s'
                  exact (IH_eval (level + 1) b upEnv T'' h_M h_T'').2 p v T' h_s'
      | primApp f args =>
          simp only [Pure, Bool.and_eq_true] at h_M
          obtain ⟨h_f, h_args⟩ := h_M
          simp only [eval] at h_some
          match h_ef : eval n p level f env T, h_some with
          | none, h_s => simp [h_ef] at h_s
          | some (fv, T''), h_s =>
              simp [h_ef] at h_s
              have ⟨h_fv, h_T''⟩ :=
                (IH_eval level f env T h_f h_T).2 p fv T'' h_ef
              match h_el : evalList n p level args env T'', h_s with
              | none, h_s' => simp [h_el] at h_s'
              | some (avs, T'''), h_s' =>
                  simp [h_el] at h_s'
                  have ⟨h_avs, h_T'''⟩ :=
                    (IH_evalList level args env T'' h_args h_T'').2 p avs T''' h_el
                  exact (IH_applyDirect level fv avs T''' h_fv h_avs h_T''').2 p v T' h_s'
      | letE x e body =>
          simp only [Pure, Bool.and_eq_true] at h_M
          obtain ⟨h_e, h_body⟩ := h_M
          simp only [eval] at h_some
          match h_ee : eval n p level e env T, h_some with
          | none, h_s => simp [h_ee] at h_s
          | some (v_e, T''), h_s =>
              simp [h_ee] at h_s
              have ⟨h_v_e, h_T''⟩ :=
                (IH_eval level e env T h_e h_T).2 p v_e T'' h_ee
              have h_T_alloc :=
                TowerState_alloc_preserves_PureHeap h_T'' h_v_e
              exact (IH_eval level body _ _ h_body h_T_alloc).2 p v T' h_s
      | seq exps =>
          cases exps with
          | nil =>
              simp only [eval] at h_some
              obtain ⟨rfl, rfl⟩ := h_some
              exact ⟨by simp [PureVal], h_T⟩
          | cons e rest =>
              cases rest with
              | nil =>
                  simp only [Pure, PureList, Bool.and_eq_true] at h_M
                  obtain ⟨h_e, _⟩ := h_M
                  simp only [eval] at h_some
                  exact (IH_eval level e env T h_e h_T).2 p v T' h_some
              | cons e2 rest2 =>
                  simp only [Pure, PureList, Bool.and_eq_true] at h_M
                  obtain ⟨h_e, h_rest⟩ := h_M
                  simp only [eval] at h_some
                  match h_ee : eval n p level e env T, h_some with
                  | none, h_s => simp [h_ee] at h_s
                  | some (_, T''), h_s =>
                      simp [h_ee] at h_s
                      have ⟨_, h_T''⟩ :=
                        (IH_eval level e env T h_e h_T).2 p _ T'' h_ee
                      have h_seq_pure : Pure (.seq (e2 :: rest2)) = true := by
                        simp [Pure, PureList]; exact h_rest
                      exact (IH_eval level (.seq (e2 :: rest2)) env T''
                              h_seq_pure h_T'').2 p v T' h_s
      | installPolicy idx => simp [Pure] at h_M
  · -- evalList clause
    intro level Ms env T h_Ms h_T
    refine ⟨?_, ?_⟩
    · intro p₁ p₂
      cases Ms with
      | nil => simp [evalList]
      | cons hd tl =>
          simp only [PureList, Bool.and_eq_true] at h_Ms
          obtain ⟨h_hd, h_tl⟩ := h_Ms
          show evalList (n+1) p₁ level (hd :: tl) env T
                = evalList (n+1) p₂ level (hd :: tl) env T
          simp only [evalList]
          have h_outer := (IH_eval level hd env T h_hd h_T).1 p₁ p₂
          rw [h_outer]
          generalize h_e : eval n p₂ level hd env T = e
          cases e with
          | none => rfl
          | some result =>
              obtain ⟨v, T'⟩ := result
              have ⟨_, h_T'⟩ :=
                (IH_eval level hd env T h_hd h_T).2 p₂ v T' h_e
              show (match evalList n p₁ level tl env T' with
                     | none => none
                     | some (vs, T'') => some (v :: vs, T''))
                 = (match evalList n p₂ level tl env T' with
                     | none => none
                     | some (vs, T'') => some (v :: vs, T''))
              rw [(IH_evalList level tl env T' h_tl h_T').1 p₁ p₂]
    · intro p vs T' h_some
      cases Ms with
      | nil =>
          simp [evalList] at h_some
          obtain ⟨rfl, rfl⟩ := h_some
          exact ⟨by simp [PureValList], h_T⟩
      | cons hd tl =>
          simp only [PureList, Bool.and_eq_true] at h_Ms
          obtain ⟨h_hd, h_tl⟩ := h_Ms
          simp only [evalList] at h_some
          match h_e : eval n p level hd env T, h_some with
          | none, h_s => simp [h_e] at h_s
          | some (v, T''), h_s =>
              simp [h_e] at h_s
              have ⟨h_v, h_T''⟩ :=
                (IH_eval level hd env T h_hd h_T).2 p v T'' h_e
              match h_el : evalList n p level tl env T'', h_s with
              | none, h_s' => simp [h_el] at h_s'
              | some (vs', T'''), h_s' =>
                  simp [h_el] at h_s'
                  obtain ⟨rfl, rfl⟩ := h_s'
                  have ⟨h_vs', h_T'''⟩ :=
                    (IH_evalList level tl env T'' h_tl h_T'').2 p vs' T''' h_el
                  refine ⟨?_, h_T'''⟩
                  simp [PureValList]
                  exact ⟨h_v, h_vs'⟩
  · -- applyVia clause
    intro level op args T h_op h_args h_T
    refine ⟨?_, ?_⟩
    · -- Policy-independence
      intro p₁ p₂
      show applyVia (n+1) p₁ level op args T = applyVia (n+1) p₂ level op args T
      simp only [applyVia]
      cases h_mat : T.materialize (level + 1) with
      | none => simp [h_mat]
      | some T' =>
          simp [h_mat]
          have h_T' := materialize_preserves_PureHeap h_mat h_T
          cases h_env : T'.envAt? (level + 1) with
          | none =>
              simp [h_env]
              exact (IH_applyDirect level op args T' h_op h_args h_T').1 p₁ p₂
          | some upEnv =>
              simp [h_env]
              cases h_la : upEnv.lookup "base-apply" with
              | none =>
                  simp [h_la]
                  exact (IH_applyDirect level op args T' h_op h_args h_T').1 p₁ p₂
              | some idx =>
                  simp [h_la]
                  cases h_cell : T'.heap[idx]? with
                  | none => rfl
                  | some baseApply =>
                      have h_ba_pure : PureVal baseApply = true :=
                        PureHeap_getElem? h_T' h_cell
                      have h_listToVal : ∀ xs, PureValList xs = true →
                          PureVal (listToVal xs) = true := by
                        intro xs
                        induction xs with
                        | nil => intro _; rfl
                        | cons x xs IH =>
                            intro h
                            simp only [PureValList, Bool.and_eq_true] at h
                            simp only [listToVal, PureVal, Bool.and_eq_true]
                            exact ⟨h.1, IH h.2⟩
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]; exact ⟨h_op, h_listToVal args h_args⟩
                      cases baseApply with
                      | builtinBaseApply =>
                          exact (IH_applyDirect level op args T'
                                   h_op h_args h_T').1 p₁ p₂
                      | num _ =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
                      | bool _ =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
                      | nilV =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
                      | sym _ =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
                      | cons _ _ =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
                      | closure _ _ _ =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
                      | prim _ =>
                          exact (IH_applyDirect level _ [op, listToVal args]
                                  T' h_ba_pure h_args' h_T').1 p₁ p₂
    · -- Preservation
      intro p v T' h_some
      simp only [applyVia] at h_some
      match h_mat : T.materialize (level + 1), h_some with
      | none, h_s => simp [h_mat] at h_s
      | some T'', h_s =>
          simp [h_mat] at h_s
          have h_T'' := materialize_preserves_PureHeap h_mat h_T
          match h_env : T''.envAt? (level + 1), h_s with
          | none, h_s' =>
              simp [h_env] at h_s'
              exact (IH_applyDirect level op args T'' h_op h_args h_T'').2 p v T' h_s'
          | some upEnv, h_s' =>
              simp [h_env] at h_s'
              match h_la : upEnv.lookup "base-apply", h_s' with
              | none, h_s'' =>
                  simp [h_la] at h_s''
                  exact (IH_applyDirect level op args T'' h_op h_args h_T'').2 p v T' h_s''
              | some idx, h_s'' =>
                  simp [h_la] at h_s''
                  match h_cell : T''.heap[idx]?, h_s'' with
                  | none, h_s''' => simp [h_cell] at h_s'''
                  | some .builtinBaseApply, h_s''' =>
                      simp [h_cell] at h_s'''
                      exact (IH_applyDirect level op args T'' h_op h_args h_T'').2 p v T' h_s'''
                  | some (.closure ps body cenv), h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_ba_pure : PureVal (.closure ps body cenv) = true :=
                        PureHeap_getElem? h_T'' h_cell
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              h_ba_pure h_args' h_T'').2 p v T' h_s'''
                  | some (.num _), h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              (by simp [PureVal]) h_args' h_T'').2 p v T' h_s'''
                  | some (.bool _), h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              (by simp [PureVal]) h_args' h_T'').2 p v T' h_s'''
                  | some .nilV, h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              (by simp [PureVal]) h_args' h_T'').2 p v T' h_s'''
                  | some (.cons _ _), h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_ba_pure : PureVal _ = true :=
                        PureHeap_getElem? h_T'' h_cell
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              h_ba_pure h_args' h_T'').2 p v T' h_s'''
                  | some (.sym _), h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              (by simp [PureVal]) h_args' h_T'').2 p v T' h_s'''
                  | some (.prim _), h_s''' =>
                      simp [h_cell] at h_s'''
                      have h_args' : PureValList [op, listToVal args] = true := by
                        simp [PureValList]
                        exact ⟨h_op, PureVal_listToVal h_args⟩
                      exact (IH_applyDirect level _ [op, listToVal args] T''
                              (by simp [PureVal]) h_args' h_T'').2 p v T' h_s'''
  · -- applyDirect clause
    intro level op args T h_op h_args h_T
    refine ⟨?_, ?_⟩
    · -- Policy-independence
      intro p₁ p₂
      show applyDirect (n+1) p₁ level op args T = applyDirect (n+1) p₂ level op args T
      unfold applyDirect
      cases op with
      | num _ => rfl
      | bool _ => rfl
      | nilV => rfl
      | sym _ => rfl
      | cons _ _ => rfl
      | builtinBaseApply =>
          cases args with
          | nil => rfl
          | cons _ tl =>
              cases tl with
              | nil => rfl
              | cons opList tl2 =>
                  cases tl2 with
                  | nil =>
                      simp only [PureValList, Bool.and_eq_true] at h_args
                      cases h_vtl : valToList opList with
                      | none => simp [h_vtl]
                      | some operands =>
                          simp [h_vtl]
                          have h_ops_pure :=
                            valToList_PureValList h_args.2.1 h_vtl
                          exact (IH_applyDirect level _ operands T
                                  h_args.1 h_ops_pure h_T).1 p₁ p₂
                  | cons _ _ => rfl
      | closure ps body cenv =>
          simp only [PureVal] at h_op
          by_cases h_len : ps.length = args.length
          · simp [bne, h_len]
            have h_pairs := PureValList_zip_left h_args (ps := ps)
            have h_heap' :=
              foldl_allocStep_preserves_PureHeap (args.zip ps) T.heap cenv h_T h_pairs
            exact (IH_eval level body _ _ h_op h_heap').1 p₁ p₂
          · simp [bne, h_len]
      | prim _ => rfl
    · -- Preservation
      intro p v T' h_some
      unfold applyDirect at h_some
      cases op with
      | num _ => cases h_some
      | bool _ => cases h_some
      | nilV => cases h_some
      | sym _ => cases h_some
      | cons _ _ => cases h_some
      | builtinBaseApply =>
          match args, h_some with
          | [], h => cases h
          | [_], h => cases h
          | [actualOp, opList], h_s =>
              simp only [PureValList, Bool.and_eq_true] at h_args
              cases h_vtl : valToList opList with
              | none => simp [h_vtl] at h_s
              | some operands =>
                  simp [h_vtl] at h_s
                  have h_ops_pure :=
                    valToList_PureValList h_args.2.1 h_vtl
                  exact (IH_applyDirect level _ operands T
                          h_args.1 h_ops_pure h_T).2 p v T' h_s
          | _ :: _ :: _ :: _, h => cases h
      | closure ps body cenv =>
          simp only [PureVal] at h_op
          by_cases h_len : ps.length = args.length
          · simp [bne, h_len] at h_some
            have h_pairs := PureValList_zip_left h_args (ps := ps)
            have h_heap' :=
              foldl_allocStep_preserves_PureHeap (args.zip ps) T.heap cenv h_T h_pairs
            exact (IH_eval level body _ _ h_op h_heap').2 p v T' h_some
          · simp [bne, h_len] at h_some
      | prim name =>
          cases h_pa : applyPrim name args with
          | none => simp [h_pa] at h_some
          | some v' =>
              simp [h_pa] at h_some
              obtain ⟨rfl, rfl⟩ := h_some
              exact ⟨applyPrim_PureVal h_args h_pa, h_T⟩

theorem allPureIndep : ∀ fuel, AllPureIndep fuel
  | 0     => allPureIndep_zero
  | n + 1 => allPureIndep_succ n (allPureIndep n)

/-- The empty heap is `PureHeap` (vacuously). -/
theorem PureHeap_empty : PureHeap [] := by
  intro i v h; simp at h

/-- `initTower`'s heap is `PureHeap`: it's built by `freshLevelEnv []`
    (one materializeStep from the empty state), which only adds
    primitive cells. -/
theorem PureHeap_initTower : PureHeap initTower.heap := by
  unfold initTower buildTower
  simp only [Nat.fold]
  exact freshLevelEnv_preserves_PureHeap [] PureHeap_empty

/-- `setPolicyAt` doesn't change the heap, so `PureHeap` is preserved. -/
theorem setPolicyAt_preserves_PureHeap {T : TowerState} {n : Nat} {p : BlackPolicy}
    (h_T : PureHeap T.heap) : PureHeap (T.setPolicyAt n p).heap := by
  unfold TowerState.setPolicyAt
  split <;> exact h_T

/-! ### β-redex W1 under the gated policy table

With `AllPureIndep` in hand, we can upgrade `wand_defeated_existential`
to use the β-redex witness `((λx. x) 0)` vs `.num 0` under the gated
policy table `[approvedPolicy approvals]`. The β-redex is `Pure`
(no `.set`, no `.installPolicy`), so the policy-independence lemma
applies. -/

/-- Top-level `evalProgram` is policy-independent for `Pure` programs. -/
theorem evalProgram_pure_indep (M : Expr) (h_M : Pure M = true) (fuel : Nat)
    (p₁ p₂ : PolicyTable) :
    evalProgram fuel p₁ M = evalProgram fuel p₂ M := by
  have h_T_pure : PureHeap (initTower.setPolicyAt 0 acceptAllPolicy).heap :=
    setPolicyAt_preserves_PureHeap PureHeap_initTower
  simp only [evalProgram]
  generalize h_env : (initTower.setPolicyAt 0 acceptAllPolicy).envAt? 0 = e
  cases e with
  | none => rfl
  | some env =>
      show Option.map Prod.fst
            (eval fuel p₁ 0 M env (initTower.setPolicyAt 0 acceptAllPolicy))
          = Option.map Prod.fst
            (eval fuel p₂ 0 M env (initTower.setPolicyAt 0 acceptAllPolicy))
      rw [((allPureIndep fuel).1 0 M env _ h_M h_T_pure).1 p₁ p₂]

theorem wand_defeated_existential_gated_beta
    (approvals : List ApprovedModification) :
    ∃ M N : Expr, M ≠ N ∧ ObsEquivConvergesGated approvals M N := by
  refine ⟨.app [.lam ["x"] (.var "x"), .num 0], .num 0, ?_, ?_⟩
  · intro h; cases h
  · refine ⟨100, .num 0, ?_, ?_⟩
    · have h_M_pure : Pure (.app [.lam ["x"] (.var "x"), .num 0]) = true := by
        decide
      rw [evalProgram_pure_indep _ h_M_pure 100
            [approvedPolicy approvals] [acceptAllPolicy]]
      -- `decide +kernel`: kernel evaluation, no trusted-compiler axiom.
      decide +kernel
    · simp [evalProgram, eval]; rfl

/-! ## Multn approval — fuel-split machinery

The multn approval itself lives in `LeanBlack/HeapAgree.lean`: its
certificate is the *selective* proof (`multnApproval_at_proof`,
pinning only the closure's captured `orig` and `num?` cells), with
the full-prefix `CE_weak_strong` form derived via
`CE_weak_strong_of_at`. What remains here is the fuel-split
machinery that proof consumes:

**Fuel split.** `multnExact_soundForCE_first_install_tower` requires
`fuel ≥ 2`, while the certificate quantifies over arbitrary `fuel`.
- `fuel = 0`: `callAsBaseApply 0 .builtinBaseApply ... = applyDirect 0 ... = none`,
  so the old-side call is unsatisfiable. Vacuous.
- `fuel = 1`: `callAsBaseApply 1 .builtinBaseApply op operands T
  = applyDirect 1 ... op operands T`. By case on `op`:
  - `.num`/`.bool`/`.nilV`/`.sym`/`.cons`/`.closure`: `applyDirect 1`
    returns `none` (closure body eval with fuel 0 is `none`; other
    constructors are non-callable). Vacuous.
  - `.prim p`: returns `some (applyPrim p operands, T)` (fuel-
    independent). Handled by "bumping" fuel to 2
    (`applyDirect_prim_fuel_bump`).
  - `.builtinBaseApply`: recurses to `applyDirect 0` → `none`.
    Vacuous.
- `fuel ≥ 2`: invoke the multn theorem directly.
-/

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
      cases h

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

/-! ### The multn approval — moved

`multnApproval` now lives in `LeanBlack/HeapAgree.lean`, where its
certificate is *derived* from the selective proof
`multnApproval_at_proof` via `CE_weak_strong_of_at` — there is one
multn proof, not two. The fuel-split helpers above remain here; the
selective proof consumes them. -/

end LeanBlack
