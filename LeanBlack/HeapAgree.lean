/-
  lean-sage: HeapAgreeAt — selective heap-prefix relation.

  `HeapPrefix h₁ h₂` (in `ProofBased.lean`) demands content-equality
  at *every* index < `h₁.length`. The multn-style CE proofs only
  read specific cells (the closure's captured `orig` and `num?`
  indices). After a `.set "base-apply"` commits, the base-apply
  cell's content changes — breaking `HeapPrefix` even though the
  cells the proof reads are unchanged.

  `HeapAgreeAt indices h₁ h₂` demands content-equality at exactly
  the specified indices. With length-extension carried separately,
  this is the right premise for "the proof's cell lookups
  transport to a later heap." Preserved by heap appends and by
  heap-updates at any index not in `indices`.

  This file provides the predicate + foundational lemmas. The
  multn proof refactor that consumes them is a separate step.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Soundness
import LeanBlack.Policies
import LeanBlack.ProofBased

open LeanBlack

namespace LeanBlack

/-- `HeapAgreeAt indices h₁ h₂` iff for every `i ∈ indices`,
    `h₁[i]? = h₂[i]?`. Note: no length constraint on either side;
    out-of-bounds on either side both yield `none`, which trivially
    agree. -/
def HeapAgreeAt (indices : List Nat) (h₁ h₂ : Heap) : Prop :=
  ∀ i ∈ indices, h₁[i]? = h₂[i]?

/-- Reflexivity. -/
theorem HeapAgreeAt.refl (indices : List Nat) (h : Heap) :
    HeapAgreeAt indices h h := by
  intro _ _; rfl

/-- Symmetry. -/
theorem HeapAgreeAt.symm {indices : List Nat} {h₁ h₂ : Heap}
    (hab : HeapAgreeAt indices h₁ h₂) :
    HeapAgreeAt indices h₂ h₁ := by
  intro i hi; exact (hab i hi).symm

/-- Transitivity. -/
theorem HeapAgreeAt.trans {indices : List Nat} {h₁ h₂ h₃ : Heap}
    (h12 : HeapAgreeAt indices h₁ h₂) (h23 : HeapAgreeAt indices h₂ h₃) :
    HeapAgreeAt indices h₁ h₃ := by
  intro i hi; exact (h12 i hi).trans (h23 i hi)

/-- `HeapPrefix h₁ h₂` (full content prefix) implies `HeapAgreeAt`
    on any list of indices < `h₁.length`. The wider relation
    discards information; the lemma confirms the implication is
    in the safe direction. -/
theorem HeapPrefix.toHeapAgreeAt
    {h₁ h₂ : Heap} {indices : List Nat}
    (hp : HeapPrefix h₁ h₂)
    (h_bounds : ∀ i ∈ indices, i < h₁.length) :
    HeapAgreeAt indices h₁ h₂ := by
  intro i hi
  have h_lt : i < h₁.length := h_bounds i hi
  have h_take : h₁ = h₂.take h₁.length := hp
  rw [h_take]
  rw [List.getElem?_take]
  split
  · rfl
  · omega

/-- `HeapAgreeAt` survives appending cells beyond the indices' max.
    Specifically, if all indices < `h₁.length` (so within the
    pre-append portion), then appending preserves agreement on
    those indices.

    This is the bread-and-butter monotonicity: heap allocation only
    grows the heap, never disturbs existing cells. -/
theorem HeapAgreeAt.append_right
    {indices : List Nat} {h₁ h₂ : Heap} (extras : List Val)
    (h_agree : HeapAgreeAt indices h₁ h₂)
    (h_bounds : ∀ i ∈ indices, i < h₂.length) :
    HeapAgreeAt indices h₁ (h₂ ++ extras) := by
  intro i hi
  have h_lt : i < h₂.length := h_bounds i hi
  rw [h_agree i hi, List.getElem?_append_left h_lt]

/-- Helper: heap-update at index `j` leaves all other indices
    unchanged. (List.set-like behavior on the custom Heap.update.) -/
theorem heap_update_get_ne (h : Heap) (j : Nat) (v : Val) (i : Nat)
    (h_ne : i ≠ j) :
    (h.update j v)[i]? = h[i]? := by
  induction h generalizing i j with
  | nil => simp [Heap.update]
  | cons x t ih =>
    cases j with
    | zero =>
      cases i with
      | zero => exact absurd rfl h_ne
      | succ i' => simp [Heap.update]
    | succ j' =>
      cases i with
      | zero => simp [Heap.update]
      | succ i' =>
        simp only [Heap.update, List.getElem?_cons_succ]
        have h_ne' : i' ≠ j' := fun h_eq => h_ne (congrArg Nat.succ h_eq)
        exact ih j' i' h_ne'

/-- `HeapAgreeAt` survives heap-update at any index *not* in the
    agreement set. This is the key lemma for post-mutation lifting:
    a `.set "base-apply"` mutates the level's base-apply cell;
    if that cell's index is not among the indices the CE proof
    reads, the agreement on those indices is preserved. -/
theorem HeapAgreeAt.update_disjoint
    {indices : List Nat} {h₁ h₂ : Heap} (j : Nat) (v : Val)
    (h_agree : HeapAgreeAt indices h₁ h₂)
    (h_disjoint : j ∉ indices) :
    HeapAgreeAt indices h₁ (h₂.update j v) := by
  intro i hi
  rw [h_agree i hi]
  have h_ne : i ≠ j := fun h_eq => h_disjoint (h_eq ▸ hi)
  exact (heap_update_get_ne h₂ j v i h_ne).symm

/-! ## CE_weak_strong_at — selective-prefix CE predicate

Mirrors `CE_weak_strong` but consumes `HeapAgreeAt indices` (with
length-monotonicity carried as a separate premise) instead of the
full `HeapPrefix`. Approvals constructed in this form survive
post-mutation lifting as long as the mutated cell is disjoint from
`indices`.

This is the predicate that unblocks contextual β: an approval
carrying `CE_weak_strong_at [idx_o, idx_n] …` (the multn-style
indices the proof actually reads) is consumable at any heap
preserving agreement at those two cells, including the
post-admission heap. -/

def CE_weak_strong_at (level : Nat) (indices : List Nat)
    (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    h_ref.length ≤ T.heap.length →
    HeapAgreeAt indices h_ref T.heap →
    HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
    ValValid old T.heap → ValValid new T.heap →
    PolicyTableRespectsBisimT ptable →
    (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
    (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
    HeapDeep T.heap → ValDeep op T.heap → ListValDeep operands T.heap →
    (∀ n env, T.envAt? n = some env → EnvDeep env T.heap) →
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

/-- Sanity check: a stronger `CE_weak_strong` certificate yields the
    weaker `CE_weak_strong_at` form, provided all `indices` lie
    within `h_ref`. The conversion uses `HeapPrefix.toHeapAgreeAt`
    to bridge the premises.

    Caveat: this works only because we have *both* the
    length-monotone premise (`h_ref.length ≤ T.heap.length`) AND
    can establish `HeapPrefix h_ref T.heap` from `HeapAgreeAt indices
    h_ref T.heap` *only when* indices cover the full prefix —
    which they don't, in general. So this is **not** a general
    conversion; it only works when `CE_weak_strong` was overkill
    to begin with.

    The real value of `CE_weak_strong_at` is for proofs that
    *cannot* be derived from `CE_weak_strong` — specifically, the
    multn proof under HeapPrefix-too-strong. -/
theorem CE_weak_strong_at.of_HeapPrefix_certificate
    {level : Nat} {indices : List Nat} {h_ref : Heap} {old new : Val}
    (_h_bounds : ∀ i ∈ indices, i < h_ref.length)
    (h_full_prefix_premise : ∀ T : TowerState,
        h_ref.length ≤ T.heap.length →
        HeapAgreeAt indices h_ref T.heap →
        HeapPrefix h_ref T.heap)
    (h_ce : CE_weak_strong level h_ref old new) :
    CE_weak_strong_at level indices h_ref old new := by
  intro fuel ptable op operands T r T' h_len h_agree
    h_heap h_op h_operands h_old h_new h_ptable h_lvl_pol h_env
    h_pol h_env_bisim h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift h_call
  exact h_ce fuel ptable op operands T r T'
    (h_full_prefix_premise T h_len h_agree)
    h_heap h_op h_operands h_old h_new h_ptable h_lvl_pol h_env
    h_pol h_env_bisim h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift h_call

/-! ## Extracting multn-style indices

For an admitted multn-style modification, the proof reads exactly
the `orig` cell and the `num?` cell from the closure's captured
env. The indices that need to be in `HeapAgreeAt` are precisely
these two. -/

/-- Extract the `orig` and `num?` indices from a closure value, if
    it has the multn shape. Returns `none` if the value isn't a
    closure or doesn't bind both names. -/
def multnRelevantIndices : Val → Option (Nat × Nat)
  | .closure _ _ cenv =>
      match cenv.lookup "orig", cenv.lookup "num?" with
      | some idx_o, some idx_n => some (idx_o, idx_n)
      | _, _ => none
  | _ => none

/-- `OrigBoundIn` transports across `HeapAgreeAt` at the relevant
    `orig` index. -/
theorem OrigBoundIn_heap_agree
    {h₁ h₂ : Heap} {old new : Val}
    (h_orig : OrigBoundIn h₁ old new)
    (h_agree : ∀ idx, (∃ ps body cenv, new = .closure ps body cenv ∧
                       cenv.lookup "orig" = some idx) →
                       h₁[idx]? = h₂[idx]?) :
    OrigBoundIn h₂ old new := by
  obtain ⟨ps, body, cenv, idx, h_eq, h_lookup, h_heap⟩ := h_orig
  refine ⟨ps, body, cenv, idx, h_eq, h_lookup, ?_⟩
  have h_eq_cells := h_agree idx ⟨ps, body, cenv, h_eq, h_lookup⟩
  rw [← h_eq_cells]; exact h_heap

/-- `NumQBoundIn` transports across `HeapAgreeAt` at the relevant
    `num?` index. -/
theorem NumQBoundIn_heap_agree
    {h₁ h₂ : Heap} {new : Val}
    (h_numq : NumQBoundIn h₁ new)
    (h_agree : ∀ idx, (∃ ps body cenv, new = .closure ps body cenv ∧
                       cenv.lookup "num?" = some idx) →
                       h₁[idx]? = h₂[idx]?) :
    NumQBoundIn h₂ new := by
  obtain ⟨ps, body, cenv, idx, h_eq, h_lookup, h_heap⟩ := h_numq
  refine ⟨ps, body, cenv, idx, h_eq, h_lookup, ?_⟩
  have h_eq_cells := h_agree idx ⟨ps, body, cenv, h_eq, h_lookup⟩
  rw [← h_eq_cells]; exact h_heap

/-- `InstallFacts` transports across `HeapAgreeAt` covering both
    the `orig` and `num?` indices. This is the key transport
    lemma the new multn proof uses, replacing the
    `InstallFacts_heap_extend` lemma that demanded full
    `HeapPrefix`. -/
theorem InstallFacts_heap_agree
    {h₁ h₂ : Heap} {old new : Val}
    (install : InstallFacts old new h₁)
    (h_agree_orig : ∀ idx, (∃ ps body cenv, new = .closure ps body cenv ∧
                              cenv.lookup "orig" = some idx) →
                              h₁[idx]? = h₂[idx]?)
    (h_agree_numq : ∀ idx, (∃ ps body cenv, new = .closure ps body cenv ∧
                              cenv.lookup "num?" = some idx) →
                              h₁[idx]? = h₂[idx]?) :
    InstallFacts old new h₂ :=
  { orig := OrigBoundIn_heap_agree install.orig h_agree_orig
    numq := NumQBoundIn_heap_agree install.numq h_agree_numq }

/-- Cleaner cell-level variant: explicit indices, single-cell
    agreement. The multn proof's actual use site. -/
theorem InstallFacts_heap_agree_cells
    {h₁ h₂ : Heap} {old new : Val} {idx_o idx_n : Nat}
    (h_shape_orig : ∃ ps body cenv, new = .closure ps body cenv ∧
                    cenv.lookup "orig" = some idx_o)
    (h_shape_numq : ∃ ps body cenv, new = .closure ps body cenv ∧
                    cenv.lookup "num?" = some idx_n)
    (install : InstallFacts old new h₁)
    (h_agree_o : h₁[idx_o]? = h₂[idx_o]?)
    (h_agree_n : h₁[idx_n]? = h₂[idx_n]?) :
    InstallFacts old new h₂ := by
  apply InstallFacts_heap_agree install
  · intro idx ⟨ps', body', cenv', h_eq', h_l'⟩
    obtain ⟨ps, body, cenv, h_eq, h_l⟩ := h_shape_orig
    rw [h_eq] at h_eq'
    injection h_eq' with h_ps h_body h_cenv
    subst h_ps; subst h_body; subst h_cenv
    rw [h_l] at h_l'
    injection h_l' with h_idx_eq
    subst h_idx_eq
    exact h_agree_o
  · intro idx ⟨ps', body', cenv', h_eq', h_l'⟩
    obtain ⟨ps, body, cenv, h_eq, h_l⟩ := h_shape_numq
    rw [h_eq] at h_eq'
    injection h_eq' with h_ps h_body h_cenv
    subst h_ps; subst h_body; subst h_cenv
    rw [h_l] at h_l'
    injection h_l' with h_idx_eq
    subst h_idx_eq
    exact h_agree_n

/-- Bridge from `HeapAgreeAt` on `[idx_o, idx_n]` to the two
    single-cell agreements `InstallFacts_heap_agree_cells` consumes. -/
theorem heapAgreeAt_pair_to_cells
    {idx_o idx_n : Nat} {h₁ h₂ : Heap}
    (h_agree : HeapAgreeAt [idx_o, idx_n] h₁ h₂) :
    h₁[idx_o]? = h₂[idx_o]? ∧ h₁[idx_n]? = h₂[idx_n]? :=
  ⟨h_agree idx_o (by simp), h_agree idx_n (by simp)⟩

/-! ## `multnApproval_at` — the multn approval, weakened-premise form

Mirrors `multnApproval` in `ProofBased.lean` but produces a
`CE_weak_strong_at` certificate. Almost the entire body is shared
with `multnApproval`'s proof; the only change is the InstallFacts
transport step, which now uses `InstallFacts_heap_agree_cells` +
`heapAgreeAt_pair_to_cells` instead of `InstallFacts_heap_extend`.

The constructed approval's certificate is **consumable
post-admission**: a `.set "base-apply"` mutation at a level
mutates `idx_ba`, which is disjoint from `[idx_o, idx_n]` (by the
`installMultnOneUp` pattern's `letE "orig" (var "base-apply")`
trick — `orig` is allocated fresh, separate from the level's
base-apply cell). So `HeapAgreeAt [idx_o, idx_n]` is preserved by
the .set, and the certificate continues to apply. -/

/-- The proof field of `multnApproval_at`, packaged so the
    `CE_weak_strong_at` signature can be discharged. Identical to
    `multnApproval`'s proof body except for the InstallFacts
    transport line.

    Takes `idx_o`, `idx_n` as explicit parameters with a witness
    that they match the closure's captured env. -/
theorem multnApproval_at_proof
    (level : Nat) (heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : multnExactPolicy
                 { target := "base-apply", heap := heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true)
    (idx_o idx_n : Nat)
    (h_shape_o : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "orig" = some idx_o)
    (h_shape_n : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "num?" = some idx_n) :
    CE_weak_strong_at level [idx_o, idx_n] heap .builtinBaseApply newClosure := by
  intro fuel ptable op operands T r T'
    _h_len h_agree
    h_heap h_op h_operands _h_old h_new
    h_ptable _h_lvl_pol h_env h_pol _h_env_bisim
    h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift h_call
  -- NEW: install facts via HeapAgreeAt instead of HeapPrefix.
  have ⟨_, install_heap⟩ := multnExactPolicy_implies_InstallFacts h_admit
  obtain ⟨h_agree_o, h_agree_n⟩ := heapAgreeAt_pair_to_cells h_agree
  have install_T : InstallFacts .builtinBaseApply newClosure T.heap :=
    InstallFacts_heap_agree_cells h_shape_o h_shape_n install_heap h_agree_o h_agree_n
  -- Rest of the proof mirrors `multnApproval` in `ProofBased.lean:1862-1896`.
  have wf : RuntimeWF newClosure op operands T := {
    hv_heap      := h_heap
    ev_levels    := h_env
    ev_cenv      := fun ps body cenv' h_eq => by
      have h_vv : ValValid (.closure ps body cenv') T.heap := h_eq ▸ h_new
      exact h_vv
    vv_op        := h_op
    lvv_operands := h_operands }
  match fuel, h_call with
  | 0,     h_call =>
      exact absurd h_call (by simp [callAsBaseApply, applyDirect])
  | 1,     h_call =>
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
      obtain ⟨fuel', T'', r', h_call', h_vv, h_pol_all, h_heap_v, h_mono⟩ :=
        multnExact_soundForCE_first_install_tower h_admit (by omega) h_ptable
          h_call install_T wf h_heap_deep h_op_deep h_operands_deep
          h_env_deep h_pol h_pt_shift h_pol_shift
      exact ⟨fuel', T'', r', h_call', h_vv, h_pol_all level, h_heap_v, h_mono⟩

end LeanBlack
