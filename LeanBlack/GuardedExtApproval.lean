/-
  lean-sage: Approval packaging for guarded-extension wrappers.

  Mirrors the multn approval layer (`HeapAgree.lean`): the selective
  certificate `guardedExtApproval_at_proof` pins exactly the two heap
  cells the master theorem reads (the closure's captured `orig` and
  guard bindings); `guardedExtApproval` widens it to the full-prefix
  `CE_weak_strong` form that `approvedPolicy` consumes.

  The only inputs beyond the admission fact are the guard name `g`
  and its `GuardSpec g` — the per-proposal obligations. Everything
  else is the class-level machinery from `GuardedExt.lean`.
-/

import LeanBlack.GuardedExt
import LeanBlack.HeapAgree

namespace LeanBlack

/-- Transport `GuardedInstallFacts` across heaps that agree on the two
    cells the facts mention. Mirrors `InstallFacts_heap_agree_cells`. -/
theorem GuardedInstallFacts_heap_agree_cells
    {g : String} {h₁ h₂ : Heap} {old new : Val} {idx_o idx_g : Nat}
    (h_shape_orig : ∃ ps body cenv, new = .closure ps body cenv ∧
                    cenv.lookup "orig" = some idx_o)
    (h_shape_guard : ∃ ps body cenv, new = .closure ps body cenv ∧
                     cenv.lookup g = some idx_g)
    (install : GuardedInstallFacts g old new h₁)
    (h_agree_o : h₁[idx_o]? = h₂[idx_o]?)
    (h_agree_g : h₁[idx_g]? = h₂[idx_g]?) :
    GuardedInstallFacts g old new h₂ := by
  constructor
  · obtain ⟨ps, body, cenv, idx, h_eq, h_l, h_cell⟩ := install.orig
    obtain ⟨ps', body', cenv', h_eq', h_l'⟩ := h_shape_orig
    rw [h_eq] at h_eq'
    injection h_eq' with h1 h2 h3
    subst h1; subst h2; subst h3
    rw [h_l] at h_l'
    injection h_l' with h4
    subst h4
    exact ⟨ps, body, cenv, idx, h_eq, h_l, by rw [← h_agree_o]; exact h_cell⟩
  · obtain ⟨ps, body, cenv, idx, h_eq, h_l, h_cell⟩ := install.guard
    obtain ⟨ps', body', cenv', h_eq', h_l'⟩ := h_shape_guard
    rw [h_eq] at h_eq'
    injection h_eq' with h1 h2 h3
    subst h1; subst h2; subst h3
    rw [h_l] at h_l'
    injection h_l' with h4
    subst h4
    exact ⟨ps, body, cenv, idx, h_eq, h_l, by rw [← h_agree_g]; exact h_cell⟩

/-- The selective certificate for a guarded-extension admission: the
    proof reads only the closure's captured `orig` and guard cells.
    Mirrors `multnApproval_at_proof`, with the master theorem
    (`guardedExt_soundForCE_first_install_tower`) in place of the
    multn headline and `GuardSpec g` as the per-proposal input. -/
theorem guardedExtApproval_at_proof
    {g : String} (spec : GuardSpec g)
    (level : Nat) (heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : guardedExtPolicy g
                 { target := "base-apply", heap := heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true)
    (idx_o idx_g : Nat)
    (h_shape_o : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "orig" = some idx_o)
    (h_shape_g : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup g = some idx_g) :
    CE_weak_strong_at level [idx_o, idx_g] heap .builtinBaseApply newClosure := by
  intro fuel ptable op operands T r T'
    _h_len h_agree
    h_heap h_op h_operands _h_old h_new
    h_ptable _h_lvl_pol h_env h_pol _h_env_bisim
    h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift h_call
  have ⟨_, install_heap⟩ := guardedExtPolicy_implies_InstallFacts h_admit
  obtain ⟨h_agree_o, h_agree_g⟩ := heapAgreeAt_pair_to_cells h_agree
  have install_T : GuardedInstallFacts g .builtinBaseApply newClosure T.heap :=
    GuardedInstallFacts_heap_agree_cells h_shape_o h_shape_g install_heap
      h_agree_o h_agree_g
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
        guardedExt_soundForCE_first_install_tower spec h_admit (by omega)
          h_ptable h_call_2 install_T wf h_heap_deep h_op_deep h_operands_deep
          h_env_deep h_pol h_pt_shift h_pol_shift
      exact ⟨fuel', T'', r', h_call', h_vv, h_pol_all level, h_heap_v, h_mono⟩
  | n + 2, h_call =>
      obtain ⟨fuel', T'', r', h_call', h_vv, h_pol_all, h_heap_v, h_mono⟩ :=
        guardedExt_soundForCE_first_install_tower spec h_admit (by omega)
          h_ptable h_call install_T wf h_heap_deep h_op_deep h_operands_deep
          h_env_deep h_pol h_pt_shift h_pol_shift
      exact ⟨fuel', T'', r', h_call', h_vv, h_pol_all level, h_heap_v, h_mono⟩

/-- A guarded-extension approval: the `ApprovedModification` for any
    admission of a `guardedExtPolicy g`-shaped wrapper, given the
    guard's `GuardSpec`. Mirrors `multnApproval`. The certificate is
    derived: the selective proof pins the two cells actually read,
    and `CE_weak_strong_of_at` widens to the full prefix. -/
def guardedExtApproval
    {g : String} (spec : GuardSpec g)
    (level : Nat) (heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : guardedExtPolicy g
                 { target := "base-apply", heap := heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true) :
    ApprovedModification :=
{ level   := level
  heap    := heap
  oldVal  := .builtinBaseApply
  newVal  := newClosure
  proof   := by
    have ⟨_, install_heap⟩ := guardedExtPolicy_implies_InstallFacts h_admit
    obtain ⟨ps_o, body_o, cenv_o, idx_o, h_eq_o, h_lk_o, h_cell_o⟩ := install_heap.orig
    obtain ⟨ps_g, body_g, cenv_g, idx_g, h_eq_g, h_lk_g, h_cell_g⟩ := install_heap.guard
    refine CE_weak_strong_of_at ?_
      (guardedExtApproval_at_proof spec level heap env metaEnv index newClosure
        h_admit idx_o idx_g
        ⟨ps_o, body_o, cenv_o, h_eq_o, h_lk_o⟩
        ⟨ps_g, body_g, cenv_g, h_eq_g, h_lk_g⟩)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact getElem?_some_lt_length h_cell_o
    · exact getElem?_some_lt_length h_cell_g }

end LeanBlack
