import LeanBlack.Bisim
import LeanBlack.Policies
import LeanBlack.ProofBased

/-!
# Compose — transitivity / composition of value bisimulation and CE

`ValVis_weak` transitivity across heap triples, then (eventually)
`CE_weak` transitivity, then the substrate-level claim: a chain of
`approvedPolicy`-admitted modifications yields a final apply value
that conservatively extends `bbApply`. This is the *global guarantee
across composed admissions* claimed by the LICS abstract.

This file (in progress): just the `ValVis_aux_weak` / `ValVis_weak`
transitivity foundation. `CE_weak_trans` and the substrate-level
theorem build on top.
-/

namespace LeanBlack

/-! ## ValVis_aux_weak transitivity

Proof by induction on the depth index `n`, case-analysis on the value
constructor of `v_a`, and using `ValVis_aux_weak`'s shape-discrimination
(non-matching constructor pairs reduce to `False`). -/

theorem ValVis_aux_weak_trans : ∀ (n : Nat) (v_a v_b v_c : Val) (h_a h_b h_c : Heap),
    ValVis_aux_weak n v_a v_b h_a h_b →
    ValVis_aux_weak n v_b v_c h_b h_c →
    ValVis_aux_weak n v_a v_c h_a h_c := by
  intro n
  induction n with
  | zero =>
      intro v_a v_b v_c h_a h_b h_c _ _
      simp [ValVis_aux_weak]
  | succ n ih =>
      intro v_a v_b v_c h_a h_b h_c h1 h2
      cases v_a <;> cases v_b <;> cases v_c <;>
        simp only [ValVis_aux_weak] at h1 h2 ⊢ <;>
        (try exact h1.elim) <;> (try exact h2.elim) <;>
        (first
          | (try subst h1; try subst h2; try rfl; try exact h2; try exact h1)
          | skip)
      all_goals (try trivial)
      all_goals (try (cases h1; cases h2; rfl))
      -- Remaining cases: .cons and .closure (the structural recursive cases).
      case cons.cons.cons x_a y_a x_b y_b x_c y_c =>
          obtain ⟨hx1, hy1⟩ := h1
          obtain ⟨hx2, hy2⟩ := h2
          exact ⟨ih _ _ _ h_a h_b h_c hx1 hx2, ih _ _ _ h_a h_b h_c hy1 hy2⟩
      case closure.closure.closure ps_a body_a cenv_a ps_b body_b cenv_b ps_c body_c cenv_c =>
          obtain ⟨hps1, hbody1, hcenv1⟩ := h1
          obtain ⟨hps2, hbody2, hcenv2⟩ := h2
          refine ⟨hps1.trans hps2, hbody1.trans hbody2, ?_⟩
          intro x
          have hx1 := hcenv1 x
          have hx2 := hcenv2 x
          -- Case-analyze on the three cenv lookups + heap reads.
          cases h_la : cenv_a.lookup x <;>
            cases h_lb : cenv_b.lookup x <;>
            cases h_lc : cenv_c.lookup x <;>
            simp [h_la, h_lb, h_lc] at hx1 hx2 ⊢
          all_goals (try exact hx1.elim)
          all_goals (try exact hx2.elim)
          -- Both lookups produce some i.
          rename_i i_a i_b i_c
          cases h_ha : h_a[i_a]? <;>
            cases h_hb : h_b[i_b]? <;>
            cases h_hc : h_c[i_c]? <;>
            simp [h_ha, h_hb, h_hc] at hx1 hx2 ⊢
          all_goals (try exact hx1.elim)
          all_goals (try exact hx2.elim)
          rename_i v_a v_b v_c
          exact ih _ _ _ h_a h_b h_c hx1 hx2

theorem ValVis_weak_trans
    {v_a v_b v_c : Val} {h_a h_b h_c : Heap}
    (h1 : ValVis_weak v_a v_b h_a h_b)
    (h2 : ValVis_weak v_b v_c h_b h_c) :
    ValVis_weak v_a v_c h_a h_c := by
  intro n
  exact ValVis_aux_weak_trans n v_a v_b v_c h_a h_b h_c (h1 n) (h2 n)

/-! ## CE_weak transitivity

If `v_a → v_b` is CE-weak and `v_b → v_c` is CE-weak (both at the same
`h_ref`), then `v_a → v_c` is CE-weak. Requires `ValValid v_b T.heap`
as an extra premise: the intermediate apply value must itself be valid
at the test state.

In practice, when chaining admissions, the intermediate `v_b` is the
`newVal` of a prior admission and hence valid at the post-admission
heap. -/

theorem CE_weak_trans
    {level : Nat} {h_ref : Heap} {v_a v_b v_c : Val}
    (h1 : CE_weak level h_ref v_a v_b)
    (h2 : CE_weak level h_ref v_b v_c) :
    ∀ (fuel : Nat) (ptable : PolicyTable) (op : Val) (operands : List Val)
      (T : TowerState) (r : Val) (T' : TowerState),
      h_ref.length ≤ T.heap.length →
      HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
      ValValid v_a T.heap → ValValid v_b T.heap → ValValid v_c T.heap →
      PolicyTableRespectsBisimT ptable →
      (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
      (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
      (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
      (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
      callAsBaseApply fuel ptable level v_a op operands T = some (r, T') →
      ∃ fuel' T'' r',
        callAsBaseApply fuel' ptable level v_c op operands T = some (r', T'') ∧
        ValVis_weak r r' T'.heap T''.heap ∧
        T'.policyAt? level = T''.policyAt? level ∧
        HeapValid T''.heap ∧
        T.heap.length ≤ T''.heap.length := by
  intro fuel ptable op operands T r T'
  intro h_len h_heap h_op h_operands h_va h_vb h_vc h_pt h_pol h_envs h_pols h_envvis h_call
  -- Step 1: apply h1 to get v_b's call from T succeeds.
  obtain ⟨fuel_b, T_b, r_b, h_call_b, h_vis_ab, h_pol_eq_ab, h_heap_b, h_len_b⟩ :=
    h1 fuel ptable op operands T r T'
        h_len h_heap h_op h_operands h_va h_vb h_pt h_pol h_envs h_pols h_envvis h_call
  -- Step 2: apply h2 to v_b's call.
  obtain ⟨fuel_c, T_c, r_c, h_call_c, h_vis_bc, h_pol_eq_bc, h_heap_c, h_len_c⟩ :=
    h2 fuel_b ptable op operands T r_b T_b
        h_len h_heap h_op h_operands h_vb h_vc h_pt h_pol h_envs h_pols h_envvis h_call_b
  -- Combine.
  refine ⟨fuel_c, T_c, r_c, h_call_c, ?_, ?_, h_heap_c, h_len_c⟩
  · exact ValVis_weak_trans h_vis_ab h_vis_bc
  · exact h_pol_eq_ab.trans h_pol_eq_bc

/-! ## CE_weak_strong transitivity

Analogous to `CE_weak_trans` but with the additional Deep + Shift
premises that `CE_weak_strong` carries. This is the form `Approval`'s
proof field uses, so this is the one that lifts to a chain of
admissions. -/

theorem CE_weak_strong_trans
    {level : Nat} {h_ref : Heap} {v_a v_b v_c : Val}
    (h1 : CE_weak_strong level h_ref v_a v_b)
    (h2 : CE_weak_strong level h_ref v_b v_c) :
    ∀ (fuel : Nat) (ptable : PolicyTable) (op : Val) (operands : List Val)
      (T : TowerState) (r : Val) (T' : TowerState),
      HeapPrefix h_ref T.heap →
      HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
      ValValid v_a T.heap → ValValid v_b T.heap → ValValid v_c T.heap →
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
      callAsBaseApply fuel ptable level v_a op operands T = some (r, T') →
      ∃ fuel' T'' r',
        callAsBaseApply fuel' ptable level v_c op operands T = some (r', T'') ∧
        ValVis_weak r r' T'.heap T''.heap ∧
        T'.policyAt? level = T''.policyAt? level ∧
        HeapValid T''.heap ∧
        T.heap.length ≤ T''.heap.length := by
  intro fuel ptable op operands T r T'
  intro h_prefix h_heap h_op h_operands h_va h_vb h_vc h_pt h_pol h_envs h_pols h_envvis
  intro h_heap_deep h_op_deep h_operands_deep h_levels_deep h_pt_shift h_pol_shift h_call
  obtain ⟨fuel_b, T_b, r_b, h_call_b, h_vis_ab, h_pol_eq_ab, h_heap_b, h_len_b⟩ :=
    h1 fuel ptable op operands T r T'
        h_prefix h_heap h_op h_operands h_va h_vb h_pt h_pol h_envs h_pols h_envvis
        h_heap_deep h_op_deep h_operands_deep h_levels_deep h_pt_shift h_pol_shift h_call
  obtain ⟨fuel_c, T_c, r_c, h_call_c, h_vis_bc, h_pol_eq_bc, h_heap_c, h_len_c⟩ :=
    h2 fuel_b ptable op operands T r_b T_b
        h_prefix h_heap h_op h_operands h_vb h_vc h_pt h_pol h_envs h_pols h_envvis
        h_heap_deep h_op_deep h_operands_deep h_levels_deep h_pt_shift h_pol_shift h_call_b
  refine ⟨fuel_c, T_c, r_c, h_call_c, ?_, ?_, h_heap_c, h_len_c⟩
  · exact ValVis_weak_trans h_vis_ab h_vis_bc
  · exact h_pol_eq_ab.trans h_pol_eq_bc

end LeanBlack
