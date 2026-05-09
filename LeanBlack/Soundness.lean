/-
  lean-black: Tower-level soundness theorem (statement scaffold).

  The headline theorem is the cross-level lift of:
  - lean-grey's `eval_tower_conservative` (which has the *shape* —
    quantifies over arbitrary depth, materialized lazily — but
    operates over an abstract `ApplyRule`),
  - and lean-green's `multnExact_soundForCE_first_install` (which
    has the *substance* — real heap, real `set!`, CakeML-style
    `ValVis` bisim — but is single-level).

  The synthesis: under `SafeEvolution` (every materialized level's
  policy is sound for CE-at-that-level, and every policy in the
  table is universally sound across all levels), evaluating any
  program preserves cross-level conservative extension across the
  entire tower AND preserves `SafeEvolution` post-eval.

  ## Status

  This file is a **scaffold**: the statement is in place, the body
  is `sorry`. Discharging it requires:
  - The full frame theorem (`Frame.lean` — currently 6 cases
    sorry'd).
  - The headline single-install soundness
    (`Policies.lean :: multnExact_soundForCE_first_install_tower`
    — currently sorry, depends on frame).
  - A coinductive (or maxDepth-bounded) lift of single-install
    soundness to the cross-level `TowerCE` predicate below.

  The architecture of the cross-level lift mirrors lean-grey's
  `eval_tower_conservative` proof, but instantiated against the
  real-heap operational semantics from lean-green rather than the
  abstract `ApplyRule` layer. This is precisely the synthesis
  promised by `DESIGN.md`.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Policies

/-! ## Cross-level conservative extension -/

/-- A policy is **universally sound** at level `level` if it admits
    only modifications that preserve CE-at-`level`, *for any
    starting state*. Mirrors lean-grey's `Policy.UnivSound`. -/
def BlackPolicy.UnivSoundAt (level : Nat) (p : BlackPolicy) : Prop :=
  p.SoundForCE level

/-- **Tower-level CE preservation** between two tower states. For
    every materialized level `n`, the level-`n` apply rule (= the
    value at `(T.envAt? (n+1)).lookup "base-apply"` projected
    through the heap, or `.builtinBaseApply` if absent) in `T'`
    conservatively extends the corresponding rule in `T`.

    The `h_ref` for the underlying CE is `T'.heap` (the post-state
    heap). This restricts test states to those extending `T'.heap`,
    which is what enables compositional CE-chaining: when composing
    `T → T_mid → T''`, intermediate values from `T_mid.heap` (which
    is a prefix of `T''.heap`) remain ValValid in any test state
    extending `T''.heap`. -/
def TowerCE (T T' : TowerState) : Prop :=
  ∀ (n : Nat),
    -- For each materialized level `n`, the apply value at level
    -- `n` in `T'` conservatively extends the apply value at level
    -- `n` in `T`. (Concretely: the value bound at the
    -- `base-apply` cell of level `(n+1)`'s env in `T`'s heap and
    -- in `T'`'s heap, related by `CE n`, with `h_ref := T'.heap`.)
    ∀ idx oldApply newApply,
      (T.envAt? (n + 1)).bind (·.lookup "base-apply") = some idx →
      T.heap[idx]? = some oldApply →
      T'.heap[idx]? = some newApply →
      CE n T'.heap oldApply newApply

/-- `TowerCE` is reflexive (every well-formed tower CE-extends itself).
    Uses `frame_tower`'s applyDirect clause with self-pair (T_a = T_b)
    to derive bisim, HeapValid preservation, and heap monotonicity for
    the `callAsBaseApply` post-state. The `.builtinBaseApply` case is
    fully proved; the non-builtin case (closures, atoms) is sorry'd
    because we'd need `ValValid oldApply T₀.heap` (oldApply is from T,
    test state is T₀ — which may differ).
    A complete proof would require either further CE preconditions
    (e.g., a `ValValid old T.heap` premise for the candidate base-apply
    value) or a more refined statement scoped to test states whose
    heaps extend T's. -/
theorem TowerCE.refl (T : TowerState)
    (hh : HeapValid T.heap)
    (h_levs : ∀ n env, T.envAt? n = some env → EnvValid env T.heap)
    (h_resp_all : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_bisim : ∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) :
    TowerCE T T := by
  intro n idx oldApply newApply h_lookup h_old h_new
  have h_eq : oldApply = newApply := by
    rw [h_old] at h_new; exact Option.some.inj h_new
  subst h_eq
  intro fuel ptable op operands T₀ r T₀' _h_ext hh_T₀ hv_op hv_args
        hv_oldApply hv_oldApply' h_pt
        h_pol_resp_T₀ h_levs_T₀ h_resp_all_T₀ h_bisim_T₀ h_call
  obtain ⟨_, _, _, h_apd⟩ := frame_tower fuel
  have h_vv_op_self : ValVis op op T₀.heap T₀.heap := by
    intro d
    have := ValVis_aux_self_extend d op T₀.heap [] hh_T₀ hv_op
    simpa using this
  have h_lvv_self : ListValVis operands operands T₀.heap T₀.heap := by
    clear h_call hh hv_op h_pol_resp_T₀ h_levs_T₀ h_resp_all_T₀
          h_bisim_T₀ h_pt h_lookup h_old h_new h_vv_op_self h_levs h_resp_all h_bisim
          hv_oldApply hv_oldApply'
    induction operands with
    | nil => trivial
    | cons head tail ih =>
        refine ⟨?_, ih hv_args.2⟩
        intro d
        have := ValVis_aux_self_extend d head T₀.heap [] hh_T₀ hv_args.1
        simpa using this
  unfold callAsBaseApply at h_call
  cases h_old_match : oldApply with
  | builtinBaseApply =>
      rw [h_old_match] at h_call
      simp only at h_call
      obtain ⟨r_b, T_b', h_call_b, h_vv_r, h_he, h_tc, _, _⟩ :=
        h_apd ptable n op op operands operands T₀ T₀ r T₀'
          h_pt h_pol_resp_T₀ rfl hh_T₀ hh_T₀ rfl
          h_levs_T₀ h_levs_T₀ (fun _ => rfl) (fun _ => rfl) h_resp_all_T₀
          h_bisim_T₀
          h_vv_op_self h_lvv_self
          hv_op hv_op hv_args hv_args h_call
      refine ⟨fuel, T_b', r_b, ?_, h_vv_r, h_tc.policy_eq_at, h_tc.hv_b_out, h_he.len_b⟩
      simp only [callAsBaseApply]; exact h_call_b
  | num _ | bool _ | nilV | sym _ | cons _ _ =>
      -- For non-applicable values, applyDirect returns none.
      -- callAsBaseApply unfolds to applyDirect ... oldApply [...] T₀,
      -- and applyDirect on these constructors returns none for any fuel.
      rw [h_old_match] at h_call
      simp only at h_call
      exfalso
      cases fuel with
      | zero => simp [applyDirect] at h_call
      | succ k => simp [applyDirect] at h_call
  | prim s =>
      -- .prim case: applyDirect dispatches via applyPrim. Self-bisim of
      -- .prim is trivial (atomic). Args are [op, listToVal operands].
      rw [h_old_match] at h_call
      simp only at h_call
      have h_vv_prim : ValVis (.prim s) (.prim s) T₀.heap T₀.heap := by
        intro d
        exact closedValB_ValVis_aux d (.prim s) T₀.heap T₀.heap rfl
      have h_lvv_disp : ListValVis [op, listToVal operands] [op, listToVal operands]
          T₀.heap T₀.heap :=
        ⟨h_vv_op_self, ValVis_listToVal h_lvv_self, trivial⟩
      have hv_disp : ListValValid [op, listToVal operands] T₀.heap :=
        ⟨hv_op, ValValid_listToVal hv_args, trivial⟩
      obtain ⟨r_b, T_b', h_call_b, h_vv_r, h_he, h_tc, _, _⟩ :=
        h_apd ptable n (.prim s) (.prim s)
          [op, listToVal operands] [op, listToVal operands]
          T₀ T₀ r T₀'
          h_pt h_pol_resp_T₀ rfl hh_T₀ hh_T₀ rfl
          h_levs_T₀ h_levs_T₀ (fun _ => rfl) (fun _ => rfl) h_resp_all_T₀
          h_bisim_T₀
          h_vv_prim h_lvv_disp
          trivial trivial hv_disp hv_disp h_call
      refine ⟨fuel, T_b', r_b, ?_, h_vv_r, h_tc.policy_eq_at, h_tc.hv_b_out, h_he.len_b⟩
      simp only [callAsBaseApply]; exact h_call_b
  | closure ps body cenv =>
      -- .closure case: now we have ValValid (.closure ps body cenv) T₀.heap
      -- (i.e., EnvValid cenv T₀.heap) from CE's hv_oldApply premise.
      rw [h_old_match] at h_call
      simp only at h_call
      have h_vv_cl : ValVis (.closure ps body cenv) (.closure ps body cenv)
          T₀.heap T₀.heap := by
        intro d
        have := ValVis_aux_self_extend d (.closure ps body cenv) T₀.heap []
          hh_T₀ (h_old_match ▸ hv_oldApply)
        simpa using this
      have h_lvv_disp : ListValVis [op, listToVal operands] [op, listToVal operands]
          T₀.heap T₀.heap :=
        ⟨h_vv_op_self, ValVis_listToVal h_lvv_self, trivial⟩
      have hv_disp : ListValValid [op, listToVal operands] T₀.heap :=
        ⟨hv_op, ValValid_listToVal hv_args, trivial⟩
      obtain ⟨r_b, T_b', h_call_b, h_vv_r, h_he, h_tc, _, _⟩ :=
        h_apd ptable n (.closure ps body cenv) (.closure ps body cenv)
          [op, listToVal operands] [op, listToVal operands]
          T₀ T₀ r T₀'
          h_pt h_pol_resp_T₀ rfl hh_T₀ hh_T₀ rfl
          h_levs_T₀ h_levs_T₀ (fun _ => rfl) (fun _ => rfl) h_resp_all_T₀
          h_bisim_T₀
          h_vv_cl h_lvv_disp
          (h_old_match ▸ hv_oldApply) (h_old_match ▸ hv_oldApply)
          hv_disp hv_disp h_call
      refine ⟨fuel, T_b', r_b, ?_, h_vv_r, h_tc.policy_eq_at, h_tc.hv_b_out, h_he.len_b⟩
      simp only [callAsBaseApply]; exact h_call_b

/-- `CE` is covariant in `h_ref` (a smaller `h_ref` gives a stronger CE
    that implies the CE for any larger `h_ref`). When `h₂` extends `h₁`,
    the test states extending `h₂` are a subset of those extending `h₁`,
    so `CE level h₁ old new` implies `CE level h₂ old new`. -/
private theorem CE_weaken_h_ref (level : Nat) (h₁ h₂ : Heap)
    (h_ext : ∃ extras, h₂ = h₁ ++ extras)
    (old new : Val) (h_ce : CE level h₁ old new) :
    CE level h₂ old new := by
  intro fuel ptable op operands T r T' h_ext_T hh hv_op hv_args
        hv_old hv_new h_pt h_pol_resp h_levs h_resp_all h_bisim h_call
  obtain ⟨e2, he2⟩ := h_ext
  obtain ⟨e1, he1⟩ := h_ext_T
  have h_ext_T_h₁ : ∃ extras, T.heap = h₁ ++ extras := by
    refine ⟨e2 ++ e1, ?_⟩
    rw [he1, he2, List.append_assoc]
  exact h_ce fuel ptable op operands T r T' h_ext_T_h₁ hh hv_op hv_args
        hv_old hv_new h_pt h_pol_resp h_levs h_resp_all h_bisim h_call

/-- If `T'` has the same heap as `T` (e.g., after `setPolicyAt`), then
    `TowerCE T T'` reduces to `TowerCE T T`. The heap-equality forces
    `oldApply = newApply` in TowerCE's premises, and the rest follows
    from self-CE. -/
private theorem TowerCE_of_heap_eq (T T' : TowerState)
    (h_heap_eq : T'.heap = T.heap)
    (h_self : TowerCE T T) :
    TowerCE T T' := by
  intro n idx oldApply newApply h_lookup h_old h_new
  have h_new_T : T.heap[idx]? = some newApply := h_heap_eq ▸ h_new
  -- h_self gives CE n T.heap; we need CE n T'.heap. Since heaps equal, rewrite.
  rw [h_heap_eq]
  exact h_self n idx oldApply newApply h_lookup h_old h_new_T

/-- More general than `TowerCE_of_heap_eq`: if `T'.heap` extends `T.heap`
    by appending cells (no mutation), then `TowerCE T T'` reduces to
    `TowerCE T T` plus a `CE_weaken_h_ref` lift. -/
private theorem TowerCE_of_heap_extends (T T' : TowerState)
    (h_ext : ∃ extras, T'.heap = T.heap ++ extras)
    (h_self : TowerCE T T) :
    TowerCE T T' := by
  intro n idx oldApply newApply h_lookup h_old h_new
  obtain ⟨extras, h_eq⟩ := h_ext
  have h_lt : idx < T.heap.length :=
    (List.getElem?_eq_some_iff.mp h_old).1
  have h_t' : T'.heap[idx]? = T.heap[idx]? := by
    rw [h_eq]; exact List.getElem?_append_left h_lt
  rw [h_t', h_old] at h_new
  have h_eq_app : oldApply = newApply := Option.some.inj h_new
  subst h_eq_app
  -- h_self gives CE n T.heap oldApply oldApply; we need CE n T'.heap.
  -- T'.heap extends T.heap by h_ext, so apply CE_weaken_h_ref.
  exact CE_weaken_h_ref n T.heap T'.heap ⟨extras, h_eq⟩ oldApply oldApply
    (h_self n idx oldApply oldApply h_lookup h_old h_old)

/-- An expression is *atomic* if its evaluation reduces to a result
    pair `(cv, T)` without mutating the tower state. The atomic
    constructors are: `.num`, `.bool`, `.lam`, `.var`, `.quote`. -/
def Expr.IsAtomic : Expr → Prop
  | .num _   => True
  | .bool _  => True
  | .lam _ _ => True
  | .var _   => True
  | .quote _ => True
  | _        => False

/-- For atomic expressions, `eval` doesn't change the tower state.
    A useful lemma for proving compound cases of `eval_tower_safe`
    where the first sub-eval is on an atomic expression. -/
private theorem eval_atomic_T_unchanged
    (k : Nat) (ptable : PolicyTable) (level : Nat) (c : Expr)
    (env : Env) (T : TowerState) (cv : Val) (T_mid : TowerState)
    (h_atomic : c.IsAtomic)
    (h_eval : eval k ptable level c env T = some (cv, T_mid)) :
    T_mid = T := by
  cases c with
  | num i =>
      cases k with
      | zero => simp [eval] at h_eval
      | succ j =>
          simp [eval] at h_eval
          exact h_eval.2.symm
  | bool b =>
      cases k with
      | zero => simp [eval] at h_eval
      | succ j =>
          simp [eval] at h_eval
          exact h_eval.2.symm
  | lam ps body =>
      cases k with
      | zero => simp [eval] at h_eval
      | succ j =>
          simp [eval] at h_eval
          exact h_eval.2.symm
  | var x =>
      cases k with
      | zero => simp [eval] at h_eval
      | succ j =>
          simp only [eval] at h_eval
          cases hx : env.lookup x with
          | none => rw [hx] at h_eval; simp at h_eval
          | some idx =>
              rw [hx] at h_eval
              simp only at h_eval
              cases hp : T.heap[idx]? with
              | none => rw [hp] at h_eval; simp at h_eval
              | some w =>
                  rw [hp] at h_eval
                  simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                  exact h_eval.2.symm
  | quote w =>
      cases k with
      | zero => simp [eval] at h_eval
      | succ j =>
          simp only [eval] at h_eval
          by_cases hc : closedValB w = true
          · simp only [hc, if_true, Option.some.injEq, Prod.mk.injEq] at h_eval
            exact h_eval.2.symm
          · simp only [hc, if_false] at h_eval
            simp at h_eval
  | ifte _ _ _ | app _ | set _ _ | em _
  | primApp _ _ | letE _ _ _ | seq _ | installPolicy _ =>
      simp [Expr.IsAtomic] at h_atomic

/-- **TowerCE composition (transitivity).** Given two-step CE chain
    `T → T_mid → T''` with appropriate monotonicity, derives
    `TowerCE T T''`. The strengthened CE (with `h_ref` premise) is
    what makes this work: a test state `T₀` extending `T''.heap`
    also extends `T_mid.heap` (by transitivity of heap-prefix), so
    intermediate values from `T_mid.heap` remain ValValid in
    `T₀.heap` — the precondition needed to invoke the second CE.

    Depends on `ValVis_trans` (currently sorry'd in `Bisim.lean`)
    for chaining the bisim conclusion of the two CE invocations.

    Preconditions:
    - `T_mid.heap` extends `T.heap` (no mutations in first sub-eval
      of base-apply cells)
    - `T''.heap` extends `T_mid.heap` (heap monotonicity)
    - per-level envs are stable across the first transition
    - `HeapValid T_mid.heap` (so intermediate values are ValValid)

    Note: this is the *general* composition lemma. For specific
    cases where one of the heaps is unchanged (e.g., `.installPolicy`),
    use `TowerCE_of_heap_eq` instead — it doesn't need ValVis_trans. -/
private theorem TowerCE_trans (T T_mid T'' : TowerState)
    (h_mono_12 : ∃ extras, T_mid.heap = T.heap ++ extras)
    (h_mono_23 : ∃ extras, T''.heap = T_mid.heap ++ extras)
    (h_env_eq_12 : ∀ n, T_mid.envAt? n = T.envAt? n)
    (h_hh_mid : HeapValid T_mid.heap)
    (h_hh_T'' : HeapValid T''.heap)
    (h12 : TowerCE T T_mid)
    (h23 : TowerCE T_mid T'') :
    TowerCE T T'' := by
  intro n idx oldApply newApply h_lookup h_old h_new
  -- Get mid = T_mid.heap[idx]?. Some by monotonicity.
  obtain ⟨extras12, h_eq_12⟩ := h_mono_12
  have h_lt : idx < T.heap.length := (List.getElem?_eq_some_iff.mp h_old).1
  have h_t_mid_idx : T_mid.heap[idx]? = T.heap[idx]? := by
    rw [h_eq_12]; exact List.getElem?_append_left h_lt
  have h_mid : T_mid.heap[idx]? = some oldApply := h_t_mid_idx.trans h_old
  -- Apply h12 at (n, idx, old, mid).
  obtain ⟨extras23, h_eq_23⟩ := h_mono_23
  -- TowerCE T T_mid uses T_mid.heap as h_ref. We have T_mid.heap[idx] = some oldApply
  -- (from h_mid). Apply h12 to get CE n T_mid.heap oldApply oldApply
  -- (since old = mid because heap is unchanged at this idx).
  have h_ce_12 : CE n T_mid.heap oldApply oldApply :=
    h12 n idx oldApply oldApply h_lookup h_old h_mid
  -- TowerCE T_mid T'' uses T''.heap as h_ref. Apply h23 at (n, idx, oldApply, newApply)
  -- with the env lookup lifted via h_env_eq_12.
  have h_lookup_mid : (T_mid.envAt? (n + 1)).bind (·.lookup "base-apply") = some idx := by
    rw [h_env_eq_12]; exact h_lookup
  have h_ce_23 : CE n T''.heap oldApply newApply :=
    h23 n idx oldApply newApply h_lookup_mid h_mid h_new
  -- Goal: CE n T''.heap oldApply newApply.
  -- We have h_ce_23 directly. Wait — but what about h_ce_12's contribution?
  -- If oldApply = newApply (no mutation), CE refl works. Otherwise, need
  -- ValVis_trans to chain through mid (= oldApply).
  -- For now, just use h_ce_23 (which directly answers the question).
  -- The composition only matters if mid ≠ old, in which case h_ce_12 gives
  -- CE old mid (which is the chain T → T_mid). That's needed to chain through
  -- if T''.heap[idx] differs from T.heap[idx] AND from T_mid.heap[idx].
  -- Since T_mid.heap[idx] = T.heap[idx] = oldApply (heap monotonicity preserved
  -- old), we just have CE n T''.heap oldApply newApply directly.
  exact h_ce_23

/-- If `T_mid` shares its heap and per-level envs with `T`, then
    `TowerCE T_mid T''` lifts to `TowerCE T T''`. Useful when a
    sub-eval doesn't change the tower (e.g., the condition of an
    `.ifte` is an atomic expression). -/
private theorem TowerCE_lift_source (T T_mid T'' : TowerState)
    (h_heap_eq : T_mid.heap = T.heap)
    (h_env_eq : ∀ n, T_mid.envAt? n = T.envAt? n)
    (h23 : TowerCE T_mid T'') :
    TowerCE T T'' := by
  intro n idx oldApply newApply h_lookup h_old h_new
  apply h23 n idx oldApply newApply
  · rw [h_env_eq]; exact h_lookup
  · rw [h_heap_eq]; exact h_old
  · exact h_new

/-! ## Safe evolution -/

/-- Every materialized level's policy is universally sound (at its
    own level), and every policy in the table is universally sound
    at every level. The latter is needed because `(installPolicy n)`
    can swap any table policy into any materialized level. -/
def SafeEvolution (ptable : PolicyTable) (T : TowerState) : Prop :=
  (∀ n p, T.policyAt? n = some p → p.UnivSoundAt n) ∧
  (∀ p, p ∈ ptable → ∀ level, p.UnivSoundAt level)

/-! ## The headline theorem (statement; body deferred) -/

/-- `eval` preserves the self-WFCtxT invariants (HeapValid, level-envs-valid,
    policies-resp-all, EnvVis self-self at all materialized levels), plus
    EnvValid of the active env and ValValid of the result. Derived from
    `frame_tower`'s eval clause with self-pair (T_a = T_b = T). -/
private theorem eval_preserves_self_invariants
    (fuel : Nat) (ptable : PolicyTable) (level : Nat) (exp : Expr)
    (env : Env) (T : TowerState) (v : Val) (T' : TowerState)
    (hh : HeapValid T.heap)
    (hev : EnvValid env T.heap)
    (h_levs : ∀ n e, T.envAt? n = some e → EnvValid e T.heap)
    (h_resp_all : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_pt : PolicyTableRespectsBisimT ptable)
    (h_pol_resp_at : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_env_self : EnvVis env env T.heap T.heap)
    (h_eval : eval fuel ptable level exp env T = some (v, T')) :
    HeapValid T'.heap ∧
    (∀ n e, T'.envAt? n = some e → EnvValid e T'.heap) ∧
    (∀ n p, T'.policyAt? n = some p → PolicyRespectsBisimT p) ∧
    (∀ n e, T'.envAt? n = some e → EnvVis e e T'.heap T'.heap) ∧
    EnvValid env T'.heap ∧
    ValValid v T'.heap := by
  obtain ⟨ih_eval, _, _, _⟩ := frame_tower fuel
  have h_ctx : WFCtxT env env T T level :=
    WFCtxT.refl env T level hh hev h_pol_resp_at h_levs h_resp_all
  obtain ⟨v_b, T_b', h_eval_b, _, h_ctx_out, _, _, hv_va, _⟩ :=
    ih_eval ptable level exp env env T T v T'
      h_pt h_ctx h_env_self h_eval
  -- eval is deterministic: v_b = v, T_b' = T'.
  have h_eq : (v, T') = (v_b, T_b') := by
    have : some (v, T') = some (v_b, T_b') := h_eval.symm.trans h_eval_b
    exact Option.some.inj this
  obtain ⟨h_v_eq, h_T_eq⟩ : v = v_b ∧ T' = T_b' := Prod.mk.inj h_eq
  subst h_v_eq; subst h_T_eq
  exact ⟨h_ctx_out.hv_a, h_ctx_out.level_envs_valid_a,
         h_ctx_out.policies_resp_all, h_ctx_out.heap_content_bisim_at_levels,
         h_ctx_out.ev_a, hv_va⟩

/-- **Tower safety**. Under `SafeEvolution`, evaluating any program
    — with `(em ...)`, `(set! base-apply ...)`, `(installPolicy n)`
    at any depth — preserves cross-level conservative extension
    across the entire materialized tower AND preserves
    `SafeEvolution` post-eval.

    This is the synthesis of:
    - lean-grey's `eval_tower_conservative` (the *shape*: full
      tower, governance-of-governance),
    - lean-green's `multnExact_soundForCE_first_install` (the
      *substance*: real heap, real `set!`, CakeML-style bisim).

    **Body deferred.** Discharging requires the full frame
    theorem (Frame.lean: 6 sorries) and the single-install
    soundness theorem (Policies.lean: 1 sorry). Once those are
    complete, the cross-level induction here is mechanical
    (mirrors lean-grey's proof structure). -/
theorem eval_tower_safe
    (ptable : PolicyTable) (fuel : Nat) (level : Nat)
    (exp : Expr) (env : Env) (T : TowerState)
    (hh : HeapValid T.heap)
    (hev : EnvValid env T.heap)
    (h_levs : ∀ n env, T.envAt? n = some env → EnvValid env T.heap)
    (h_resp_all : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_bisim : ∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap)
    (h_pt : PolicyTableRespectsBisimT ptable)
    (h_pol_resp_at : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_env_self : EnvVis env env T.heap T.heap)
    (h_safe : SafeEvolution ptable T)
    (v : Val) (T' : TowerState)
    (h_eval : eval fuel ptable level exp env T = some (v, T')) :
    TowerCE T T' ∧ SafeEvolution ptable T' := by
  -- Easy cases: where T' = T, both conjuncts follow trivially.
  -- Recursive cases (.seq/.ifte/.app/.primApp/.letE/.em): use the IH on
  -- fuel k via `induction fuel generalizing ...`. Note `level` is also
  -- generalized because `.em` changes it.
  -- Hard cases (.set, .em-with-fresh-policies, multi-step composition):
  -- require cross-level architecture arguments — see DUMP.md.
  induction fuel generalizing exp env T v T' level with
  | zero => simp [eval] at h_eval
  | succ k ih =>
      cases exp with
      | num i =>
          simp [eval] at h_eval
          obtain ⟨_, h_T⟩ := h_eval
          subst h_T
          exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
      | bool b =>
          simp [eval] at h_eval
          obtain ⟨_, h_T⟩ := h_eval
          subst h_T
          exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
      | lam ps body =>
          simp [eval] at h_eval
          obtain ⟨_, h_T⟩ := h_eval
          subst h_T
          exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
      | quote w =>
          simp only [eval] at h_eval
          split at h_eval
          · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_T⟩ := h_eval
            subst h_T
            exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
          · simp at h_eval
      | var x =>
          simp only [eval] at h_eval
          cases hx : env.lookup x with
          | none => rw [hx] at h_eval; simp at h_eval
          | some idx =>
              rw [hx] at h_eval
              simp only at h_eval
              cases hp : T.heap[idx]? with
              | none => rw [hp] at h_eval; simp at h_eval
              | some w =>
                  rw [hp] at h_eval
                  simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                  obtain ⟨_, h_T⟩ := h_eval
                  subst h_T
                  exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
      | installPolicy idx =>
          -- T' is either T (when ptable[idx]? = none) or
          -- T.setPolicyAt level newPolicy (heap unchanged).
          -- TowerCE: heap unchanged ⇒ reduces to self-CE via TowerCE.refl.
          -- SafeEvolution: the new policy comes from ptable, which by
          -- h_safe.2 is UnivSoundAt at every level (including `level`).
          simp only [eval] at h_eval
          cases h_pt_idx : ptable[idx]? with
          | none =>
              rw [h_pt_idx] at h_eval
              simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨_, h_T⟩ := h_eval
              subst h_T
              exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
          | some newPolicy =>
              rw [h_pt_idx] at h_eval
              simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨_, h_T⟩ := h_eval
              subst h_T
              have h_heap_eq : (T.setPolicyAt level newPolicy).heap = T.heap :=
                TowerState.setPolicyAt_heap T level newPolicy
              refine ⟨?_, ?_, h_safe.2⟩
              · exact TowerCE_of_heap_eq T (T.setPolicyAt level newPolicy)
                  h_heap_eq (TowerCE.refl T hh h_levs h_resp_all h_bisim)
              · -- ∀ n p, (T.setPolicyAt level newPolicy).policyAt? n
                --       = some p → p.UnivSoundAt n
                intro n p hp
                by_cases hnl : level = n
                · subst hnl
                  rw [TowerState.setPolicyAt_policyAt?_self] at hp
                  cases h_orig : T.policyAt? level with
                  | none => rw [h_orig] at hp; simp at hp
                  | some p_orig =>
                      rw [h_orig] at hp
                      simp only [Option.map_some, Option.some.injEq] at hp
                      have h_in : newPolicy ∈ ptable :=
                        List.mem_of_getElem? h_pt_idx
                      rw [← hp]
                      exact h_safe.2 newPolicy h_in level
                · rw [TowerState.setPolicyAt_policyAt?_other T level n newPolicy hnl]
                    at hp
                  exact h_safe.1 n p hp
      | app exps =>
          -- Empty `.app` returns `none` (contradiction); non-empty
          -- requires multi-step CE composition (architectural — DUMP).
          cases exps with
          | nil => simp [eval] at h_eval
          | cons _ _ =>
              -- Composition case — sorry.
              sorry
      | seq exps =>
          -- Three sub-cases: empty seq (T' = T trivially), singleton
          -- seq (delegates to inner eval — pure IH application), and
          -- multi-element seq (compositional — requires CE-chaining).
          cases exps with
          | nil =>
              simp [eval] at h_eval
              obtain ⟨_, h_T⟩ := h_eval
              subst h_T
              exact ⟨TowerCE.refl T hh h_levs h_resp_all h_bisim, h_safe⟩
          | cons e rest =>
              cases rest with
              | nil =>
                  -- exps = [e] — eval at fuel k delegates to inner.
                  simp only [eval] at h_eval
                  -- h_eval : eval k ptable level e env T = some (v, T')
                  apply ih <;> assumption
              | cons e' rest' =>
                  -- exps = e :: e' :: rest'.
                  -- Sub-case: e is atomic ⇒ eval e doesn't mutate (T_mid = T),
                  -- so we can apply IH to (.seq (e' :: rest')) at T directly.
                  -- For non-atomic e, composition required (deferred).
                  cases e with
                  | num _ | bool _ | lam _ _ | var _ | quote _ =>
                      simp only [eval] at h_eval
                      -- h_eval has structure: match (eval k ... e env T) with ...
                      cases h_e : eval k ptable level _ env T with
                      | none => rw [h_e] at h_eval; simp at h_eval
                      | some pr =>
                          rw [h_e] at h_eval
                          cases pr with
                          | mk _ T_mid =>
                              simp only at h_eval
                              have h_T_eq : T_mid = T :=
                                eval_atomic_T_unchanged k ptable level _ env T _
                                  T_mid (by simp [Expr.IsAtomic]) h_e
                              subst h_T_eq
                              apply ih <;> assumption
                  | _ =>
                      -- Non-atomic e: composition required (DUMP.md
                      -- "Architectural blocker").
                      sorry
      | ifte c t e =>
          -- For atomic conditions (.num/.bool/.lam/.quote/.var), eval c
          -- doesn't change T, so the branch eval handles everything via
          -- IH. For non-atomic c, composition is required (deferred).
          cases c with
          | num i =>
              simp only [eval] at h_eval
              -- h_eval reduces: eval k ... = some (v, T') for the t-branch.
              -- eval k ptable level (.num i) env T = some (.num i, T) when k > 0.
              cases k with
              | zero => simp [eval] at h_eval
              | succ j =>
                  simp only [eval] at h_eval
                  -- h_eval : eval (j+1) ... t env T = some (v, T') (true branch)
                  apply ih <;> assumption
          | bool b =>
              simp only [eval] at h_eval
              cases k with
              | zero => simp [eval] at h_eval
              | succ j =>
                  cases b with
                  | true =>
                      simp only [eval] at h_eval
                      apply ih <;> assumption
                  | false =>
                      simp only [eval] at h_eval
                      apply ih <;> assumption
          | lam ps body =>
              simp only [eval] at h_eval
              cases k with
              | zero => simp [eval] at h_eval
              | succ j =>
                  simp only [eval] at h_eval
                  -- closure is not .bool false, so falls to t-branch.
                  apply ih <;> assumption
          | var x =>
              cases k with
              | zero => simp [eval] at h_eval
              | succ j =>
                  simp only [eval] at h_eval
                  cases hx : env.lookup x with
                  | none =>
                      rw [hx] at h_eval; simp at h_eval
                  | some idx =>
                      rw [hx] at h_eval
                      simp only at h_eval
                      cases hp : T.heap[idx]? with
                      | none =>
                          rw [hp] at h_eval; simp at h_eval
                      | some w =>
                          rw [hp] at h_eval
                          simp only at h_eval
                          -- h_eval now matches on w: .bool false → e branch, else → t.
                          -- For all cases, the branch eval is at T (no mutation).
                          cases w with
                          | bool b =>
                              cases b with
                              | true => apply ih <;> assumption
                              | false => apply ih <;> assumption
                          | num _ | nilV | sym _ | cons _ _ | closure _ _ _
                          | prim _ | builtinBaseApply =>
                              apply ih <;> assumption
          | quote w =>
              cases k with
              | zero => simp [eval] at h_eval
              | succ j =>
                  simp only [eval] at h_eval
                  by_cases hc : closedValB w = true
                  · simp only [hc, if_true] at h_eval
                    cases w with
                    | bool b =>
                        cases b with
                        | true => apply ih <;> assumption
                        | false => apply ih <;> assumption
                    | num _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        apply ih <;> assumption
                  · simp only [hc, if_false] at h_eval
                    simp at h_eval
          | _ =>
              -- Recursive c (.ifte/.app/.primApp/.letE/.seq/.set/.em/.installPolicy):
              -- composition required (deferred — see DUMP.md
              -- "Architectural blocker").
              sorry
      | _ =>
          -- Remaining cases: app/primApp/letE (heap extended
          -- but base-apply cells unchanged → TowerCE preserved via
          -- length_mono), em (heap extended via materialize), set
          -- (heap mutated via gated update; SoundForCE → CE preserved).
          sorry

/-! ## Necessity

    The converse: without `SafeEvolution`, there exist programs that
    break cross-level CE. Concrete counterexample:

    Setup a minimal tower with level 0 (empty env) and level 1 binding
    `"base-apply"` to heap cell `0`, which holds `.builtinBaseApply`
    under `acceptAllPolicy`. Run `(set! base-apply (lam (op args) (app)))`
    at level 1 — `acceptAllPolicy` admits the mutation, replacing the
    apply with a *diverging* closure (body is the empty application,
    which evaluates to `none` at any fuel).

    For `TowerCE T T'` at `n = 0`: `T.heap[0] = .builtinBaseApply` admits
    `(.prim "+", [.num 1, .num 2])` returning `(.num 3)`; but every call
    through the new diverging closure returns `none`, so no `CE`
    witness exists.

    Mirrors lean-grey's `safeEvolution_necessary`. -/

private def cex_envL1 : Env := .cons "base-apply" 0 .nil

private def cex_lam : Expr := .lam ["op", "args"] (.app [])

private def cex_T : TowerState :=
  { heap := [.builtinBaseApply],
    levels := [
      { env := .nil, policy := acceptAllPolicy },
      { env := cex_envL1, policy := acceptAllPolicy }
    ] }

private def cex_div_closure : Val :=
  .closure ["op", "args"] (.app []) cex_envL1

private def cex_T' : TowerState := cex_T.updateHeap 0 cex_div_closure

private theorem cex_T_heapValid : HeapValid cex_T.heap := by
  intro i v hp
  match i, hp with
  | 0, h =>
      have : v = .builtinBaseApply := by simp [cex_T] at h; exact h.symm
      rw [this]; trivial
  | k + 1, h => simp [cex_T] at h

private theorem cex_T_envValid_at : ∀ n env,
    cex_T.envAt? n = some env → EnvValid env cex_T.heap := by
  intro n env hen
  match n, hen with
  | 0, h =>
      have : env = .nil := by
        simp [cex_T, TowerState.envAt?, TowerState.levelAt?] at h; exact h.symm
      rw [this]
      intro x i hx; simp [Env.lookup] at hx
  | 1, h =>
      have h_env : env = cex_envL1 := by
        simp [cex_T, TowerState.envAt?, TowerState.levelAt?] at h; exact h.symm
      rw [h_env]
      intro x i hx
      simp [cex_envL1, Env.lookup] at hx
      -- hx : "base-apply" = x ∧ 0 = i
      rw [← hx.2]; simp [cex_T]
  | n + 2, h => simp [cex_T, TowerState.envAt?, TowerState.levelAt?] at h

private theorem cex_T_policyResp_all : ∀ n p,
    cex_T.policyAt? n = some p → PolicyRespectsBisimT p := by
  intro n p hp
  match n, hp with
  | 0, h =>
      have : p = acceptAllPolicy := by
        simp [cex_T, TowerState.policyAt?, TowerState.levelAt?] at h; exact h.symm
      rw [this]; exact acceptAllPolicy_respects_bisimT
  | 1, h =>
      have : p = acceptAllPolicy := by
        simp [cex_T, TowerState.policyAt?, TowerState.levelAt?] at h; exact h.symm
      rw [this]; exact acceptAllPolicy_respects_bisimT
  | n + 2, h => simp [cex_T, TowerState.policyAt?, TowerState.levelAt?] at h

private theorem cex_T_bisim_self : ∀ n env,
    cex_T.envAt? n = some env → EnvVis env env cex_T.heap cex_T.heap := by
  intro n env hen
  exact EnvVis_self_of_valid env cex_T.heap (cex_T_envValid_at n env hen) cex_T_heapValid

/-! cex_T'-side helpers: the strengthened CE requires the test state's
    heap to extend `cex_T'.heap`. Using `cex_T'` as the test state
    trivially satisfies this. The post-set heap holds `cex_div_closure`
    at idx 0; we need ValValidity in `cex_T'.heap` instead of `cex_T.heap`. -/

private theorem cex_T'_envValid_cex_envL1 : EnvValid cex_envL1 cex_T'.heap := by
  intro x i hx
  simp [cex_envL1, Env.lookup] at hx
  -- hx : "base-apply" = x ∧ 0 = i
  rw [← hx.2]
  simp [cex_T', cex_T, TowerState.updateHeap, Heap.update]

private theorem cex_T'_heapValid : HeapValid cex_T'.heap := by
  intro i v hp
  match i, hp with
  | 0, h =>
      have : v = cex_div_closure := by
        simp [cex_T', cex_T, TowerState.updateHeap, Heap.update] at h
        exact h.symm
      rw [this]
      -- ValValid cex_div_closure cex_T'.heap = EnvValid cex_envL1 cex_T'.heap
      exact cex_T'_envValid_cex_envL1
  | k + 1, h => simp [cex_T', cex_T, TowerState.updateHeap, Heap.update] at h

private theorem cex_T'_envAt_eq : ∀ n, cex_T'.envAt? n = cex_T.envAt? n := by
  intro n; rfl

private theorem cex_T'_policyAt_eq : ∀ n, cex_T'.policyAt? n = cex_T.policyAt? n := by
  intro n; rfl

private theorem cex_T'_envValid_at : ∀ n env,
    cex_T'.envAt? n = some env → EnvValid env cex_T'.heap := by
  intro n env hen
  rw [cex_T'_envAt_eq] at hen
  -- For n = 1, env = cex_envL1.
  match n, hen with
  | 0, h =>
      have : env = .nil := by
        simp [cex_T, TowerState.envAt?, TowerState.levelAt?] at h; exact h.symm
      rw [this]
      intro x i hx; simp [Env.lookup] at hx
  | 1, h =>
      have h_env : env = cex_envL1 := by
        simp [cex_T, TowerState.envAt?, TowerState.levelAt?] at h; exact h.symm
      rw [h_env]
      exact cex_T'_envValid_cex_envL1
  | n + 2, h => simp [cex_T, TowerState.envAt?, TowerState.levelAt?] at h

private theorem cex_T'_policyResp_all : ∀ n p,
    cex_T'.policyAt? n = some p → PolicyRespectsBisimT p := by
  intro n p hp
  rw [cex_T'_policyAt_eq] at hp
  exact cex_T_policyResp_all n p hp

private theorem cex_T'_bisim_self : ∀ n env,
    cex_T'.envAt? n = some env → EnvVis env env cex_T'.heap cex_T'.heap := by
  intro n env hen
  exact EnvVis_self_of_valid env cex_T'.heap (cex_T'_envValid_at n env hen) cex_T'_heapValid

theorem safeEvolution_necessary :
    ∃ (ptable : PolicyTable) (fuel : Nat) (level : Nat) (exp : Expr)
      (env : Env) (T : TowerState) (v : Val) (T' : TowerState),
    eval fuel ptable level exp env T = some (v, T') ∧
    ¬ TowerCE T T' := by
  refine ⟨[], 100, 1, .set "base-apply" cex_lam, cex_envL1, cex_T, .bool true,
          cex_T', ?_, ?_⟩
  · -- eval at level 1 of (set! base-apply <lam>) succeeds via acceptAllPolicy.
    show eval 100 [] 1 (.set "base-apply" cex_lam) cex_envL1 cex_T
       = some (.bool true, cex_T')
    simp [eval, cex_lam, cex_envL1, cex_T, cex_T', cex_div_closure,
          isMetaMutation, acceptAllPolicy, TowerState.envAt?,
          TowerState.policyAt?, TowerState.levelAt?, Env.lookup,
          TowerState.updateHeap, Heap.update]
  · -- ¬ TowerCE cex_T cex_T'
    intro h_tce
    have h_lookup :
        (cex_T.envAt? 1).bind (·.lookup "base-apply") = some 0 := rfl
    have h_old : cex_T.heap[0]? = some .builtinBaseApply := rfl
    have h_new : cex_T'.heap[0]? = some cex_div_closure := rfl
    -- With strengthened CE, h_tce gives CE 0 cex_T'.heap (h_ref is post-state).
    have h_ce : CE 0 cex_T'.heap .builtinBaseApply cex_div_closure :=
      h_tce 0 0 .builtinBaseApply cex_div_closure h_lookup h_old h_new
    -- The premise: builtinBaseApply admits (+ 1 2) → (.num 3) at cex_T'.
    have h_witness :
        callAsBaseApply 10 [] 0 .builtinBaseApply (.prim "+")
          [.num 1, .num 2] cex_T' = some (.num 3, cex_T') := by
      simp [callAsBaseApply, applyDirect, applyPrim, applyPrim_plus]
    have h_pol_resp : ∀ p, cex_T'.policyAt? 0 = some p → PolicyRespectsBisimT p :=
      cex_T'_policyResp_all 0
    have h_pt_empty : PolicyTableRespectsBisimT [] := by intro idx p hp; simp at hp
    have hv_old_cex : ValValid Val.builtinBaseApply cex_T'.heap := trivial
    have hv_new_cex : ValValid cex_div_closure cex_T'.heap :=
      cex_T'_envValid_cex_envL1
    -- Test state extends cex_T'.heap trivially (use cex_T' itself).
    have h_ext : ∃ extras, cex_T'.heap = cex_T'.heap ++ extras := ⟨[], by simp⟩
    obtain ⟨fuel', T'', r', h_call, _⟩ :=
      h_ce 10 [] (.prim "+") [.num 1, .num 2] cex_T' (.num 3) cex_T'
        h_ext
        cex_T'_heapValid trivial ⟨trivial, trivial, trivial⟩
        hv_old_cex hv_new_cex
        h_pt_empty h_pol_resp cex_T'_envValid_at cex_T'_policyResp_all
        cex_T'_bisim_self
        h_witness
    -- Every call through cex_div_closure diverges (body = (.app [])).
    have h_div : ∀ f, callAsBaseApply f [] 0 cex_div_closure (.prim "+")
        [.num 1, .num 2] cex_T' = none := by
      intro f
      match f with
      | 0 =>
          simp [callAsBaseApply, applyDirect, cex_div_closure]
      | 1 =>
          simp [callAsBaseApply, applyDirect, cex_div_closure, allocStep, eval]
      | k + 2 =>
          simp [callAsBaseApply, applyDirect, cex_div_closure, allocStep, eval]
    rw [h_div fuel'] at h_call
    exact Option.noConfusion h_call
