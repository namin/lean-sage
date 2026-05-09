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
    conservatively extends the corresponding rule in `T`. -/
def TowerCE (T T' : TowerState) : Prop :=
  ∀ (n : Nat),
    -- For each materialized level `n`, the apply value at level
    -- `n` in `T'` conservatively extends the apply value at level
    -- `n` in `T`. (Concretely: the value bound at the
    -- `base-apply` cell of level `(n+1)`'s env in `T`'s heap and
    -- in `T'`'s heap, related by `CE n`.)
    ∀ idx oldApply newApply,
      (T.envAt? (n + 1)).bind (·.lookup "base-apply") = some idx →
      T.heap[idx]? = some oldApply →
      T'.heap[idx]? = some newApply →
      CE n oldApply newApply

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
  intro fuel ptable op operands T₀ r T₀' hh_T₀ hv_op hv_args
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
  -- Hard cases (.set/.installPolicy/recursive): require cross-level induction
  -- + per-case SoundForCE arguments. See DUMP.md for the full strategy.
  cases fuel with
  | zero => simp [eval] at h_eval
  | succ k =>
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
      | _ =>
          -- All other cases: lam (T' = T), var (T' = T), quote (T' = T),
          -- ifte/app/seq/primApp/letE (heap extended but base-apply
          -- cells unchanged → TowerCE preserved via length_mono),
          -- em (heap extended via materialize), set (heap mutated via
          -- gated update; SoundForCE → CE preserved), installPolicy
          -- (policy at level changed to ptable policy; UnivSoundAt by
          -- SafeEvolution).
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
    have h_ce : CE 0 .builtinBaseApply cex_div_closure :=
      h_tce 0 0 .builtinBaseApply cex_div_closure h_lookup h_old h_new
    -- The premise: builtinBaseApply admits (+ 1 2) → (.num 3).
    have h_witness :
        callAsBaseApply 10 [] 0 .builtinBaseApply (.prim "+")
          [.num 1, .num 2] cex_T = some (.num 3, cex_T) := by
      simp [callAsBaseApply, applyDirect, applyPrim, applyPrim_plus]
    have h_pol_resp : ∀ p, cex_T.policyAt? 0 = some p → PolicyRespectsBisimT p :=
      cex_T_policyResp_all 0
    have h_pt_empty : PolicyTableRespectsBisimT [] := by intro idx p hp; simp at hp
    have hv_old_cex : ValValid Val.builtinBaseApply cex_T.heap := trivial
    have hv_new_cex : ValValid cex_div_closure cex_T.heap := by
      show EnvValid cex_envL1 cex_T.heap
      exact cex_T_envValid_at 1 cex_envL1 rfl
    obtain ⟨fuel', T'', r', h_call, _⟩ :=
      h_ce 10 [] (.prim "+") [.num 1, .num 2] cex_T (.num 3) cex_T
        cex_T_heapValid trivial ⟨trivial, trivial, trivial⟩
        hv_old_cex hv_new_cex
        h_pt_empty h_pol_resp cex_T_envValid_at cex_T_policyResp_all cex_T_bisim_self
        h_witness
    -- Every call through cex_div_closure diverges (body = (.app [])).
    have h_div : ∀ f, callAsBaseApply f [] 0 cex_div_closure (.prim "+")
        [.num 1, .num 2] cex_T = none := by
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
