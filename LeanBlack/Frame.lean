/-
  lean-black: Frame theorem (tower-aware).

  Adapts lean-green's `frame` to the tower model. Shape changes:

  - **No `metaEnv` parameter.** In lean-green's stage-1 model, every
    eval call carried `metaEnv` (the env containing `base-apply`),
    threaded as an independent parameter. In the tower model,
    metaEnv at level N *is* `T.envAt? (level + 1)` — derived from
    the tower, not an independent parameter.
  - **New `level : Nat` parameter.** WFCtx and FrameStmt are
    parameterized by the level at which the eval is happening.
  - **`StateExt`-like component changes.** Cross-side policy
    equality is at *the current level*: `T_a.policyAt? level =
    T_b.policyAt? level`. The lean-green shimmed `StateExt` (level-0
    policy equality) is too weak.

  This file defines the new `WFCtxT` / `FrameStmtT` and states the
  `frame_tower` theorem. **The case proofs are deferred** —
  porting them is genuine engineering (~1500-2000 LOC adapted from
  lean-green's `frame`):

  - Mechanical cases (`.num`, `.bool`, `.lam`, `.var`, `.ifte`,
    `.app`, `.primApp`, `.letE`, `.seq`) port nearly verbatim,
    threading `level` through inner IH calls. A few are proved
    here as templates.
  - **`.em`** is genuinely new logic: the level shifts. We need a
    bisim-preserving materialization lemma (`Tower.materialize`
    extends both sides equivalently).
  - **`.set`** uses `T.policyAt? level` for the gate; the cross-
    side argument needs `policies_eq_at_level`.
  - **`.installPolicy`** mutates `T.policyAt? level`; both sides
    get the same new policy at the same level.
  - **`applyVia`** dispatches through `T.envAt? (level + 1)`
    instead of an independent metaEnv. The level-(level+1) env
    needs to be bisim-related cross-side.

  The remaining case proofs are the work of follow-up sessions.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim

/-! ## Tower-aware framing context -/

/-- A policy **respects bisim**: same-level cross-side, the policy
    gives the same admit/reject decision on bisim-related arguments
    in bisim-related heaps.

    Identical to lean-green's `PolicyRespectsBisim`. The new
    `MutationCtx.level` field is part of the policy's input but the
    policy is asked to make the *same* decision regardless of which
    side it's evaluated on (the level is constant cross-side at any
    moment of evaluation). -/
def PolicyRespectsBisimT (p : BlackPolicy) : Prop :=
  ∀ (target : String) (idx : Nat) (level : Nat) (env metaEnv : Env)
    (heap_a heap_b : Heap) (oldVal_a oldVal_b new_a new_b : Val),
    HeapValid heap_a → HeapValid heap_b →
    EnvValid env heap_a → EnvValid env heap_b →
    EnvValid metaEnv heap_a → EnvValid metaEnv heap_b →
    ValValid oldVal_a heap_a → ValValid oldVal_b heap_b →
    ValValid new_a heap_a → ValValid new_b heap_b →
    EnvVis env env heap_a heap_b →
    EnvVis metaEnv metaEnv heap_a heap_b →
    ValVis oldVal_a oldVal_b heap_a heap_b →
    ValVis new_a new_b heap_a heap_b →
    p { target := target, heap := heap_a, env := env,
        metaEnv := metaEnv, index := idx, level := level } oldVal_a new_a =
    p { target := target, heap := heap_b, env := env,
        metaEnv := metaEnv, index := idx, level := level } oldVal_b new_b

def PolicyTableRespectsBisimT (ptable : PolicyTable) : Prop :=
  ∀ (idx : Nat) p, ptable[idx]? = some p → PolicyRespectsBisimT p

/-- Tower well-formedness at a specific level. -/
structure WFCtxT (env_a env_b : Env) (T_a T_b : TowerState) (level : Nat)
    : Prop where
  /-- Cross-side: policy at the active level matches. The lean-green
      `StateExt` was global policy equality; in the tower this is
      per-level. -/
  policy_eq_at : T_a.policyAt? level = T_b.policyAt? level
  hv_a         : HeapValid T_a.heap
  hv_b         : HeapValid T_b.heap
  ev_a         : EnvValid env_a T_a.heap
  ev_b         : EnvValid env_b T_b.heap
  /-- The active policy respects bisim. -/
  policy_resp  : ∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p
  env_eq       : env_a = env_b
  heap_len_eq  : T_a.heap.length = T_b.heap.length
  /-- All materialized levels' envs are valid in both heaps. -/
  level_envs_valid_a : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap
  level_envs_valid_b : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap

theorem WFCtxT.refl (env : Env) (T : TowerState) (level : Nat)
    (hh : HeapValid T.heap) (hev : EnvValid env T.heap)
    (hresp : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_levels : ∀ n env, T.envAt? n = some env → EnvValid env T.heap) :
    WFCtxT env env T T level :=
  ⟨rfl, hh, hh, hev, hev, hresp, rfl, rfl, h_levels, h_levels⟩

/-! ## Tower-cross invariants

    `HeapEvolution` (from lean-green's Bisim) carries cross-side
    bisim preservation and per-side heap monotonicity, but doesn't
    carry the *cross-side* invariants that `WFCtxT` needs at the
    output state of an applyVia / applyDirect call (specifically:
    cross-side heap-length equality and cross-side policy-at-level
    equality, plus single-side level-envs monotonicity).

    `TowerCross` bundles those four facts so that `applyVia` /
    `applyDirect` can return them as an extra output component, and
    the `.app` / `.primApp` cases of the framing theorem can
    reconstruct a full `WFCtxT` for the post-call state. -/
structure TowerCross (level : Nat) (T_a T_b T_a' T_b' : TowerState) : Prop where
  heap_len_eq           : T_a'.heap.length = T_b'.heap.length
  policy_eq_at          : T_a'.policyAt? level = T_b'.policyAt? level
  levels_mono_a         : ∀ n env, T_a.envAt? n = some env → T_a'.envAt? n = some env
  levels_mono_b         : ∀ n env, T_b.envAt? n = some env → T_b'.envAt? n = some env
  hv_a_out              : HeapValid T_a'.heap
  hv_b_out              : HeapValid T_b'.heap
  level_envs_valid_a_out : ∀ n env, T_a'.envAt? n = some env → EnvValid env T_a'.heap
  level_envs_valid_b_out : ∀ n env, T_b'.envAt? n = some env → EnvValid env T_b'.heap
  policy_resp_out       : ∀ p, T_a'.policyAt? level = some p → PolicyRespectsBisimT p

theorem TowerCross.refl (level : Nat) (T_a T_b : TowerState)
    (h_len : T_a.heap.length = T_b.heap.length)
    (h_pol : T_a.policyAt? level = T_b.policyAt? level)
    (h_hv_a : HeapValid T_a.heap) (h_hv_b : HeapValid T_b.heap)
    (h_levs_a : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap)
    (h_levs_b : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap)
    (h_resp_at : ∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p) :
    TowerCross level T_a T_b T_a T_b :=
  ⟨h_len, h_pol, fun _ _ h => h, fun _ _ h => h,
   h_hv_a, h_hv_b, h_levs_a, h_levs_b, h_resp_at⟩

/-! ## The framing statement (joint, mutual) -/

private def FrameStmtT (n : Nat) : Prop :=
  -- eval
  (∀ (ptable : PolicyTable) (level : Nat) (exp : Expr) (env_a env_b : Env)
     (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    WFCtxT env_a env_b T_a T_b level →
    EnvVis env_a env_b T_a.heap T_b.heap →
    eval n ptable level exp env_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      eval n ptable level exp env_b T_b = some (r_b, T_b') ∧
      ValVis r_a r_b T_a'.heap T_b'.heap ∧
      WFCtxT env_a env_b T_a' T_b' level ∧
      HeapEvolution T_a T_b T_a' T_b' ∧
      EnvVis env_a env_b T_a'.heap T_b'.heap ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap) ∧
  -- evalList
  (∀ (ptable : PolicyTable) (level : Nat) (exps : List Expr)
     (env_a env_b : Env) (T_a T_b : TowerState)
     (rs_a : List Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    WFCtxT env_a env_b T_a T_b level →
    EnvVis env_a env_b T_a.heap T_b.heap →
    evalList n ptable level exps env_a T_a = some (rs_a, T_a') →
    ∃ rs_b T_b',
      evalList n ptable level exps env_b T_b = some (rs_b, T_b') ∧
      ListValVis rs_a rs_b T_a'.heap T_b'.heap ∧
      WFCtxT env_a env_b T_a' T_b' level ∧
      HeapEvolution T_a T_b T_a' T_b' ∧
      EnvVis env_a env_b T_a'.heap T_b'.heap ∧
      ListValValid rs_a T_a'.heap ∧ ListValValid rs_b T_b'.heap) ∧
  -- applyVia
  (∀ (ptable : PolicyTable) (level : Nat) (op_a op_b : Val)
     (args_a args_b : List Val) (T_a T_b : TowerState)
     (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    -- For applyVia we use a "self" WFCtx: env_a = env_b = some sentinel.
    -- The actual env arguments to applyVia are op/args, not an env.
    -- We carry T_a/T_b validity via h_T_wf.
    (∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p) →
    T_a.policyAt? level = T_b.policyAt? level →
    HeapValid T_a.heap → HeapValid T_b.heap →
    T_a.heap.length = T_b.heap.length →
    (∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap) →
    (∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap) →
    ValVis op_a op_b T_a.heap T_b.heap →
    ListValVis args_a args_b T_a.heap T_b.heap →
    ValValid op_a T_a.heap → ValValid op_b T_b.heap →
    ListValValid args_a T_a.heap → ListValValid args_b T_b.heap →
    applyVia n ptable level op_a args_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      applyVia n ptable level op_b args_b T_b = some (r_b, T_b') ∧
      ValVis r_a r_b T_a'.heap T_b'.heap ∧
      HeapEvolution T_a T_b T_a' T_b' ∧
      TowerCross level T_a T_b T_a' T_b' ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap) ∧
  -- applyDirect
  (∀ (ptable : PolicyTable) (level : Nat) (op_a op_b : Val)
     (args_a args_b : List Val) (T_a T_b : TowerState)
     (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    (∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p) →
    T_a.policyAt? level = T_b.policyAt? level →
    HeapValid T_a.heap → HeapValid T_b.heap →
    T_a.heap.length = T_b.heap.length →
    (∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap) →
    (∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap) →
    ValVis op_a op_b T_a.heap T_b.heap →
    ListValVis args_a args_b T_a.heap T_b.heap →
    ValValid op_a T_a.heap → ValValid op_b T_b.heap →
    ListValValid args_a T_a.heap → ListValValid args_b T_b.heap →
    applyDirect n ptable level op_a args_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      applyDirect n ptable level op_b args_b T_b = some (r_b, T_b') ∧
      ValVis r_a r_b T_a'.heap T_b'.heap ∧
      HeapEvolution T_a T_b T_a' T_b' ∧
      TowerCross level T_a T_b T_a' T_b' ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap)

/-! ## The headline theorem (zero case + literal cases proved;
    everything else `sorry`'d as a stub for follow-up sessions) -/

theorem frame_tower : ∀ n, FrameStmtT n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ _ _ _ _ h; simp [eval] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalList] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h
  | succ k ih =>
      obtain ⟨ih_eval, ih_evalList, ih_applyVia, ih_applyDirect⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- eval (k+1)
        intro ptable level exp env_a env_b T_a T_b r_a T_a'
              hresp_pt h_ctx h_env h_eval
        cases exp with
        | num i =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_T⟩ := h_eval
            subst h_r; subst h_T
            refine ⟨.num i, T_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, trivial, trivial⟩
            · simp [eval]
            · intro depth
              cases depth with | zero => trivial | succ _ => rfl
        | bool b =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_T⟩ := h_eval
            subst h_r; subst h_T
            refine ⟨.bool b, T_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, trivial, trivial⟩
            · simp [eval]
            · intro depth
              cases depth with | zero => trivial | succ _ => rfl
        | lam ps body =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_T⟩ := h_eval
            subst h_r; subst h_T
            refine ⟨.closure ps body env_b, T_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, h_ctx.ev_a, h_ctx.ev_b⟩
            · simp [eval]
            · intro depth
              cases depth with
              | zero => trivial
              | succ k' =>
                  refine ⟨rfl, rfl, h_ctx.env_eq, ?_⟩
                  exact h_env k'
        | quote v =>
            -- Same shape as lean-green: closedValB v restricts the value
            -- so it self-bisims across any heap pair.
            simp only [eval] at h_eval
            split at h_eval
            · rename_i h_closed
              simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨h_r, h_T⟩ := h_eval
              subst h_r; subst h_T
              refine ⟨v, T_b, ?_, ?_, h_ctx,
                      HeapEvolution.refl _ _, h_env,
                      closedValB_ValValid v T_a.heap h_closed,
                      closedValB_ValValid v T_b.heap h_closed⟩
              · simp [eval, h_closed]
              · intro depth
                exact closedValB_ValVis_aux depth v T_a.heap T_b.heap h_closed
            · simp at h_eval
        | var x =>
            -- Mechanical port of lean-green's `.var` case. The
            -- value is looked up in env (same idx cross-side via
            -- env_eq) then in the heap (same value cross-side via
            -- h_env at depth 1).
            simp only [eval] at h_eval
            cases hl_a : env_a.lookup x with
            | none => rw [hl_a] at h_eval; simp at h_eval
            | some i_a =>
                rw [hl_a] at h_eval
                simp only at h_eval
                cases hp_a : T_a.heap[i_a]? with
                | none => rw [hp_a] at h_eval; simp at h_eval
                | some v_a =>
                    rw [hp_a] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨h_r, h_T⟩ := h_eval
                    subst h_r; subst h_T
                    have h_x1 := h_env 1 x
                    rw [hl_a] at h_x1
                    cases hl_b : env_b.lookup x with
                    | none =>
                        rw [hl_b] at h_x1; simp only [EnvVis_aux] at h_x1
                    | some i_b =>
                        rw [hl_b] at h_x1
                        simp only at h_x1
                        rw [hp_a] at h_x1
                        cases hp_b : T_b.heap[i_b]? with
                        | none =>
                            rw [hp_b] at h_x1; simp only at h_x1
                        | some v_b =>
                            refine ⟨v_b, T_b, ?_, ?_, h_ctx,
                                    HeapEvolution.refl _ _, h_env,
                                    h_ctx.hv_a i_a v_a hp_a,
                                    h_ctx.hv_b i_b v_b hp_b⟩
                            · simp [eval, hl_b, hp_b]
                            · intro depth
                              have h_x_d := h_env depth x
                              rw [hl_a, hl_b] at h_x_d
                              simp only at h_x_d
                              rw [hp_a, hp_b] at h_x_d
                              exact h_x_d
        | ifte c t e =>
            -- Mechanical port. Key trick: ValVis_bool_false_iff
            -- means cv_a = .bool false ↔ cv_b = .bool false, so
            -- both sides take the same branch.
            simp only [eval] at h_eval
            cases hc : eval k ptable level c env_a T_a with
            | none => rw [hc] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨cv_a, T_c_a⟩ := pr
                rw [hc] at h_eval
                obtain ⟨cv_b, T_c_b, h_eval_c_b, h_vv_c, h_ctx_c, h_he_c,
                        h_env_c, _hv_cva, _hv_cvb⟩ :=
                  ih_eval ptable level c env_a env_b T_a T_b cv_a T_c_a
                    hresp_pt h_ctx h_env hc
                have h_iff : cv_a = .bool false ↔ cv_b = .bool false :=
                  ValVis_bool_false_iff cv_a cv_b T_c_a.heap T_c_b.heap h_vv_c
                by_cases hcv : cv_a = .bool false
                · -- both sides take else-branch
                  have h_cv_b : cv_b = .bool false := h_iff.mp hcv
                  subst hcv
                  simp only at h_eval
                  obtain ⟨r_b, T_b', h_eval_e_b, h_vv, h_ctx', h_he',
                          h_env', hv_ra, hv_rb⟩ :=
                    ih_eval ptable level e env_a env_b T_c_a T_c_b r_a T_a'
                      hresp_pt h_ctx_c h_env_c h_eval
                  refine ⟨r_b, T_b', ?_, h_vv, h_ctx',
                          HeapEvolution.trans h_he_c h_he',
                          h_env', hv_ra, hv_rb⟩
                  simp [eval, h_eval_c_b, h_cv_b, h_eval_e_b]
                · -- both sides take then-branch
                  have h_cv_b_ne : cv_b ≠ .bool false := fun h => hcv (h_iff.mpr h)
                  have h_eval_t : eval k ptable level t env_a T_c_a = some (r_a, T_a') := by
                    cases cv_a with
                    | bool b =>
                        cases b with
                        | false => exact absurd rfl hcv
                        | true  => exact h_eval
                    | num _            => exact h_eval
                    | nilV             => exact h_eval
                    | cons _ _         => exact h_eval
                    | sym _            => exact h_eval
                    | closure _ _ _    => exact h_eval
                    | prim _           => exact h_eval
                    | builtinBaseApply => exact h_eval
                  obtain ⟨r_b, T_b', h_eval_t_b, h_vv, h_ctx', h_he',
                          h_env', hv_ra, hv_rb⟩ :=
                    ih_eval ptable level t env_a env_b T_c_a T_c_b r_a T_a'
                      hresp_pt h_ctx_c h_env_c h_eval_t
                  refine ⟨r_b, T_b', ?_, h_vv, h_ctx',
                          HeapEvolution.trans h_he_c h_he',
                          h_env', hv_ra, hv_rb⟩
                  simp only [eval, h_eval_c_b]
                  cases cv_b with
                  | bool b =>
                      cases b with
                      | false => exact absurd rfl h_cv_b_ne
                      | true  => exact h_eval_t_b
                  | num _            => exact h_eval_t_b
                  | nilV             => exact h_eval_t_b
                  | cons _ _         => exact h_eval_t_b
                  | sym _            => exact h_eval_t_b
                  | closure _ _ _    => exact h_eval_t_b
                  | prim _           => exact h_eval_t_b
                  | builtinBaseApply => exact h_eval_t_b
        | app exps =>
            cases exps with
            | nil =>
                simp only [eval] at h_eval
                exact absurd h_eval (by simp)
            | cons f args =>
                simp only [eval] at h_eval
                cases hf : eval k ptable level f env_a T_a with
                | none => rw [hf] at h_eval; simp at h_eval
                | some pr =>
                    obtain ⟨fv_a, T_a_inner⟩ := pr
                    rw [hf] at h_eval
                    simp only at h_eval
                    obtain ⟨fv_b, T_b_inner, h_eval_f_b, h_vv_f, h_ctx1, h_he1,
                            h_env1, hv_fva, hv_fvb⟩ :=
                      ih_eval ptable level f env_a env_b T_a T_b fv_a T_a_inner
                        hresp_pt h_ctx h_env hf
                    cases ha : evalList k ptable level args env_a T_a_inner with
                    | none => rw [ha] at h_eval; simp at h_eval
                    | some pr2 =>
                        obtain ⟨avs_a, T_a_inner2⟩ := pr2
                        rw [ha] at h_eval
                        simp only at h_eval
                        obtain ⟨avs_b, T_b_inner2, h_eval_args_b, h_lvv, h_ctx2,
                                h_he2, h_env2, hv_avsa, hv_avsb⟩ :=
                          ih_evalList ptable level args env_a env_b
                            T_a_inner T_b_inner avs_a T_a_inner2
                            hresp_pt h_ctx1 h_env1 ha
                        -- Lift fv_a/fv_b ValVis + ValValid across the args evolution
                        have h_vv_f' : ValVis fv_a fv_b T_a_inner2.heap T_b_inner2.heap :=
                          h_he2.valVis_preserve fv_a fv_b hv_fva hv_fvb h_vv_f
                        have hv_fva2 : ValValid fv_a T_a_inner2.heap :=
                          ValValid.length_mono fv_a hv_fva h_he2.len_a
                        have hv_fvb2 : ValValid fv_b T_b_inner2.heap :=
                          ValValid.length_mono fv_b hv_fvb h_he2.len_b
                        -- Apply ih_applyVia
                        obtain ⟨r_b, T_b', h_eval_av_b, h_vv, h_he3, h_tc3,
                                hv_ra, hv_rb⟩ :=
                          ih_applyVia ptable level fv_a fv_b avs_a avs_b
                            T_a_inner2 T_b_inner2 r_a T_a'
                            hresp_pt h_ctx2.policy_resp h_ctx2.policy_eq_at
                            h_ctx2.hv_a h_ctx2.hv_b h_ctx2.heap_len_eq
                            h_ctx2.level_envs_valid_a h_ctx2.level_envs_valid_b
                            h_vv_f' h_lvv hv_fva2 hv_fvb2 hv_avsa hv_avsb h_eval
                        have h_he_chain : HeapEvolution T_a T_b T_a' T_b' :=
                          HeapEvolution.trans h_he1 (HeapEvolution.trans h_he2 h_he3)
                        -- Build output WFCtxT using h_tc3 for the cross-side
                        -- invariants and length_mono lifts for env/heap validity.
                        have h_he_outer_a : T_a.heap.length ≤ T_a'.heap.length := by
                          calc T_a.heap.length
                              ≤ T_a_inner.heap.length := h_he1.len_a
                            _ ≤ T_a_inner2.heap.length := h_he2.len_a
                            _ ≤ T_a'.heap.length := h_he3.len_a
                        have h_he_outer_b : T_b.heap.length ≤ T_b'.heap.length := by
                          calc T_b.heap.length
                              ≤ T_b_inner.heap.length := h_he1.len_b
                            _ ≤ T_b_inner2.heap.length := h_he2.len_b
                            _ ≤ T_b'.heap.length := h_he3.len_b
                        -- TowerCross from ih_applyVia carries the missing
                        -- output facts (HeapValid, level_envs_valid, policy_resp).
                        have h_ctx_out : WFCtxT env_a env_b T_a' T_b' level :=
                          ⟨h_tc3.policy_eq_at,
                           h_tc3.hv_a_out, h_tc3.hv_b_out,
                           EnvValid.length_mono h_ctx.ev_a h_he_outer_a,
                           EnvValid.length_mono h_ctx.ev_b h_he_outer_b,
                           h_tc3.policy_resp_out,
                           h_ctx.env_eq, h_tc3.heap_len_eq,
                           h_tc3.level_envs_valid_a_out, h_tc3.level_envs_valid_b_out⟩
                        have h_env_out : EnvVis env_a env_b T_a'.heap T_b'.heap :=
                          h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                            h_ctx.ev_a h_ctx.ev_b h_env
                        refine ⟨r_b, T_b', ?_, h_vv, h_ctx_out,
                                h_he_chain, h_env_out, hv_ra, hv_rb⟩
                        simp [eval, h_eval_f_b, h_eval_args_b, h_eval_av_b]
        | primApp f args =>
            -- Structurally identical to .app, but uses applyDirect
            -- (no base-apply lookup, no level dispatch).
            simp only [eval] at h_eval
            cases hf : eval k ptable level f env_a T_a with
            | none => rw [hf] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨fv_a, T_a_inner⟩ := pr
                rw [hf] at h_eval
                simp only at h_eval
                obtain ⟨fv_b, T_b_inner, h_eval_f_b, h_vv_f, h_ctx1, h_he1,
                        h_env1, hv_fva, hv_fvb⟩ :=
                  ih_eval ptable level f env_a env_b T_a T_b fv_a T_a_inner
                    hresp_pt h_ctx h_env hf
                cases ha : evalList k ptable level args env_a T_a_inner with
                | none => rw [ha] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨avs_a, T_a_inner2⟩ := pr2
                    rw [ha] at h_eval
                    simp only at h_eval
                    obtain ⟨avs_b, T_b_inner2, h_eval_args_b, h_lvv, h_ctx2,
                            h_he2, h_env2, hv_avsa, hv_avsb⟩ :=
                      ih_evalList ptable level args env_a env_b
                        T_a_inner T_b_inner avs_a T_a_inner2
                        hresp_pt h_ctx1 h_env1 ha
                    have h_vv_f' : ValVis fv_a fv_b T_a_inner2.heap T_b_inner2.heap :=
                      h_he2.valVis_preserve fv_a fv_b hv_fva hv_fvb h_vv_f
                    have hv_fva2 : ValValid fv_a T_a_inner2.heap :=
                      ValValid.length_mono fv_a hv_fva h_he2.len_a
                    have hv_fvb2 : ValValid fv_b T_b_inner2.heap :=
                      ValValid.length_mono fv_b hv_fvb h_he2.len_b
                    obtain ⟨r_b, T_b', h_eval_av_b, h_vv, h_he3, h_tc3,
                            hv_ra, hv_rb⟩ :=
                      ih_applyDirect ptable level fv_a fv_b avs_a avs_b
                        T_a_inner2 T_b_inner2 r_a T_a'
                        hresp_pt h_ctx2.policy_resp h_ctx2.policy_eq_at
                        h_ctx2.hv_a h_ctx2.hv_b h_ctx2.heap_len_eq
                        h_ctx2.level_envs_valid_a h_ctx2.level_envs_valid_b
                        h_vv_f' h_lvv hv_fva2 hv_fvb2 hv_avsa hv_avsb h_eval
                    have h_he_chain : HeapEvolution T_a T_b T_a' T_b' :=
                      HeapEvolution.trans h_he1 (HeapEvolution.trans h_he2 h_he3)
                    have h_he_outer_a : T_a.heap.length ≤ T_a'.heap.length := by
                      calc T_a.heap.length
                          ≤ T_a_inner.heap.length := h_he1.len_a
                        _ ≤ T_a_inner2.heap.length := h_he2.len_a
                        _ ≤ T_a'.heap.length := h_he3.len_a
                    have h_he_outer_b : T_b.heap.length ≤ T_b'.heap.length := by
                      calc T_b.heap.length
                          ≤ T_b_inner.heap.length := h_he1.len_b
                        _ ≤ T_b_inner2.heap.length := h_he2.len_b
                        _ ≤ T_b'.heap.length := h_he3.len_b
                    have h_ctx_out : WFCtxT env_a env_b T_a' T_b' level :=
                      ⟨h_tc3.policy_eq_at,
                       h_tc3.hv_a_out, h_tc3.hv_b_out,
                       EnvValid.length_mono h_ctx.ev_a h_he_outer_a,
                       EnvValid.length_mono h_ctx.ev_b h_he_outer_b,
                       h_tc3.policy_resp_out,
                       h_ctx.env_eq, h_tc3.heap_len_eq,
                       h_tc3.level_envs_valid_a_out, h_tc3.level_envs_valid_b_out⟩
                    have h_env_out : EnvVis env_a env_b T_a'.heap T_b'.heap :=
                      h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                        h_ctx.ev_a h_ctx.ev_b h_env
                    refine ⟨r_b, T_b', ?_, h_vv, h_ctx_out,
                            h_he_chain, h_env_out, hv_ra, hv_rb⟩
                    simp [eval, h_eval_f_b, h_eval_args_b, h_eval_av_b]
        | set _ _          => sorry  -- USES policy_eq_at + ValVis_aux_update; substantial
        | em _             => sorry  -- NEW: needs Tower.materialize bisim-preservation
        | letE x e body =>
            -- Mechanical port from lean-green's `.letE`:
            -- 1) IH on e
            -- 2) alloc v_a / v_b in respective heaps
            -- 3) build WFCtxT for the body call (cons-extended env, alloc'd state)
            -- 4) IH on body
            -- 5) chain HeapEvolutions, build output WFCtxT
            simp only [eval] at h_eval
            cases he : eval k ptable level e env_a T_a with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v_a, T_a_inner⟩ := pr
                rw [he] at h_eval
                obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner,
                        h_env_inner, hv_va, hv_vb⟩ :=
                  ih_eval ptable level e env_a env_b T_a T_b v_a T_a_inner
                    hresp_pt h_ctx h_env he
                -- Reduce h_eval: T_a_inner.alloc v_a unfolds.
                simp only [TowerState.alloc, Heap.alloc] at h_eval
                have h_lookup_a :
                    (T_a_inner.heap ++ [v_a])[T_a_inner.heap.length]? = some v_a := by
                  rw [List.getElem?_append_right (Nat.le_refl _)]; simp
                have h_lookup_b :
                    (T_b_inner.heap ++ [v_b])[T_b_inner.heap.length]? = some v_b := by
                  rw [List.getElem?_append_right (Nat.le_refl _)]; simp
                -- HeapValid on alloc heaps.
                have hh_a_alloc : HeapValid (T_a_inner.heap ++ [v_a]) := by
                  intro i v hp
                  by_cases h_lt : i < T_a_inner.heap.length
                  · have hp_old : T_a_inner.heap[i]? = some v := by
                      have heq := getElem?_prefix T_a_inner.heap [v_a] i h_lt
                      rw [← heq]; exact hp
                    exact ValValid.heap_extends v (h_ctx_inner.hv_a i v hp_old)
                      ⟨[v_a], rfl⟩
                  · have h_eq : i = T_a_inner.heap.length := by
                      have h_le : i < (T_a_inner.heap ++ [v_a]).length := by
                        rw [List.getElem?_eq_some_iff] at hp
                        obtain ⟨h, _⟩ := hp; exact h
                      simp [List.length_append] at h_le; omega
                    subst h_eq
                    rw [h_lookup_a] at hp
                    simp only [Option.some.injEq] at hp
                    subst hp
                    exact ValValid.heap_extends v_a hv_va ⟨[v_a], rfl⟩
                have hh_b_alloc : HeapValid (T_b_inner.heap ++ [v_b]) := by
                  intro i v hp
                  by_cases h_lt : i < T_b_inner.heap.length
                  · have hp_old : T_b_inner.heap[i]? = some v := by
                      have heq := getElem?_prefix T_b_inner.heap [v_b] i h_lt
                      rw [← heq]; exact hp
                    exact ValValid.heap_extends v (h_ctx_inner.hv_b i v hp_old)
                      ⟨[v_b], rfl⟩
                  · have h_eq : i = T_b_inner.heap.length := by
                      have h_le : i < (T_b_inner.heap ++ [v_b]).length := by
                        rw [List.getElem?_eq_some_iff] at hp
                        obtain ⟨h, _⟩ := hp; exact h
                      simp [List.length_append] at h_le; omega
                    subst h_eq
                    rw [h_lookup_b] at hp
                    simp only [Option.some.injEq] at hp
                    subst hp
                    exact ValValid.heap_extends v_b hv_vb ⟨[v_b], rfl⟩
                -- EnvValid the cons-extended envs in the alloc heaps.
                have hev_a' : EnvValid (.cons x T_a_inner.heap.length env_a)
                    (T_a_inner.heap ++ [v_a]) := by
                  intro name i hl
                  simp only [List.length_append, List.length_singleton]
                  simp only [Env.lookup] at hl
                  by_cases h_eq : x = name
                  · subst h_eq
                    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                    omega
                  · have h_neq : (x == name) = false := by
                      rw [beq_eq_false_iff_ne]; exact h_eq
                    simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                    have := h_ctx_inner.ev_a name i hl
                    omega
                have hev_b' : EnvValid (.cons x T_b_inner.heap.length env_b)
                    (T_b_inner.heap ++ [v_b]) := by
                  intro name i hl
                  simp only [List.length_append, List.length_singleton]
                  simp only [Env.lookup] at hl
                  by_cases h_eq : x = name
                  · subst h_eq
                    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                    omega
                  · have h_neq : (x == name) = false := by
                      rw [beq_eq_false_iff_ne]; exact h_eq
                    simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                    have := h_ctx_inner.ev_b name i hl
                    omega
                -- Cons-extended envs match cross-side: same name x,
                -- same alloc index (h_ctx_inner.heap_len_eq), same env (env_eq).
                have h_cons_eq :
                    (.cons x T_a_inner.heap.length env_a : Env)
                      = (.cons x T_b_inner.heap.length env_b) := by
                  rw [h_ctx_inner.env_eq, h_ctx_inner.heap_len_eq]
                have h_alloc_len_eq :
                    (T_a_inner.heap ++ [v_a]).length =
                      (T_b_inner.heap ++ [v_b]).length := by
                  simp [List.length_append, h_ctx_inner.heap_len_eq]
                -- Level envs valid in alloc heap (single-side, via
                -- length_mono on h_ctx_inner.level_envs_valid_*).
                have h_levs_a_alloc : ∀ n env, T_a_inner.envAt? n = some env →
                    EnvValid env (T_a_inner.heap ++ [v_a]) := fun n env hen =>
                  EnvValid.heap_extends (h_ctx_inner.level_envs_valid_a n env hen)
                    ⟨[v_a], rfl⟩
                have h_levs_b_alloc : ∀ n env, T_b_inner.envAt? n = some env →
                    EnvValid env (T_b_inner.heap ++ [v_b]) := fun n env hen =>
                  EnvValid.heap_extends (h_ctx_inner.level_envs_valid_b n env hen)
                    ⟨[v_b], rfl⟩
                -- T_a_inner with new heap, same levels.
                let T_a_alloc : TowerState :=
                  { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
                let T_b_alloc : TowerState :=
                  { T_b_inner with heap := T_b_inner.heap ++ [v_b] }
                -- WFCtxT for the body call.
                have h_ctx_alloc :
                    WFCtxT (.cons x T_a_inner.heap.length env_a)
                      (.cons x T_b_inner.heap.length env_b) T_a_alloc T_b_alloc level :=
                  ⟨h_ctx_inner.policy_eq_at, hh_a_alloc, hh_b_alloc,
                   hev_a', hev_b', h_ctx_inner.policy_resp, h_cons_eq, h_alloc_len_eq,
                   h_levs_a_alloc, h_levs_b_alloc⟩
                -- ValVis v_a v_b lifted to alloc heaps.
                have h_vv_v_alloc :
                    ValVis v_a v_b (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) :=
                  ValVis_extends v_a v_b T_a_inner.heap T_b_inner.heap [v_a] [v_b]
                    h_ctx_inner.hv_a h_ctx_inner.hv_b hv_va hv_vb h_vv_v
                -- EnvVis env_a env_b at alloc heaps.
                have h_env_alloc :
                    EnvVis env_a env_b (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) :=
                  EnvVis_extends env_a env_b T_a_inner.heap T_b_inner.heap [v_a] [v_b]
                    h_ctx_inner.hv_a h_ctx_inner.hv_b h_ctx_inner.ev_a h_ctx_inner.ev_b
                    h_env_inner
                -- EnvVis on cons-extended envs at alloc heaps.
                have h_env' :
                    EnvVis (.cons x T_a_inner.heap.length env_a)
                      (.cons x T_b_inner.heap.length env_b)
                      (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) :=
                  EnvVis_cons x T_a_inner.heap.length T_b_inner.heap.length env_a env_b
                    (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) v_a v_b
                    h_lookup_a h_lookup_b h_vv_v_alloc h_env_alloc
                -- IH on body.
                obtain ⟨r_b, T_b', h_eval_b_b, h_vv_r, h_ctx_body, h_he_body,
                        _h_env_body, hv_ra, hv_rb⟩ :=
                  ih_eval ptable level body
                    (.cons x T_a_inner.heap.length env_a)
                    (.cons x T_b_inner.heap.length env_b) T_a_alloc T_b_alloc r_a T_a'
                    hresp_pt h_ctx_alloc h_env' h_eval
                -- HeapEvolution from inner to alloc (just heap-prefix).
                have h_he_alloc : HeapEvolution T_a_inner T_b_inner T_a_alloc T_b_alloc :=
                  HeapEvolution.from_heapExt h_ctx_inner.hv_a h_ctx_inner.hv_b
                    ⟨[v_a], rfl⟩ ⟨[v_b], rfl⟩
                have h_he_chain : HeapEvolution T_a T_b T_a' T_b' :=
                  HeapEvolution.trans h_he_inner
                    (HeapEvolution.trans h_he_alloc h_he_body)
                have h_ctx_out : WFCtxT env_a env_b T_a' T_b' level :=
                  ⟨h_ctx_body.policy_eq_at, h_ctx_body.hv_a, h_ctx_body.hv_b,
                   h_ctx.ev_a.length_mono h_he_chain.len_a,
                   h_ctx.ev_b.length_mono h_he_chain.len_b,
                   h_ctx_body.policy_resp, h_ctx.env_eq, h_ctx_body.heap_len_eq,
                   h_ctx_body.level_envs_valid_a, h_ctx_body.level_envs_valid_b⟩
                have h_env_out : EnvVis env_a env_b T_a'.heap T_b'.heap :=
                  h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                    h_ctx.ev_a h_ctx.ev_b h_env
                refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out,
                        h_he_chain, h_env_out, hv_ra, hv_rb⟩
                simp only [eval, h_eval_e_b, TowerState.alloc, Heap.alloc]
                exact h_eval_b_b
        | seq exps =>
            -- Three sub-cases: empty, singleton, e :: e2 :: rest2.
            -- Mechanical port of lean-green's template, threading
            -- `level` through inner ih_eval calls. No metaEnv.
            cases exps with
            | nil =>
                simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_T⟩ := h_eval
                subst h_r; subst h_T
                refine ⟨.nilV, T_b, ?_, ?_, h_ctx,
                        HeapEvolution.refl _ _, h_env, trivial, trivial⟩
                · simp [eval]
                · intro depth
                  cases depth with | zero => trivial | succ _ => trivial
            | cons e rest =>
                cases rest with
                | nil =>
                    -- exps = [e]: eval (k+1) (.seq [e]) ↦ eval k e
                    simp only [eval] at h_eval
                    obtain ⟨r_b, T_b', h_eval_b, h_vv, h_ctx', h_he,
                            h_env', hv_ra, hv_rb⟩ :=
                      ih_eval ptable level e env_a env_b T_a T_b r_a T_a'
                        hresp_pt h_ctx h_env h_eval
                    refine ⟨r_b, T_b', ?_, h_vv, h_ctx', h_he, h_env',
                            hv_ra, hv_rb⟩
                    simp [eval, h_eval_b]
                | cons e2 rest2 =>
                    -- exps = e :: e2 :: rest2: eval e then recurse on .seq (e2 :: rest2)
                    simp only [eval] at h_eval
                    cases he : eval k ptable level e env_a T_a with
                    | none => rw [he] at h_eval; simp at h_eval
                    | some pr =>
                        obtain ⟨v_e, T_a_inner⟩ := pr
                        rw [he] at h_eval
                        simp only at h_eval
                        obtain ⟨_v_e_b, T_b_inner, h_eval_e_b, _h_vv_e,
                                h_ctx_inner, h_he_inner, h_env_inner,
                                _hv_ve_a, _hv_ve_b⟩ :=
                          ih_eval ptable level e env_a env_b T_a T_b v_e T_a_inner
                            hresp_pt h_ctx h_env he
                        obtain ⟨r_b, T_b', h_eval_seq_b, h_vv, h_ctx', h_he',
                                h_env', hv_ra, hv_rb⟩ :=
                          ih_eval ptable level (.seq (e2 :: rest2)) env_a env_b
                            T_a_inner T_b_inner r_a T_a'
                            hresp_pt h_ctx_inner h_env_inner h_eval
                        refine ⟨r_b, T_b', ?_, h_vv, h_ctx',
                                HeapEvolution.trans h_he_inner h_he',
                                h_env', hv_ra, hv_rb⟩
                        simp [eval, h_eval_e_b, h_eval_seq_b]
        | installPolicy idx =>
            -- Both sides install the same policy at the same level.
            -- Heaps unchanged; cross-side WFCtxT preserved with the
            -- new policy (which respects bisim — from hresp_pt).
            simp only [eval] at h_eval
            cases hp : ptable[idx]? with
            | none =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_T⟩ := h_eval
                subst h_r; subst h_T
                refine ⟨.bool false, T_b, ?_, ?_, h_ctx,
                        HeapEvolution.refl _ _, h_env, trivial, trivial⟩
                · simp [eval, hp]
                · intro depth
                  cases depth with | zero => trivial | succ _ => rfl
            | some newPolicy =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_T⟩ := h_eval
                subst h_r; subst h_T
                have h_resp_new : PolicyRespectsBisimT newPolicy :=
                  hresp_pt idx newPolicy hp
                -- T_a' = T_a.setPolicyAt level newPolicy.
                -- T_b' = T_b.setPolicyAt level newPolicy.
                -- Cross-side: heap unchanged, level envs unchanged,
                -- policy at `level` is some newPolicy on both sides
                -- (when level was materialized; otherwise unchanged).
                have h_pol_a := T_a.setPolicyAt_policyAt?_self level newPolicy
                have h_pol_b := T_b.setPolicyAt_policyAt?_self level newPolicy
                have h_heap_a := T_a.setPolicyAt_heap level newPolicy
                have h_heap_b := T_b.setPolicyAt_heap level newPolicy
                have h_envs_a : ∀ m,
                    (T_a.setPolicyAt level newPolicy).envAt? m = T_a.envAt? m :=
                  fun m => T_a.setPolicyAt_envAt? level m newPolicy
                have h_envs_b : ∀ m,
                    (T_b.setPolicyAt level newPolicy).envAt? m = T_b.envAt? m :=
                  fun m => T_b.setPolicyAt_envAt? level m newPolicy
                refine ⟨.bool true, T_b.setPolicyAt level newPolicy, ?_, ?_,
                        ?_, ?_, ?_, trivial, trivial⟩
                · simp [eval, hp]
                · intro depth
                  cases depth with | zero => trivial | succ _ => rfl
                · -- WFCtxT for output state
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h_ctx.env_eq, ?_, ?_, ?_⟩
                  · -- policy_eq_at: rewrite with the .map fact, both sides
                    rw [h_pol_a, h_pol_b, h_ctx.policy_eq_at]
                  · rw [h_heap_a]; exact h_ctx.hv_a
                  · rw [h_heap_b]; exact h_ctx.hv_b
                  · rw [h_heap_a]; exact h_ctx.ev_a
                  · rw [h_heap_b]; exact h_ctx.ev_b
                  · -- policy_resp at output: from hresp_pt for newPolicy
                    intro p h_eq
                    rw [h_pol_a] at h_eq
                    cases h_old : T_a.policyAt? level with
                    | none => rw [h_old] at h_eq; simp at h_eq
                    | some _ => rw [h_old] at h_eq; simp at h_eq; subst h_eq; exact h_resp_new
                  · -- heap_len_eq: heaps unchanged
                    rw [h_heap_a, h_heap_b]; exact h_ctx.heap_len_eq
                  · -- level_envs_valid_a: envs and heap unchanged
                    intro m env h_env_eq
                    rw [h_envs_a m] at h_env_eq
                    rw [h_heap_a]
                    exact h_ctx.level_envs_valid_a m env h_env_eq
                  · intro m env h_env_eq
                    rw [h_envs_b m] at h_env_eq
                    rw [h_heap_b]
                    exact h_ctx.level_envs_valid_b m env h_env_eq
                · -- HeapEvolution: heaps unchanged on both sides; the
                  -- levels field changed but HeapEvolution only cares
                  -- about heaps + bisim preservation.
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · rw [h_heap_a]; exact Nat.le_refl _
                  · rw [h_heap_b]; exact Nat.le_refl _
                  · intro _ _ _ _ _ _ h_vis
                    rw [h_heap_a, h_heap_b]
                    exact h_vis
                  · intro _ _ _ _ _ h_vis
                    rw [h_heap_a, h_heap_b]
                    exact h_vis
                · -- EnvVis env_a env_b T_a'.heap T_b'.heap
                  rw [h_heap_a, h_heap_b]; exact h_env
      · -- evalList (k+1) — mechanical port from lean-green
        intro ptable level exps env_a env_b T_a T_b rs_a T_a'
              hresp_pt h_ctx h_env h_eval
        cases exps with
        | nil =>
            simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨h_r, h_T⟩ := h_eval
            subst h_r; subst h_T
            refine ⟨[], T_b, ?_, ?_, h_ctx,
                    HeapEvolution.refl _ _, h_env, trivial, trivial⟩
            · simp [evalList]
            · trivial
        | cons e rest =>
            simp only [evalList] at h_eval
            cases he : eval k ptable level e env_a T_a with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v_a, T_a_inner⟩ := pr
                rw [he] at h_eval
                simp only at h_eval
                cases hrest : evalList k ptable level rest env_a T_a_inner with
                | none => rw [hrest] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨vs_a, T_a_inner2⟩ := pr2
                    rw [hrest] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨h_r, h_T⟩ := h_eval
                    subst h_r; subst h_T
                    -- IH on e
                    obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner,
                            h_he_inner, h_env_inner, hv_va, hv_vb⟩ :=
                      ih_eval ptable level e env_a env_b T_a T_b v_a T_a_inner
                        hresp_pt h_ctx h_env he
                    -- IH on rest
                    obtain ⟨vs_b, T_b_inner2, h_eval_rest_b, h_lvv, h_ctx_inner2,
                            h_he_inner2, h_env_inner2, hv_vsa, hv_vsb⟩ :=
                      ih_evalList ptable level rest env_a env_b T_a_inner T_b_inner
                        vs_a T_a_inner2 hresp_pt h_ctx_inner h_env_inner hrest
                    -- Lift ValVis v_a v_b and ValValid via HeapEvolution preservation
                    have h_vv_v' : ValVis v_a v_b T_a_inner2.heap T_b_inner2.heap :=
                      h_he_inner2.valVis_preserve v_a v_b hv_va hv_vb h_vv_v
                    have hv_va' : ValValid v_a T_a_inner2.heap :=
                      ValValid.length_mono v_a hv_va h_he_inner2.len_a
                    have hv_vb' : ValValid v_b T_b_inner2.heap :=
                      ValValid.length_mono v_b hv_vb h_he_inner2.len_b
                    have h_he_chain : HeapEvolution T_a T_b T_a_inner2 T_b_inner2 :=
                      HeapEvolution.trans h_he_inner h_he_inner2
                    refine ⟨v_b :: vs_b, T_b_inner2, ?_,
                            ⟨h_vv_v', h_lvv⟩, h_ctx_inner2,
                            h_he_chain, h_env_inner2,
                            ⟨hv_va', hv_vsa⟩, ⟨hv_vb', hv_vsb⟩⟩
                    simp [evalList, h_eval_e_b, h_eval_rest_b]
      · -- applyVia (k+1) — needs T.materialize bisim-preservation, then dispatch
        sorry
      · -- applyDirect (k+1) — non-applicable / builtin / prim cases proved;
        -- .closure case sorry'd (needs allocStep / EnvVis_extends / WFCtxT
        -- alloc-state construction — substantial port of lean-green's
        -- alloc_chain_bisim machinery to the tower model)
        intro ptable level op_a op_b args_a args_b T_a T_b r_a T_a'
              hresp_pt h_resp_at h_pol_eq h_hv_a h_hv_b h_hl_eq
              h_levs_a h_levs_b h_vv_op h_lvv hv_opa hv_opb
              hv_argsa hv_argsb h_eval
        have h_vv1 : ValVis_aux 1 op_a op_b T_a.heap T_b.heap := h_vv_op 1
        cases op_a with
        | num _    => simp [applyDirect] at h_eval
        | bool _   => simp [applyDirect] at h_eval
        | nilV     => simp [applyDirect] at h_eval
        | sym _    => simp [applyDirect] at h_eval
        | cons _ _ => simp [applyDirect] at h_eval
        | builtinBaseApply =>
            have h_opb : op_b = .builtinBaseApply := by
              cases op_b with
              | builtinBaseApply => rfl
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | nilV => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | cons _ _ => simp [ValVis_aux] at h_vv1
              | closure _ _ _ => simp [ValVis_aux] at h_vv1
              | prim _ => simp [ValVis_aux] at h_vv1
            subst h_opb
            unfold applyDirect at h_eval
            match args_a, args_b, h_lvv, hv_argsa, hv_argsb with
            | [], _, _, _, _ => simp at h_eval
            | _ :: [], _, _, _, _ => simp at h_eval
            | _ :: _ :: _ :: _, _, _, _, _ => simp at h_eval
            | [_actualOp_a, _operandsList_a], [], h_lvv', _, _ => exact h_lvv'.elim
            | [_actualOp_a, _operandsList_a], [_], h_lvv', _, _ =>
                exact h_lvv'.2.elim
            | [_actualOp_a, _operandsList_a], _ :: _ :: _ :: _, h_lvv', _, _ =>
                exact h_lvv'.2.2.elim
            | [actualOp_a, operandsList_a], [actualOp_b, operandsList_b],
                ⟨h_vv_actual, h_vv_olist, _⟩, ⟨hv_actual_a, hv_olist_a, _⟩,
                ⟨hv_actual_b, hv_olist_b, _⟩ =>
                simp only at h_eval
                cases hl_a : valToList operandsList_a with
                | none => rw [hl_a] at h_eval; simp at h_eval
                | some operands_a =>
                    rw [hl_a] at h_eval
                    simp only at h_eval
                    obtain ⟨operands_b, hl_b, h_lvv_ops, hv_ops_a, hv_ops_b⟩ :=
                      valToList_bisim operands_a operandsList_a operandsList_b
                        T_a.heap T_b.heap hl_a h_vv_olist hv_olist_a hv_olist_b
                    obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_he', h_tc, hv_ra, hv_rb⟩ :=
                      ih_applyDirect ptable level actualOp_a actualOp_b
                        operands_a operands_b T_a T_b r_a T_a'
                        hresp_pt h_resp_at h_pol_eq h_hv_a h_hv_b h_hl_eq
                        h_levs_a h_levs_b h_vv_actual h_lvv_ops
                        hv_actual_a hv_actual_b hv_ops_a hv_ops_b h_eval
                    refine ⟨r_b, T_b', ?_, h_vv_r, h_he', h_tc, hv_ra, hv_rb⟩
                    simp only [applyDirect, hl_b, h_eval_b]
        | prim name =>
            have h_opb : op_b = .prim name := by
              cases op_b with
              | prim n' =>
                  have : name = n' := by simp [ValVis_aux] at h_vv1; exact h_vv1
                  subst this; rfl
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | nilV => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | cons _ _ => simp [ValVis_aux] at h_vv1
              | closure _ _ _ => simp [ValVis_aux] at h_vv1
              | builtinBaseApply => simp [ValVis_aux] at h_vv1
            subst h_opb
            simp only [applyDirect] at h_eval
            cases hp_a : applyPrim name args_a with
            | none => rw [hp_a] at h_eval; simp at h_eval
            | some v_a' =>
                rw [hp_a] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨h_r, h_T⟩ := h_eval
                subst h_r; subst h_T
                obtain ⟨r_b, hp_b, h_vv_r, hv_ra, hv_rb⟩ :=
                  applyPrim_bisim name args_a args_b T_a.heap T_b.heap
                    h_lvv hv_argsa hv_argsb v_a' hp_a
                refine ⟨r_b, T_b, ?_, h_vv_r, HeapEvolution.refl _ _,
                        TowerCross.refl _ _ _ h_hl_eq h_pol_eq h_hv_a h_hv_b
                          h_levs_a h_levs_b h_resp_at,
                        hv_ra, hv_rb⟩
                simp only [applyDirect, hp_b]
        | closure _ _ _ =>
            -- Needs alloc_chain_bisim + allocStep_chain_aligned + EnvVis_extends
            -- adapted to TowerState. ~200 LOC port; deferred.
            sorry
