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
      obtain ⟨_ih_eval, _ih_evalList, _ih_applyVia, _ih_applyDirect⟩ := ih
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
        | ifte _ _ _       => sorry  -- mechanical: ih_eval × 2
        | app _            => sorry  -- mechanical: ih_eval, ih_evalList, ih_applyVia
        | primApp _ _      => sorry  -- mechanical: ih_eval, ih_evalList, ih_applyDirect
        | set _ _          => sorry  -- USES policy_eq_at + ValVis_aux_update; substantial
        | em _             => sorry  -- NEW: needs Tower.materialize bisim-preservation
        | letE _ _ _       => sorry  -- mechanical with ih_eval + Heap.alloc preservation
        | seq _            => sorry  -- mechanical: ih_eval recursion
        | installPolicy _  => sorry  -- needs setPolicyAt-preserves-heap/envs lemmas
      · -- evalList (k+1) — mechanical: ih_eval + ih_evalList
        sorry
      · -- applyVia (k+1) — needs T.materialize bisim-preservation, then dispatch
        sorry
      · -- applyDirect (k+1) — closure case allocates args; prim case is direct
        sorry
