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

/-- `acceptAllPolicy` admits every mutation, so trivially respects bisim
    (both sides return `true` regardless). -/
theorem acceptAllPolicy_respects_bisimT :
    PolicyRespectsBisimT acceptAllPolicy := by
  unfold PolicyRespectsBisimT acceptAllPolicy; intros; rfl

/-! ## Single-side materialize preservation lemmas

    Used by `.em` and `applyVia` cases below. Each says materialize
    preserves a single-side invariant (HeapValid, level-envs-valid,
    all-policies-respect-bisim). Bodies sorry'd — straightforward
    inductions over Nat.fold + appeal to `freshLevelEnv`'s
    deterministic structure. -/

/-- HeapValid is preserved when appending closed values (atoms have
    `ValValid v _` = True regardless of heap; pre-existing cells get
    extended via heap_extends). PROVED. -/
private theorem HeapValid_append_closed (h : Heap) (extras : Heap)
    (h_hv : HeapValid h)
    (h_extras : ∀ v ∈ extras, closedValB v = true) :
    HeapValid (h ++ extras) := by
  intro i v hp
  by_cases hi : i < h.length
  · have heq : (h ++ extras)[i]? = h[i]? := List.getElem?_append_left hi
    rw [heq] at hp
    exact ValValid.heap_extends v (h_hv i v hp) ⟨extras, rfl⟩
  · have hi' : h.length ≤ i := Nat.not_lt.mp hi
    have heq : (h ++ extras)[i]? = extras[i - h.length]? :=
      List.getElem?_append_right hi'
    rw [heq] at hp
    have h_in : v ∈ extras := List.getElem?_mem hp
    exact closedValB_ValValid v (h ++ extras) (h_extras v h_in)

/-- Every cell in `primPairs` is a closed value. Proved by `decide`
    after `unfold` exposes the concrete 13-element list. -/
private theorem primPairs_atoms : ∀ p ∈ primPairs, closedValB p.2 = true := by
  unfold primPairs
  decide

/-- The buildBindings foldl extras are all closed. -/
private theorem buildBindings_extras_closed
    (pairs : List (String × Val)) (h : Heap) (env : Env)
    (h_atoms : ∀ p ∈ pairs, closedValB p.2 = true) :
    ∃ extras, (pairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
      (h, env)).1 = h ++ extras ∧ (∀ v ∈ extras, closedValB v = true) := by
  induction pairs generalizing h env with
  | nil =>
      refine ⟨[], by simp [List.foldl], ?_⟩
      intro v hv; cases hv
  | cons p rest ih =>
      simp only [List.foldl]
      have h_p : closedValB p.2 = true := h_atoms p (List.mem_cons_self)
      have h_rest_atoms : ∀ q ∈ rest, closedValB q.2 = true :=
        fun q hq => h_atoms q (List.mem_cons_of_mem _ hq)
      obtain ⟨extras, h_eq, h_closed⟩ :=
        ih (h ++ [p.2]) (.cons p.1 h.length env) h_rest_atoms
      refine ⟨[p.2] ++ extras, ?_, ?_⟩
      · rw [h_eq, List.append_assoc]
      · intro v hv
        rcases List.mem_append.mp hv with h_in | h_in
        · simp at h_in; rw [h_in]; exact h_p
        · exact h_closed v h_in

/-- `freshLevelEnv h` extras are all closed. -/
private theorem freshLevelEnv_extras_closed (h : Heap) :
    ∃ extras, (freshLevelEnv h).1 = h ++ extras ∧
      (∀ v ∈ extras, closedValB v = true) := by
  unfold freshLevelEnv
  simp only [Heap.alloc]
  obtain ⟨extras, h_eq, h_closed⟩ :=
    buildBindings_extras_closed primPairs h .nil primPairs_atoms
  refine ⟨extras ++ [.builtinBaseApply], ?_, ?_⟩
  · rw [h_eq, List.append_assoc]
  · intro v hv
    rcases List.mem_append.mp hv with h_in | h_in
    · exact h_closed v h_in
    · simp at h_in; rw [h_in]; rfl

/-- One materializeStep preserves HeapValid. -/
private theorem materializeStep_HeapValid_preserves (T : TowerState)
    (h_hv : HeapValid T.heap) :
    HeapValid (materializeStep T).heap := by
  unfold materializeStep
  obtain ⟨extras, h_eq, h_closed⟩ := freshLevelEnv_extras_closed T.heap
  show HeapValid (freshLevelEnv T.heap).1
  rw [h_eq]
  exact HeapValid_append_closed T.heap extras h_hv h_closed

/-- Iterated materializeStep preserves HeapValid. -/
private theorem materializeStep_iter_HeapValid_preserves (T : TowerState) (k : Nat)
    (h_hv : HeapValid T.heap) :
    HeapValid (Nat.fold k (fun _ _ T' => materializeStep T') T).heap := by
  induction k with
  | zero => simp [Nat.fold]; exact h_hv
  | succ k ih =>
      simp only [Nat.fold]
      exact materializeStep_HeapValid_preserves _ ih

/-- Materialize preserves heap validity. -/
theorem materialize_HeapValid_preserves
    (T T' : TowerState) (n : Nat)
    (h_mat : T.materialize n = some T')
    (h_hv : HeapValid T.heap) :
    HeapValid T'.heap := by
  unfold TowerState.materialize at h_mat
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat
  · simp [h1] at h_mat
    by_cases h2 : T.levels.length > n
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact h_hv
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact materializeStep_iter_HeapValid_preserves T (n + 1 - T.levels.length) h_hv

/-- After buildBindings foldl, every lookup in the resulting env points
    to an idx within the resulting heap. -/
private theorem buildBindings_foldl_env_lookups_in_range
    (pairs : List (String × Val)) (h : Heap) (env : Env)
    (h_env_in_range : ∀ name i, env.lookup name = some i → i < h.length) :
    ∀ name i, (pairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
      (h, env)).2.lookup name = some i →
    i < (pairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
      (h, env)).1.length := by
  induction pairs generalizing h env with
  | nil =>
      simp only [List.foldl]; exact h_env_in_range
  | cons p rest ih =>
      simp only [List.foldl]
      apply ih (h ++ [p.2]) (.cons p.1 h.length env)
      intro name i hl
      simp only [Env.lookup, List.length_append, List.length_singleton]
      simp only [Env.lookup] at hl
      split at hl
      · -- p.1 == name: hl gives some h.length = some i
        simp at hl; rw [← hl]; omega
      · -- p.1 ≠ name: hl is env.lookup name = some i
        have h_in_range := h_env_in_range name i hl
        omega

/-- The env from `freshLevelEnv` is valid in the resulting heap. -/
private theorem freshLevelEnv_env_valid (h : Heap) :
    EnvValid (freshLevelEnv h).2 (freshLevelEnv h).1 := by
  intro name i hl
  unfold freshLevelEnv at hl ⊢
  simp only [Heap.alloc] at hl ⊢
  -- The result env is `.cons "base-apply" (foldl-h.length) envPrims`
  -- Result heap has length (foldl-h.length) + 1
  simp only [Env.lookup] at hl
  rw [List.length_append, List.length_singleton]
  split at hl
  · -- "base-apply" == name: hl is some foldl-h.length = some i
    simp at hl; rw [← hl]; omega
  · -- envPrims.lookup name = some i
    have h_inner : ∀ name i, ((primPairs.foldl
        (fun (acc : Heap × Env) (kv : String × Val) =>
          (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
        (h, .nil)).2).lookup name = some i →
        i < (primPairs.foldl
          (fun (acc : Heap × Env) (kv : String × Val) =>
            (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
          (h, .nil)).1.length :=
      buildBindings_foldl_env_lookups_in_range primPairs h .nil
        (fun _ _ h => by simp [Env.lookup] at h)
    have := h_inner name i hl
    omega

/-- One materializeStep preserves "level envs valid in heap". -/
private theorem materializeStep_level_envs_valid_preserves
    (T : TowerState)
    (h_hv : HeapValid T.heap)
    (h_levs : ∀ m env, T.envAt? m = some env → EnvValid env T.heap) :
    ∀ m env, (materializeStep T).envAt? m = some env →
    EnvValid env (materializeStep T).heap := by
  intro m env hen
  unfold materializeStep at hen ⊢
  obtain ⟨extras, h_eq, _⟩ := freshLevelEnv_extras_closed T.heap
  unfold TowerState.envAt? TowerState.levelAt? at hen
  by_cases h_in : m < T.levels.length
  · -- Existing level: env unchanged, lift via heap_extends
    rw [List.getElem?_append_left h_in] at hen
    have h_old : T.envAt? m = some env := by
      unfold TowerState.envAt? TowerState.levelAt?; exact hen
    have h_old_valid : EnvValid env T.heap := h_levs m env h_old
    show EnvValid env (freshLevelEnv T.heap).1
    rw [h_eq]
    exact EnvValid.heap_extends h_old_valid ⟨extras, rfl⟩
  · -- New level (or out of bounds)
    by_cases h_eq_idx : m = T.levels.length
    · -- New level
      subst h_eq_idx
      rw [List.getElem?_append_right (Nat.le_refl _)] at hen
      simp at hen
      rw [← hen]
      show EnvValid (freshLevelEnv T.heap).2 (freshLevelEnv T.heap).1
      exact freshLevelEnv_env_valid T.heap
    · -- Out of bounds
      let new_ls : LevelState :=
        { env := (freshLevelEnv T.heap).2, policy := acceptAllPolicy }
      have h_oob : (T.levels ++ [new_ls]).length ≤ m := by
        simp [List.length_append]; omega
      rw [List.getElem?_eq_none h_oob] at hen
      exact Option.noConfusion hen

/-- Iterated materializeStep preserves "level envs valid in heap". -/
private theorem materializeStep_iter_level_envs_valid_preserves
    (T : TowerState) (k : Nat)
    (h_hv : HeapValid T.heap)
    (h_levs : ∀ m env, T.envAt? m = some env → EnvValid env T.heap) :
    ∀ m env, (Nat.fold k (fun _ _ T' => materializeStep T') T).envAt? m = some env →
    EnvValid env (Nat.fold k (fun _ _ T' => materializeStep T') T).heap := by
  induction k with
  | zero => simp [Nat.fold]; exact h_levs
  | succ k ih =>
      simp only [Nat.fold]
      have ih_hv := materializeStep_iter_HeapValid_preserves T k h_hv
      exact materializeStep_level_envs_valid_preserves _ ih_hv ih

/-- Materialize preserves "level envs valid in heap". -/
theorem materialize_level_envs_valid_preserves
    (T T' : TowerState) (n : Nat)
    (h_mat : T.materialize n = some T')
    (h_hv : HeapValid T.heap)
    (h_levs : ∀ m env, T.envAt? m = some env → EnvValid env T.heap) :
    ∀ m env, T'.envAt? m = some env → EnvValid env T'.heap := by
  unfold TowerState.materialize at h_mat
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat
  · simp [h1] at h_mat
    by_cases h2 : T.levels.length > n
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact h_levs
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact materializeStep_iter_level_envs_valid_preserves T (n + 1 - T.levels.length) h_hv h_levs

/-- One materializeStep preserves "all policies satisfy P". -/
private theorem materializeStep_policies_resp_preserves
    (T : TowerState) (P : BlackPolicy → Prop)
    (h_resp : ∀ m p, T.policyAt? m = some p → P p)
    (h_acceptAll : P acceptAllPolicy) :
    ∀ m p, (materializeStep T).policyAt? m = some p → P p := by
  intro m p hp
  unfold materializeStep at hp
  unfold TowerState.policyAt? TowerState.levelAt? at hp
  by_cases h_in : m < T.levels.length
  · rw [List.getElem?_append_left h_in] at hp
    have h_old : T.policyAt? m = some p := by
      unfold TowerState.policyAt? TowerState.levelAt?; exact hp
    exact h_resp m p h_old
  · by_cases h_eq : m = T.levels.length
    · subst h_eq
      rw [List.getElem?_append_right (Nat.le_refl _)] at hp
      simp at hp
      rw [← hp]
      exact h_acceptAll
    · let new_ls : LevelState :=
        { env := (freshLevelEnv T.heap).2, policy := acceptAllPolicy }
      have h_oob : (T.levels ++ [new_ls]).length ≤ m := by
        simp [List.length_append]; omega
      rw [List.getElem?_eq_none h_oob] at hp
      exact Option.noConfusion hp

/-- Iterated materializeStep preserves "all policies satisfy P". -/
private theorem materializeStep_iter_policies_resp_preserves
    (T : TowerState) (k : Nat) (P : BlackPolicy → Prop)
    (h_resp : ∀ m p, T.policyAt? m = some p → P p)
    (h_acceptAll : P acceptAllPolicy) :
    ∀ m p, (Nat.fold k (fun _ _ T' => materializeStep T') T).policyAt? m = some p → P p := by
  induction k with
  | zero => simp [Nat.fold]; exact h_resp
  | succ k ih =>
      simp only [Nat.fold]
      exact materializeStep_policies_resp_preserves _ P ih h_acceptAll

/-- Materialize preserves "all policies satisfy P" provided P holds for
    `acceptAllPolicy` (which materialize uses for new levels). -/
theorem materialize_policies_resp_preserves
    (T T' : TowerState) (n : Nat) (P : BlackPolicy → Prop)
    (h_mat : T.materialize n = some T')
    (h_resp : ∀ m p, T.policyAt? m = some p → P p)
    (h_acceptAll : P acceptAllPolicy) :
    ∀ m p, T'.policyAt? m = some p → P p := by
  unfold TowerState.materialize at h_mat
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat
  · simp [h1] at h_mat
    by_cases h2 : T.levels.length > n
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact h_resp
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact materializeStep_iter_policies_resp_preserves T
        (n + 1 - T.levels.length) P h_resp h_acceptAll

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
  /-- Cross-side: at every level, the env (if materialized) is the same
      on both sides. Holds for `initTower` (rfl); preserved by every eval
      operation since none modifies existing-level envs (set!/letE/alloc
      only touch heap; installPolicy modifies policy not env; em
      materializes new levels deterministically from heap.length, equal
      cross-side via `heap_len_eq`). -/
  level_envs_eq : ∀ n, T_a.envAt? n = T_b.envAt? n
  /-- Cross-side: at every level, policies match. Needed by `.em` to
      construct `WFCtxT` for the IH at level+1 (the level above might
      have a pre-existing policy that wasn't covered by `policy_eq_at`,
      which is single-level). Preserved by every eval operation: pure
      ops don't touch policies; `installPolicy` applies the same
      `setPolicyAt` cross-side; materialize adds new levels with
      `acceptAllPolicy` deterministically. -/
  policies_eq : ∀ n, T_a.policyAt? n = T_b.policyAt? n
  /-- Every policy at every level respects bisim. Strengthens
      `policy_resp` (single-level) to a tower-wide invariant. Needed by
      `.em` to construct `policy_resp` at the new active level (level+1).
      Preserved: pure ops don't touch policies; `installPolicy` admits a
      new policy from the bisim-respecting `ptable`; materialize adds
      `acceptAllPolicy` (which respects bisim trivially). -/
  policies_resp_all : ∀ n p, T_a.policyAt? n = some p → PolicyRespectsBisimT p

theorem WFCtxT.refl (env : Env) (T : TowerState) (level : Nat)
    (hh : HeapValid T.heap) (hev : EnvValid env T.heap)
    (hresp : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_levels : ∀ n env, T.envAt? n = some env → EnvValid env T.heap)
    (h_resp_all : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) :
    WFCtxT env env T T level :=
  ⟨rfl, hh, hh, hev, hev, hresp, rfl, rfl, h_levels, h_levels,
   fun _ => rfl, fun _ => rfl, h_resp_all⟩

/-! ## Single-side level-envs preservation

    `eval` (and friends) never *removes* a materialized level — they
    can only add new levels via `(em ...)`. So `T.envAt? m` is
    monotone over evaluation: if `T.envAt? m = some env`, then
    `T'.envAt? m = some env` after eval. Mutual on fuel.

    Used by the `applyDirect.closure` case in `frame_tower` to
    discharge the `TowerCross.levels_mono_a/b` outputs: starting
    from `T_a.envAt? n = some env`, after the alloc step (which
    preserves levels via `alloc_envAt?`) and then the body eval
    (which preserves via this lemma), `T_a'.envAt? n = some env`. -/

/-- Joint conjunction theorem: all 4 mutual functions preserve
    `envAt?` at every materialized level. Proved by single induction
    on fuel, then case-split per function and per constructor. -/
theorem all_preserves_envAt (n : Nat) :
    (∀ (ptable : PolicyTable) (level : Nat) (exp : Expr) (env : Env)
       (T : TowerState) (r : Val) (T' : TowerState) (m : Nat) (env_m : Env),
        eval n ptable level exp env T = some (r, T') →
        T.envAt? m = some env_m → T'.envAt? m = some env_m) ∧
    (∀ (ptable : PolicyTable) (level : Nat) (exps : List Expr) (env : Env)
       (T : TowerState) (rs : List Val) (T' : TowerState) (m : Nat) (env_m : Env),
        evalList n ptable level exps env T = some (rs, T') →
        T.envAt? m = some env_m → T'.envAt? m = some env_m) ∧
    (∀ (ptable : PolicyTable) (level : Nat) (op : Val) (args : List Val)
       (T : TowerState) (r : Val) (T' : TowerState) (m : Nat) (env_m : Env),
        applyVia n ptable level op args T = some (r, T') →
        T.envAt? m = some env_m → T'.envAt? m = some env_m) ∧
    (∀ (ptable : PolicyTable) (level : Nat) (op : Val) (args : List Val)
       (T : TowerState) (r : Val) (T' : TowerState) (m : Nat) (env_m : Env),
        applyDirect n ptable level op args T = some (r, T') →
        T.envAt? m = some env_m → T'.envAt? m = some env_m) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intros; rename_i h _; simp [eval] at h
      · intros; rename_i h _; simp [evalList] at h
      · intros; rename_i h _; simp [applyVia] at h
      · intros; rename_i h _; simp [applyDirect] at h
  | succ k ih =>
      obtain ⟨ih_eval, ih_evalList, ih_applyVia, ih_applyDirect⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- eval (k+1)
        intro ptable level exp env T r T' m env_m h_eval h_env
        cases exp with
        | num _ | bool _ | lam _ _ =>
            simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_T⟩ := h_eval; subst h_T; exact h_env
        | quote v =>
            simp only [eval] at h_eval
            split at h_eval
            · simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
              obtain ⟨_, h_T⟩ := h_eval; subst h_T; exact h_env
            · simp at h_eval
        | var x =>
            simp only [eval] at h_eval
            cases hl : env.lookup x with
            | none => rw [hl] at h_eval; simp at h_eval
            | some i =>
                rw [hl] at h_eval; simp only at h_eval
                cases hp : T.heap[i]? with
                | none => rw [hp] at h_eval; simp at h_eval
                | some _ =>
                    rw [hp] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨_, h_T⟩ := h_eval; subst h_T; exact h_env
        | ifte c t e =>
            simp only [eval] at h_eval
            cases hc : eval k ptable level c env T with
            | none => rw [hc] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨cv, T_c⟩ := pr
                rw [hc] at h_eval
                have h_env_c := ih_eval ptable level c env T cv T_c m env_m hc h_env
                cases cv with
                | bool b =>
                    cases b with
                    | false => simp only at h_eval
                               exact ih_eval ptable level e env T_c r T' m env_m h_eval h_env_c
                    | true => exact ih_eval ptable level t env T_c r T' m env_m h_eval h_env_c
                | num _ | nilV | cons _ _ | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
                    exact ih_eval ptable level t env T_c r T' m env_m h_eval h_env_c
        | app exps =>
            cases exps with
            | nil => simp [eval] at h_eval
            | cons f args =>
                simp only [eval] at h_eval
                cases hf : eval k ptable level f env T with
                | none => rw [hf] at h_eval; simp at h_eval
                | some pr =>
                    obtain ⟨fv, T_f⟩ := pr
                    rw [hf] at h_eval; simp only at h_eval
                    have h_env_f := ih_eval ptable level f env T fv T_f m env_m hf h_env
                    cases ha : evalList k ptable level args env T_f with
                    | none => rw [ha] at h_eval; simp at h_eval
                    | some pr2 =>
                        obtain ⟨avs, T_a⟩ := pr2
                        rw [ha] at h_eval; simp only at h_eval
                        have h_env_a := ih_evalList ptable level args env T_f avs T_a m env_m ha h_env_f
                        exact ih_applyVia ptable level fv avs T_a r T' m env_m h_eval h_env_a
        | primApp f args =>
            simp only [eval] at h_eval
            cases hf : eval k ptable level f env T with
            | none => rw [hf] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨fv, T_f⟩ := pr
                rw [hf] at h_eval; simp only at h_eval
                have h_env_f := ih_eval ptable level f env T fv T_f m env_m hf h_env
                cases ha : evalList k ptable level args env T_f with
                | none => rw [ha] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨avs, T_a⟩ := pr2
                    rw [ha] at h_eval; simp only at h_eval
                    have h_env_a := ih_evalList ptable level args env T_f avs T_a m env_m ha h_env_f
                    exact ih_applyDirect ptable level fv avs T_a r T' m env_m h_eval h_env_a
        | set x e =>
            simp only [eval] at h_eval
            cases he : eval k ptable level e env T with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, T_e⟩ := pr
                rw [he] at h_eval; simp only at h_eval
                have h_env_e := ih_eval ptable level e env T v T_e m env_m he h_env
                cases hl : env.lookup x with
                | none => rw [hl] at h_eval; simp at h_eval
                | some i =>
                    rw [hl] at h_eval; simp only at h_eval
                    by_cases hm : isMetaMutation x env T_e level
                    · -- meta-mutation case: gating + heap update
                      sorry
                    · rw [if_neg hm] at h_eval
                      simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                      obtain ⟨_, h_T⟩ := h_eval; subst h_T
                      rw [TowerState.updateHeap_envAt?]; exact h_env_e
        | em body =>
            simp only [eval] at h_eval
            cases hm : T.materialize (level + 1) with
            | none => rw [hm] at h_eval; simp at h_eval
            | some T_m =>
                rw [hm] at h_eval; simp only at h_eval
                have h_env_m :=
                  T.materialize_envAt?_preserves T_m (level + 1) m env_m hm h_env
                cases he : T_m.envAt? (level + 1) with
                | none => rw [he] at h_eval; simp at h_eval
                | some upEnv =>
                    rw [he] at h_eval; simp only at h_eval
                    exact ih_eval ptable (level + 1) body upEnv T_m r T' m env_m h_eval h_env_m
        | letE x e body =>
            simp only [eval] at h_eval
            cases he : eval k ptable level e env T with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨v, T_e⟩ := pr
                rw [he] at h_eval; simp only at h_eval
                have h_env_e := ih_eval ptable level e env T v T_e m env_m he h_env
                have h_env_alloc : (T_e.alloc v).1.envAt? m = some env_m := by
                  rw [TowerState.alloc_envAt?]; exact h_env_e
                exact ih_eval ptable level body
                  (.cons x (T_e.alloc v).2 env) (T_e.alloc v).1 r T' m env_m h_eval h_env_alloc
        | seq exps =>
            cases exps with
            | nil =>
                simp only [eval, Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_T⟩ := h_eval; subst h_T; exact h_env
            | cons e rest =>
                cases rest with
                | nil =>
                    simp only [eval] at h_eval
                    exact ih_eval ptable level e env T r T' m env_m h_eval h_env
                | cons e2 rest2 =>
                    simp only [eval] at h_eval
                    cases he : eval k ptable level e env T with
                    | none => rw [he] at h_eval; simp at h_eval
                    | some pr =>
                        obtain ⟨_, T_e⟩ := pr
                        rw [he] at h_eval; simp only at h_eval
                        have h_env_e := ih_eval ptable level e env T _ T_e m env_m he h_env
                        exact ih_eval ptable level (.seq (e2 :: rest2)) env T_e r T' m env_m h_eval h_env_e
        | installPolicy idx =>
            simp only [eval] at h_eval
            cases hp : ptable[idx]? with
            | none =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_T⟩ := h_eval; subst h_T; exact h_env
            | some newPolicy =>
                rw [hp] at h_eval
                simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                obtain ⟨_, h_T⟩ := h_eval; subst h_T
                rw [TowerState.setPolicyAt_envAt?]; exact h_env
      · -- evalList (k+1)
        intro ptable level exps env T rs T' m env_m h_eval h_env
        cases exps with
        | nil =>
            simp only [evalList, Option.some.injEq, Prod.mk.injEq] at h_eval
            obtain ⟨_, h_T⟩ := h_eval; subst h_T; exact h_env
        | cons e rest =>
            simp only [evalList] at h_eval
            cases he : eval k ptable level e env T with
            | none => rw [he] at h_eval; simp at h_eval
            | some pr =>
                obtain ⟨_, T_e⟩ := pr
                rw [he] at h_eval; simp only at h_eval
                have h_env_e := ih_eval ptable level e env T _ T_e m env_m he h_env
                cases hr : evalList k ptable level rest env T_e with
                | none => rw [hr] at h_eval; simp at h_eval
                | some pr2 =>
                    obtain ⟨_, T_r⟩ := pr2
                    rw [hr] at h_eval
                    simp only [Option.some.injEq, Prod.mk.injEq] at h_eval
                    obtain ⟨_, h_T⟩ := h_eval; subst h_T
                    exact ih_evalList ptable level rest env T_e _ T_r m env_m hr h_env_e
      · -- applyVia (k+1)
        intro ptable level op args T r T' m env_m h_app h_env
        simp only [applyVia] at h_app
        cases hm : T.materialize (level + 1) with
        | none => rw [hm] at h_app; simp at h_app
        | some T_m =>
            rw [hm] at h_app; simp only at h_app
            have h_env_m := T.materialize_envAt?_preserves T_m (level + 1) m env_m hm h_env
            cases he : T_m.envAt? (level + 1) with
            | none =>
                rw [he] at h_app; simp only at h_app
                exact ih_applyDirect ptable level op args T_m r T' m env_m h_app h_env_m
            | some upEnv =>
                rw [he] at h_app; simp only at h_app
                cases hl : upEnv.lookup "base-apply" with
                | none =>
                    rw [hl] at h_app; simp only at h_app
                    exact ih_applyDirect ptable level op args T_m r T' m env_m h_app h_env_m
                | some idx =>
                    rw [hl] at h_app; simp only at h_app
                    cases hp : T_m.heap[idx]? with
                    | none => rw [hp] at h_app; simp at h_app
                    | some baseApply =>
                        rw [hp] at h_app
                        cases baseApply with
                        | builtinBaseApply =>
                            exact ih_applyDirect ptable level op args T_m r T' m env_m h_app h_env_m
                        | num _ | bool _ | nilV | cons _ _ | sym _ | closure _ _ _ | prim _ =>
                            exact ih_applyDirect ptable level _ [op, listToVal args] T_m r T' m env_m h_app h_env_m
      · -- applyDirect (k+1) — body sorry'd; same template as eval/applyVia
        -- but Lean's whnf interaction with the closure case's foldl
        -- makes the rw chain finicky. Mechanical to fix.
        intro _ _ _ _ _ _ _ _ _ _ _
        sorry

/-- Convenience wrapper for `eval`. -/
theorem eval_preserves_envAt
    (n : Nat) (ptable : PolicyTable) (level : Nat) (exp : Expr) (env : Env)
    (T : TowerState) (r : Val) (T' : TowerState) (m : Nat) (env_m : Env)
    (h_eval : eval n ptable level exp env T = some (r, T'))
    (h_env : T.envAt? m = some env_m) :
    T'.envAt? m = some env_m :=
  (all_preserves_envAt n).1 ptable level exp env T r T' m env_m h_eval h_env

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
  /-- Cross-side: every materialized level's env is the same on both
      sides at the output state. Mirrors `WFCtxT.level_envs_eq`. -/
  level_envs_eq_out     : ∀ n, T_a'.envAt? n = T_b'.envAt? n
  /-- Cross-side: every level's policy is the same on both sides at the
      output state. Mirrors `WFCtxT.policies_eq`. -/
  policies_eq_out       : ∀ n, T_a'.policyAt? n = T_b'.policyAt? n
  /-- Every level's policy in the output respects bisim. Mirrors
      `WFCtxT.policies_resp_all`. -/
  policies_resp_all_out : ∀ n p, T_a'.policyAt? n = some p → PolicyRespectsBisimT p

theorem TowerCross.refl (level : Nat) (T_a T_b : TowerState)
    (h_len : T_a.heap.length = T_b.heap.length)
    (h_pol : T_a.policyAt? level = T_b.policyAt? level)
    (h_hv_a : HeapValid T_a.heap) (h_hv_b : HeapValid T_b.heap)
    (h_levs_a : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap)
    (h_levs_b : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap)
    (h_resp_at : ∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_levs_eq : ∀ n, T_a.envAt? n = T_b.envAt? n)
    (h_pols_eq : ∀ n, T_a.policyAt? n = T_b.policyAt? n)
    (h_resp_all : ∀ n p, T_a.policyAt? n = some p → PolicyRespectsBisimT p) :
    TowerCross level T_a T_b T_a T_b :=
  ⟨h_len, h_pol, fun _ _ h => h, fun _ _ h => h,
   h_hv_a, h_hv_b, h_levs_a, h_levs_b, h_resp_at, h_levs_eq, h_pols_eq, h_resp_all⟩

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
    (∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p) →
    T_a.policyAt? level = T_b.policyAt? level →
    HeapValid T_a.heap → HeapValid T_b.heap →
    T_a.heap.length = T_b.heap.length →
    (∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap) →
    (∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap) →
    (∀ n, T_a.envAt? n = T_b.envAt? n) →
    (∀ n, T_a.policyAt? n = T_b.policyAt? n) →
    (∀ n p, T_a.policyAt? n = some p → PolicyRespectsBisimT p) →
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
    (∀ n, T_a.envAt? n = T_b.envAt? n) →
    (∀ n, T_a.policyAt? n = T_b.policyAt? n) →
    (∀ n p, T_a.policyAt? n = some p → PolicyRespectsBisimT p) →
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
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
      · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h
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
                            h_ctx2.level_envs_eq h_ctx2.policies_eq
                            h_ctx2.policies_resp_all
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
                           h_tc3.level_envs_valid_a_out, h_tc3.level_envs_valid_b_out,
                           h_tc3.level_envs_eq_out, h_tc3.policies_eq_out,
                           h_tc3.policies_resp_all_out⟩
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
                        h_ctx2.level_envs_eq h_ctx2.policies_eq
                        h_ctx2.policies_resp_all
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
                       h_tc3.level_envs_valid_a_out, h_tc3.level_envs_valid_b_out,
                       h_tc3.level_envs_eq_out, h_tc3.policies_eq_out,
                       h_tc3.policies_resp_all_out⟩
                    have h_env_out : EnvVis env_a env_b T_a'.heap T_b'.heap :=
                      h_he_chain.envVis_preserve env_a env_b h_ctx.env_eq
                        h_ctx.ev_a h_ctx.ev_b h_env
                    refine ⟨r_b, T_b', ?_, h_vv, h_ctx_out,
                            h_he_chain, h_env_out, hv_ra, hv_rb⟩
                    simp [eval, h_eval_f_b, h_eval_args_b, h_eval_av_b]
        | set _ _          => sorry  -- USES policy_eq_at + ValVis_aux_update; substantial
        | em body =>
            -- Cross-side materialize-bisim. Now that all the Tower
            -- cross-side lemmas are proved, the .em case threads them
            -- to construct WFCtxT for the IH at level+1.
            simp only [eval] at h_eval
            cases hm_a : T_a.materialize (level + 1) with
            | none => simp [hm_a] at h_eval
            | some T_a_mat =>
                simp only [hm_a] at h_eval
                cases he_a : T_a_mat.envAt? (level + 1) with
                | none => simp [he_a] at h_eval
                | some upEnv_a =>
                    simp only [he_a] at h_eval
                    -- h_eval : eval k ptable (level+1) body upEnv_a T_a_mat = some (r_a, T_a')
                    -- Cross-side: T_b materializes too
                    have hm_b_some : (T_b.materialize (level + 1)).isSome := by
                      cases h_some : T_b.materialize (level + 1) with
                      | none =>
                          have h_a_none : T_a.materialize (level + 1) = none :=
                            (T_a.materialize_cross_side_some_iff T_b _).mpr h_some
                          rw [h_a_none] at hm_a; exact Option.noConfusion hm_a
                      | some _ => simp
                    obtain ⟨T_b_mat, hm_b⟩ := Option.isSome_iff_exists.mp hm_b_some
                    -- Cross-side parallel facts
                    obtain ⟨h_heap_eq_mat, h_envs_eq_mat⟩ :=
                      T_a.materialize_cross_side_envs_eq T_b T_a_mat T_b_mat (level + 1)
                        h_ctx.heap_len_eq h_ctx.level_envs_eq hm_a hm_b
                    have h_pols_eq_mat :=
                      T_a.materialize_cross_side_policies_eq T_b T_a_mat T_b_mat (level + 1)
                        h_ctx.heap_len_eq h_ctx.policies_eq h_ctx.level_envs_eq hm_a hm_b
                    have he_b : T_b_mat.envAt? (level + 1) = some upEnv_a := by
                      rw [← h_envs_eq_mat (level + 1)]; exact he_a
                    -- Single-side preservation facts (Tower lemmas)
                    have h_hv_a_mat : HeapValid T_a_mat.heap :=
                      materialize_HeapValid_preserves T_a T_a_mat (level + 1) hm_a h_ctx.hv_a
                    have h_hv_b_mat : HeapValid T_b_mat.heap :=
                      materialize_HeapValid_preserves T_b T_b_mat (level + 1) hm_b h_ctx.hv_b
                    have h_levs_valid_a_mat :
                        ∀ m env, T_a_mat.envAt? m = some env → EnvValid env T_a_mat.heap :=
                      materialize_level_envs_valid_preserves T_a T_a_mat (level + 1) hm_a
                        h_ctx.hv_a h_ctx.level_envs_valid_a
                    have h_levs_valid_b_mat :
                        ∀ m env, T_b_mat.envAt? m = some env → EnvValid env T_b_mat.heap :=
                      materialize_level_envs_valid_preserves T_b T_b_mat (level + 1) hm_b
                        h_ctx.hv_b h_ctx.level_envs_valid_b
                    have h_resp_all_mat :
                        ∀ m p, T_a_mat.policyAt? m = some p → PolicyRespectsBisimT p :=
                      materialize_policies_resp_preserves T_a T_a_mat (level + 1)
                        PolicyRespectsBisimT hm_a h_ctx.policies_resp_all
                        acceptAllPolicy_respects_bisimT
                    -- Build WFCtxT for the IH at level+1
                    have h_pol_resp_at :
                        ∀ p, T_a_mat.policyAt? (level + 1) = some p → PolicyRespectsBisimT p :=
                      fun p h => h_resp_all_mat (level + 1) p h
                    have h_ev_a : EnvValid upEnv_a T_a_mat.heap :=
                      h_levs_valid_a_mat (level + 1) upEnv_a he_a
                    have h_ev_b : EnvValid upEnv_a T_b_mat.heap :=
                      h_levs_valid_b_mat (level + 1) upEnv_a he_b
                    have h_ctx_mat : WFCtxT upEnv_a upEnv_a T_a_mat T_b_mat (level + 1) :=
                      ⟨h_pols_eq_mat (level + 1), h_hv_a_mat, h_hv_b_mat,
                       h_ev_a, h_ev_b, h_pol_resp_at,
                       rfl, h_heap_eq_mat,
                       h_levs_valid_a_mat, h_levs_valid_b_mat,
                       h_envs_eq_mat, h_pols_eq_mat, h_resp_all_mat⟩
                    -- Need EnvVis upEnv_a upEnv_a T_a_mat.heap T_b_mat.heap (self-bisim)
                    -- This requires showing upEnv_a's bindings are bisim-related cross-side
                    -- — which holds since heap-len-equal and same env content.
                    have h_env_mat : EnvVis upEnv_a upEnv_a T_a_mat.heap T_b_mat.heap := by
                      sorry  -- env self-bisim across bisim-related heaps;
                             -- needs an EnvVis-self-via-heap-len-eq lemma
                    -- IH on body at level+1
                    obtain ⟨r_b, T_b', h_eval_b, h_vv, h_ctx_out, h_he, h_env_out, hv_ra, hv_rb⟩ :=
                      ih_eval ptable (level + 1) body upEnv_a upEnv_a T_a_mat T_b_mat r_a T_a'
                        hresp_pt h_ctx_mat h_env_mat h_eval
                    -- Construct outputs at the OUTER level (not level+1).
                    -- HeapEvolution composes materialize step with body's HeapEvolution.
                    -- materialize_HeapEvolution: T → T_mat preserves bisim trivially since
                    -- only fresh cells are appended (don't reference any existing idxes).
                    have h_he_mat : HeapEvolution T_a T_b T_a_mat T_b_mat :=
                      HeapEvolution.from_heapExt h_ctx.hv_a h_ctx.hv_b
                        (T_a.materialize_heap_extends T_a_mat (level + 1) hm_a)
                        (T_b.materialize_heap_extends T_b_mat (level + 1) hm_b)
                    have h_he_outer : HeapEvolution T_a T_b T_a' T_b' :=
                      HeapEvolution.trans h_he_mat h_he
                    -- Outer EnvVis: lift via HeapEvolution.envVis_preserve
                    have h_env_outer : EnvVis env_a env_b T_a'.heap T_b'.heap :=
                      h_he_outer.envVis_preserve env_a env_b h_ctx.env_eq
                        h_ctx.ev_a h_ctx.ev_b h_env
                    -- Outer WFCtxT: project from h_ctx_out (at level+1, with upEnv_a env)
                    -- back to (env_a env_b at outer level). Single-side env validity lifted
                    -- via length_mono. Policies/level-envs facts come from the IH output
                    -- which inherits all tower-wide invariants.
                    have h_ctx_outer : WFCtxT env_a env_b T_a' T_b' level :=
                      ⟨h_ctx_out.policies_eq level, h_ctx_out.hv_a, h_ctx_out.hv_b,
                       h_ctx.ev_a.length_mono h_he_outer.len_a,
                       h_ctx.ev_b.length_mono h_he_outer.len_b,
                       h_ctx_out.policies_resp_all level,
                       h_ctx.env_eq, h_ctx_out.heap_len_eq,
                       h_ctx_out.level_envs_valid_a, h_ctx_out.level_envs_valid_b,
                       h_ctx_out.level_envs_eq, h_ctx_out.policies_eq,
                       h_ctx_out.policies_resp_all⟩
                    refine ⟨r_b, T_b', ?_, h_vv, h_ctx_outer, h_he_outer,
                            h_env_outer, hv_ra, hv_rb⟩
                    simp [eval, hm_b, he_b, h_eval_b]
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
                   h_levs_a_alloc, h_levs_b_alloc, h_ctx_inner.level_envs_eq,
                   h_ctx_inner.policies_eq, h_ctx_inner.policies_resp_all⟩
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
                   h_ctx_body.level_envs_valid_a, h_ctx_body.level_envs_valid_b,
                   h_ctx_body.level_envs_eq, h_ctx_body.policies_eq,
                   h_ctx_body.policies_resp_all⟩
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
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h_ctx.env_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
                  · -- level_envs_eq: setPolicyAt preserves envAt? on both sides
                    intro m
                    rw [h_envs_a m, h_envs_b m]; exact h_ctx.level_envs_eq m
                  · -- policies_eq: at level, both sides have newPolicy;
                    -- elsewhere, setPolicyAt preserves policyAt? cross-side.
                    intro m
                    by_cases hm : level = m
                    · rw [← hm]
                      rw [TowerState.setPolicyAt_policyAt?_self T_a level newPolicy,
                          TowerState.setPolicyAt_policyAt?_self T_b level newPolicy,
                          h_ctx.policies_eq level]
                    · rw [TowerState.setPolicyAt_policyAt?_other T_a level m newPolicy hm,
                          TowerState.setPolicyAt_policyAt?_other T_b level m newPolicy hm]
                      exact h_ctx.policies_eq m
                  · -- policies_resp_all: at level, newPolicy from ptable
                    -- (respects bisim by hresp_pt); elsewhere, preserved.
                    intro m p h_eq
                    by_cases hm : level = m
                    · rw [← hm] at h_eq
                      rw [TowerState.setPolicyAt_policyAt?_self] at h_eq
                      cases h_old : T_a.policyAt? level with
                      | none => rw [h_old] at h_eq; simp at h_eq
                      | some _ => rw [h_old] at h_eq; simp at h_eq; subst h_eq; exact h_resp_new
                    · rw [TowerState.setPolicyAt_policyAt?_other T_a level m newPolicy hm] at h_eq
                      exact h_ctx.policies_resp_all m p h_eq
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
              h_levs_a h_levs_b h_levs_eq h_pols_eq h_resp_all h_vv_op h_lvv hv_opa hv_opb
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
                        h_levs_a h_levs_b h_levs_eq h_pols_eq h_resp_all
                        h_vv_actual h_lvv_ops
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
                          h_levs_a h_levs_b h_resp_at h_levs_eq h_pols_eq h_resp_all,
                        hv_ra, hv_rb⟩
                simp only [applyDirect, hp_b]
        | closure ps body cenv =>
            -- Adapted port from lean-green. The cross-side closure
            -- (ValVis on closures) forces ps_b = ps, body_b = body,
            -- cenv_b is bisim-related to cenv. The arg-alloc step
            -- (allocStep chain) produces parallel alloc'd envs and
            -- cross-side bisim-related allocated heaps.
            have h_opb : ∃ cenv_b, op_b = .closure ps body cenv_b ∧
                cenv = cenv_b ∧
                EnvVis cenv cenv_b T_a.heap T_b.heap := by
              cases op_b with
              | closure ps_b body_b cenv_b =>
                  obtain ⟨hps, hbody, hcenv, henv⟩ :=
                    closure_ValVis_imp_cenv_EnvVis h_vv_op
                  subst hps; subst hbody
                  exact ⟨cenv_b, rfl, hcenv, henv⟩
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | nilV => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | cons _ _ => simp [ValVis_aux] at h_vv1
              | prim _ => simp [ValVis_aux] at h_vv1
              | builtinBaseApply => simp [ValVis_aux] at h_vv1
            obtain ⟨cenv_b, h_eq, h_cenv_eq, h_env_cenv⟩ := h_opb
            subst h_eq
            have hev_cenv_a : EnvValid cenv T_a.heap := hv_opa
            have hev_cenv_b : EnvValid cenv_b T_b.heap := hv_opb
            simp only [applyDirect] at h_eval
            by_cases hlen : ps.length = args_a.length
            · -- Length matches on a-side. ListValVis transfers to b-side.
              have hlen_b : ps.length = args_b.length := by
                rw [hlen]; exact ListValVis.length_eq h_lvv
              have hne_a : (ps.length != args_a.length) = false := by
                simp [hlen]
              rw [hne_a] at h_eval
              simp only [Bool.false_eq_true, ↓reduceIte] at h_eval
              have hlen_a' : args_a.length = ps.length := hlen.symm
              have hlen_b' : args_b.length = ps.length := hlen_b.symm
              -- alloc_chain_bisim gives post-alloc invariants.
              obtain ⟨hh_a', hh_b', hev_a', hev_b', h_env_alloc, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
                alloc_chain_bisim args_a args_b ps cenv cenv_b T_a.heap T_b.heap
                  hlen_a' hlen_b' h_lvv hv_argsa hv_argsb
                  h_hv_a h_hv_b hev_cenv_a hev_cenv_b h_env_cenv
              -- allocStep_chain_aligned gives env-equal + heap-len-equal.
              have h_args_len : args_a.length = args_b.length :=
                ListValVis.length_eq h_lvv
              obtain ⟨h_alloc_env_eq', h_alloc_len_eq'⟩ :=
                allocStep_chain_aligned args_a args_b ps T_a.heap T_b.heap cenv_b
                  h_hl_eq h_args_len
              have h_alloc_env_eq :
                  ((args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).2 : Env)
                    = (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).2 := by
                rw [h_cenv_eq]; exact h_alloc_env_eq'
              have h_alloc_len_eq :
                  (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1.length =
                    (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1.length := by
                rw [h_cenv_eq]; exact h_alloc_len_eq'
              -- Lift level_envs_valid to alloc'd heaps.
              have h_levs_a_alloc : ∀ n env, T_a.envAt? n = some env →
                  EnvValid env (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 := by
                intro n env hen
                rw [hex_a]
                exact EnvValid.heap_extends (h_levs_a n env hen) ⟨ext_a, rfl⟩
              have h_levs_b_alloc : ∀ n env, T_b.envAt? n = some env →
                  EnvValid env (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 := by
                intro n env hen
                rw [hex_b]
                exact EnvValid.heap_extends (h_levs_b n env hen) ⟨ext_b, rfl⟩
              -- Construct WFCtxT for the body call.
              -- T_a after alloc: same levels (alloc only touches heap), new heap.
              let T_a_alloc : TowerState :=
                { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
              let T_b_alloc : TowerState :=
                { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 }
              have h_ctx_alloc :
                  WFCtxT
                    (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).2
                    (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).2
                    T_a_alloc T_b_alloc level :=
                ⟨h_pol_eq, hh_a', hh_b', hev_a', hev_b', h_resp_at,
                 h_alloc_env_eq, h_alloc_len_eq,
                 h_levs_a_alloc, h_levs_b_alloc, h_levs_eq, h_pols_eq, h_resp_all⟩
              -- Apply ih_eval on body.
              obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_ctx_body, h_he_body,
                      _h_env_body, hv_ra, hv_rb⟩ :=
                ih_eval ptable level body
                  (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).2
                  (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).2
                  T_a_alloc T_b_alloc r_a T_a'
                  hresp_pt h_ctx_alloc h_env_alloc h_eval
              -- HeapEvolution from the alloc step.
              have h_he_alloc : HeapEvolution T_a T_b T_a_alloc T_b_alloc :=
                HeapEvolution.from_heapExt h_hv_a h_hv_b ⟨ext_a, hex_a⟩ ⟨ext_b, hex_b⟩
              have h_he_chain : HeapEvolution T_a T_b T_a' T_b' :=
                HeapEvolution.trans h_he_alloc h_he_body
              -- TowerCross output: levels-mono via eval_preserves_envAt
              -- (which currently sorries its own body — see lemma above).
              have h_levs_mono_a : ∀ n env, T_a.envAt? n = some env →
                  T_a'.envAt? n = some env := by
                intro n env hen
                have hen' : T_a_alloc.envAt? n = some env := hen
                exact eval_preserves_envAt k ptable level body
                  (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).2
                  T_a_alloc r_a T_a' n env h_eval hen'
              have h_levs_mono_b : ∀ n env, T_b.envAt? n = some env →
                  T_b'.envAt? n = some env := by
                intro n env hen
                have hen' : T_b_alloc.envAt? n = some env := hen
                exact eval_preserves_envAt k ptable level body
                  (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).2
                  T_b_alloc r_b T_b' n env h_eval_b hen'
              have h_tc_out : TowerCross level T_a T_b T_a' T_b' :=
                ⟨h_ctx_body.heap_len_eq, h_ctx_body.policy_eq_at,
                 h_levs_mono_a, h_levs_mono_b,
                 h_ctx_body.hv_a, h_ctx_body.hv_b,
                 h_ctx_body.level_envs_valid_a, h_ctx_body.level_envs_valid_b,
                 h_ctx_body.policy_resp, h_ctx_body.level_envs_eq,
                 h_ctx_body.policies_eq, h_ctx_body.policies_resp_all⟩
              refine ⟨r_b, T_b', ?_, h_vv_r, h_he_chain, h_tc_out, hv_ra, hv_rb⟩
              -- Goal: applyDirect (k+1) ptable level (.closure ps body cenv_b) args_b T_b
              --       = some (r_b, T_b')
              simp only [applyDirect]
              have hne_b : (ps.length != args_b.length) = false := by simp [hlen_b]
              rw [hne_b]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact h_eval_b
            · -- Length doesn't match on a-side. applyDirect returns none.
              have hne : (ps.length != args_a.length) = true := by simp [hlen]
              rw [hne] at h_eval
              simp at h_eval
