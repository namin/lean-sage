/-
  lean-black: Tower layer.

  The synthesis of lean-grey's `Nat → LevelState` and lean-green's
  `RunState`. Each level has its own env and policy; the heap is
  global (one backing store, level-allocated cells). The infinite
  tower exists conceptually; only finitely many levels are realized
  at runtime — `(em body)` materializes the next level on demand.

  ## Why one global heap, not per-level heaps

  Closures created at level N+1 (by `(em ...)`) can be `set!`-ed
  into level N's `base-apply` cell. When level N then invokes
  `applyVia`, level N+1's closure runs — and its captured env
  carries idxes that were valid when allocated at level N+1. With
  one global heap, those idxes stay valid no matter who invokes
  the closure from where. With per-level heaps, the closure's
  captures would point into the wrong heap on cross-level
  invocation, and "translation" would be intractable for nested
  closures.

  This is consistent with lean-green's stage-1 design — one heap,
  one cell-allocation discipline — generalized to multiple
  per-level envs and policies.

  ## First-order encoding (per DESIGN.md, decision 1)

  `levels : List LevelState` — index 0 = level 0, length is the
  materialized depth + 1. Materialization-on-demand grows the list
  with fresh defaults. Past `Tower.maxDepth`, growth is capped —
  running off the top is a hard failure mode analogous to fuel
  exhaustion.

  ## Per-level state

  - `env` — what's bound by name at this level (root env). Includes
    `base-apply` (so level (N-1)'s `applyVia` can look it up) plus
    the standard primitives. Each level gets *its own* cells for
    these bindings, freshly allocated when the level materializes —
    so a `(set! +)` at one level does not leak across levels.
  - `policy` — gates mutations *happening at* this level. At level
    N (for N > 0) these are visible to level (N-1) via `applyVia`.
    For N = 0 the policy can still be used (e.g., to lock down
    base-level rewiring); the architectural story is uniform.

  Per DESIGN.md decision 4, `(installPolicy n)` at level N replaces
  `levels[N].policy` (governing future mutations at level N).
-/

import LeanBlack.Black

structure LevelState where
  env    : Env
  policy : BlackPolicy

structure TowerState where
  heap   : Heap
  levels : List LevelState

/-- Maximum number of materialized levels. A practical bound — past
    this, `(em ...)` returns `none`, just like fuel exhaustion.
    The infinite tower is the limit; the runtime materializes a
    finite prefix. -/
def Tower.maxDepth : Nat := 16

/-- The standard primitive bindings allocated by `freshLevelEnv`.
    Marked `@[irreducible]` so Lean's `whnf` doesn't try to normalize
    the 13-element list during proofs about `freshLevelEnv` (which would
    otherwise time out). The proofs use the foldl helpers parametrically
    in `pairs`, so they don't need `primPairs`'s explicit content. -/
@[irreducible]
def primPairs : List (String × Val) :=
  [ ("+",        .prim "+")
  , ("-",        .prim "-")
  , ("*",        .prim "*")
  , ("=",        .prim "=")
  , ("num?",     .prim "num?")
  , ("bool?",    .prim "bool?")
  , ("closure?", .prim "closure?")
  , ("prim?",    .prim "prim?")
  , ("cons",     .prim "cons")
  , ("car",      .prim "car")
  , ("cdr",      .prim "cdr")
  , ("null?",    .prim "null?")
  , ("mul-list", .prim "mul-list")
  ]

theorem primPairs_length : primPairs.length = 13 := by
  unfold primPairs; rfl

/-- Allocate a fresh "level" worth of cells in the heap: one cell
    per standard primitive plus a `base-apply` cell. Returns the
    extended heap and the env for the new level. -/
def freshLevelEnv (h : Heap) : Heap × Env :=
  let (h', envPrims) :=
    primPairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        let (hh, ee) := acc
        let (hh', idx) := hh.alloc kv.2
        (hh', .cons kv.1 idx ee))
      (h, .nil)
  let (h'', baseIdx) := h'.alloc .builtinBaseApply
  (h'', .cons "base-apply" baseIdx envPrims)

/-- Build a tower with `n` materialized levels, allocating cells in
    a fresh heap. -/
def buildTower (n : Nat) : TowerState :=
  let init : TowerState := { heap := [], levels := [] }
  Nat.fold n (fun _ _ T =>
    let (h', env) := freshLevelEnv T.heap
    { heap := h', levels := T.levels ++ [{ env := env, policy := acceptAllPolicy }] })
    init

/-- The level-0 starting tower: just level 0 materialized. -/
def initTower : TowerState := buildTower 1

/-- The level-0 user env (entry point). -/
def initUserEnv (T : TowerState) : Env :=
  match T.levels[0]? with
  | some ls => ls.env
  | none    => .nil  -- unreachable for `initTower`

/-! ## Materialization and accessors -/

/-- The fold step that materialize applies one or more times.
    Defined here so the lemmas about `materialize` can refer to it
    by name (rather than to an anonymous lambda inside the `fold`). -/
def materializeStep (T : TowerState) : TowerState :=
  let (h', env) := freshLevelEnv T.heap
  { heap := h', levels := T.levels ++ [{ env := env, policy := acceptAllPolicy }] }

/-- Ensure level `n` is materialized in `T`. Returns the (potentially
    extended) tower, or `none` if `n ≥ maxDepth`. -/
def TowerState.materialize (T : TowerState) (n : Nat) : Option TowerState :=
  if n ≥ Tower.maxDepth then none
  else if T.levels.length > n then some T
  else
    let needed := n + 1 - T.levels.length
    let extended : TowerState :=
      Nat.fold needed (fun _ _ T' => materializeStep T') T
    some extended

/-- Look up level `n`'s state. Returns `none` only if not
    materialized — ensure first. -/
def TowerState.levelAt? (T : TowerState) (n : Nat) : Option LevelState :=
  T.levels[n]?

def TowerState.envAt? (T : TowerState) (n : Nat) : Option Env :=
  (T.levelAt? n).map (·.env)

def TowerState.policyAt? (T : TowerState) (n : Nat) : Option BlackPolicy :=
  (T.levelAt? n).map (·.policy)

/-- Replace level `n`'s state. -/
def TowerState.setLevel (T : TowerState) (n : Nat) (ls : LevelState) : TowerState :=
  { T with levels := T.levels.set n ls }

/-- Replace level `n`'s policy (used by `installPolicy`). -/
def TowerState.setPolicyAt (T : TowerState) (n : Nat) (p : BlackPolicy) : TowerState :=
  match T.levelAt? n with
  | some ls => T.setLevel n { ls with policy := p }
  | none    => T

/-- Update a heap cell directly. -/
def TowerState.updateHeap (T : TowerState) (idx : Nat) (v : Val) : TowerState :=
  { T with heap := T.heap.update idx v }

/-- Allocate a new heap cell, returning the extended tower and the
    new index. -/
def TowerState.alloc (T : TowerState) (v : Val) : TowerState × Nat :=
  let (h', idx) := T.heap.alloc v
  ({ T with heap := h' }, idx)

/-! ## Allocation step (closure-call foldl body)

    Pure `(Heap, Env)`-level helper used by both the runtime's
    `applyDirect` closure case (in `Eval.lean`) and the framing
    proof's alloc-chain reasoning (in `Bisim.lean` /
    `Frame.lean`). Putting it here keeps `Eval` and `Bisim`
    aligned on the same definition. -/
def allocStep (acc : Heap × Env) (vp : Val × String) : Heap × Env :=
  let (hh, ee) := acc
  let (hh', idx) := hh.alloc vp.1
  (hh', .cons vp.2 idx ee)

/-! ## Foundational lemmas about Tower mutations

    Used by Frame.lean to discharge cross-side WFCtxT preservation
    across `setPolicyAt`, `updateHeap`, and `alloc` operations. -/

/-! ### `setPolicyAt` lemmas -/

theorem TowerState.setPolicyAt_heap (T : TowerState) (n : Nat) (p : BlackPolicy) :
    (T.setPolicyAt n p).heap = T.heap := by
  unfold setPolicyAt; split <;> rfl

theorem TowerState.setPolicyAt_levels_length (T : TowerState) (n : Nat) (p : BlackPolicy) :
    (T.setPolicyAt n p).levels.length = T.levels.length := by
  unfold setPolicyAt
  split
  · simp [setLevel, List.length_set]
  · rfl

theorem TowerState.setPolicyAt_envAt? (T : TowerState) (n m : Nat) (p : BlackPolicy) :
    (T.setPolicyAt n p).envAt? m = T.envAt? m := by
  unfold setPolicyAt setLevel envAt? levelAt?
  split
  · rename_i ls h_ls
    by_cases hnm : n = m
    · subst hnm
      have h_lt : n < T.levels.length := List.getElem?_eq_some_iff.mp h_ls |>.1
      rw [List.getElem?_set_self h_lt, h_ls]
      rfl
    · rw [List.getElem?_set_ne hnm]
  · rfl

theorem TowerState.setPolicyAt_policyAt?_self (T : TowerState) (n : Nat) (p : BlackPolicy) :
    (T.setPolicyAt n p).policyAt? n = (T.policyAt? n).map (fun _ => p) := by
  unfold setPolicyAt setLevel policyAt? levelAt?
  split
  · rename_i ls h_ls
    have h_lt : n < T.levels.length := List.getElem?_eq_some_iff.mp h_ls |>.1
    rw [List.getElem?_set_self h_lt, h_ls]
    rfl
  · rename_i h_none
    rw [h_none]
    rfl

theorem TowerState.setPolicyAt_policyAt?_other (T : TowerState) (n m : Nat) (p : BlackPolicy)
    (h : n ≠ m) :
    (T.setPolicyAt n p).policyAt? m = T.policyAt? m := by
  unfold setPolicyAt setLevel policyAt? levelAt?
  split
  · rw [List.getElem?_set_ne h]
  · rfl

/-! ### `updateHeap` lemmas -/

theorem TowerState.updateHeap_levels (T : TowerState) (idx : Nat) (v : Val) :
    (T.updateHeap idx v).levels = T.levels := by rfl

theorem TowerState.updateHeap_policyAt? (T : TowerState) (idx : Nat) (v : Val) (n : Nat) :
    (T.updateHeap idx v).policyAt? n = T.policyAt? n := by rfl

theorem TowerState.updateHeap_envAt? (T : TowerState) (idx : Nat) (v : Val) (n : Nat) :
    (T.updateHeap idx v).envAt? n = T.envAt? n := by rfl

/-! ### `alloc` lemmas -/

theorem TowerState.alloc_levels (T : TowerState) (v : Val) :
    (T.alloc v).1.levels = T.levels := by rfl

theorem TowerState.alloc_policyAt? (T : TowerState) (v : Val) (n : Nat) :
    (T.alloc v).1.policyAt? n = T.policyAt? n := by rfl

theorem TowerState.alloc_envAt? (T : TowerState) (v : Val) (n : Nat) :
    (T.alloc v).1.envAt? n = T.envAt? n := by rfl

/-! ### `materialize` lemmas -/

/-- After k applications of the fold step, levels has the original prefix
    extended by k new levels. -/
private theorem materializeStep_iter_levels_prefix (T : TowerState) (k : Nat) :
    ∃ extra : List LevelState,
      (Nat.fold k (fun _ _ T' => materializeStep T') T).levels = T.levels ++ extra ∧
      extra.length = k := by
  induction k with
  | zero =>
      refine ⟨[], ?_, ?_⟩
      · simp [Nat.fold]
      · rfl
  | succ k ih =>
      obtain ⟨extras, h_eq, h_len⟩ := ih
      simp only [Nat.fold]
      let T_k := Nat.fold k (fun _ _ T' => materializeStep T') T
      let new_ls : LevelState :=
        { env := (freshLevelEnv T_k.heap).2, policy := acceptAllPolicy }
      refine ⟨extras ++ [new_ls], ?_, ?_⟩
      · show (materializeStep T_k).levels = T.levels ++ (extras ++ [new_ls])
        unfold materializeStep
        show T_k.levels ++ [new_ls] = T.levels ++ (extras ++ [new_ls])
        rw [h_eq, List.append_assoc]
      · simp [List.length_append, h_len]

/-- `freshLevelEnv` only grows the heap. -/
private theorem freshLevelEnv_heap_grows (h : Heap) :
    h.length ≤ (freshLevelEnv h).1.length := by
  -- freshLevelEnv = (buildBindings-foldl over 13 prims) >>= alloc builtinBaseApply
  -- Each step appends one cell. Just trace through.
  unfold freshLevelEnv
  simp only [Heap.alloc, List.length_append, List.length_singleton]
  -- After buildBindings, heap is h ++ [13 prim cells]. Then alloc baseApply
  -- appends one more. So final length = h.length + 14 ≥ h.length.
  -- Use foldl_induction: each step preserves "length ≥ original".
  have h_inner : ∀ (pairs : List (String × Val)) (acc : Heap × Env),
      acc.1.length ≤ (pairs.foldl
        (fun (a : Heap × Env) (kv : String × Val) =>
          let (hh, ee) := a
          let (hh', idx) := hh.alloc kv.2
          (hh', .cons kv.1 idx ee)) acc).1.length := by
    intro pairs
    induction pairs with
    | nil => intro acc; simp [List.foldl]
    | cons p rest ih =>
        intro acc
        simp only [List.foldl]
        have h_step :
            acc.1.length ≤ (acc.1.alloc p.2).1.length := by
          simp [Heap.alloc, List.length_append]
        have h_rest := ih ((acc.1.alloc p.2).1, .cons p.1 (acc.1.alloc p.2).2 acc.2)
        exact Nat.le_trans h_step h_rest
  exact Nat.le_trans (h_inner _ (h, .nil)) (Nat.le_succ _)

/-- After k applications of the fold step, the heap grows monotonically. -/
private theorem materializeStep_iter_heap_grows (T : TowerState) (k : Nat) :
    T.heap.length ≤ (Nat.fold k (fun _ _ T' => materializeStep T') T).heap.length := by
  induction k with
  | zero => simp [Nat.fold]
  | succ k ih =>
      simp only [Nat.fold]
      have h_step : (Nat.fold k (fun _ _ T' => materializeStep T') T).heap.length
          ≤ (materializeStep (Nat.fold k (fun _ _ T' => materializeStep T') T)).heap.length := by
        unfold materializeStep
        exact freshLevelEnv_heap_grows _
      exact Nat.le_trans ih h_step

/-- `materialize` only appends new levels — existing levels (and so
    their envs) are preserved. -/
theorem TowerState.materialize_envAt?_preserves
    (T T' : TowerState) (n m : Nat) (env : Env)
    (h_mat : T.materialize n = some T')
    (h_env : T.envAt? m = some env) :
    T'.envAt? m = some env := by
  unfold materialize at h_mat
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat
  · simp [h1] at h_mat
    by_cases h2 : T.levels.length > n
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact h_env
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      -- Goal: (Nat.fold ... T).envAt? m = some env
      have h_lt : m < T.levels.length := by
        unfold envAt? levelAt? at h_env
        cases hh : T.levels[m]? with
        | none => rw [hh] at h_env; simp at h_env
        | some _ => exact List.getElem?_eq_some_iff.mp hh |>.1
      obtain ⟨extras, h_lvl_eq, _⟩ :=
        materializeStep_iter_levels_prefix T (n + 1 - T.levels.length)
      unfold envAt? levelAt?
      rw [h_lvl_eq]
      have : (T.levels ++ extras)[m]? = T.levels[m]? :=
        List.getElem?_append_left h_lt
      rw [this]
      exact h_env

/-- `materialize` only grows the heap. -/
theorem TowerState.materialize_heap_grows
    (T T' : TowerState) (n : Nat)
    (h_mat : T.materialize n = some T') :
    T.heap.length ≤ T'.heap.length := by
  unfold materialize at h_mat
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat
  · simp [h1] at h_mat
    by_cases h2 : T.levels.length > n
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact Nat.le_refl _
    · simp [h2] at h_mat
      obtain rfl := h_mat.symm
      exact materializeStep_iter_heap_grows T (n + 1 - T.levels.length)

/-! ### `freshLevelEnv` content lemmas

    Used by the `materialize_cross_side_*` lemmas: the new level's
    env+heap contribution depends only on `h.length` (not on `h`'s
    contents). -/

/-- Foldl helper: each iteration appends exactly one cell to the heap.
    Stated using `.fst`/`.snd` projections (matching what `simp` produces
    when reducing the destructuring `let`s in `freshLevelEnv`). -/
private theorem buildBindings_foldl_length (pairs : List (String × Val)) (h : Heap) (env : Env) :
    (pairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
      (h, env)).1.length = h.length + pairs.length := by
  induction pairs generalizing h env with
  | nil => simp [List.foldl]
  | cons p rest ih =>
      simp only [List.foldl, List.length_cons]
      rw [ih]
      simp [List.length_append]
      omega

/-- The buildBindings foldl produces the same env from accumulators
    with equal heap-length (the env's idxes are heap-length-derived only).
    Stated using projection form to match simp-reduced freshLevelEnv. -/
private theorem buildBindings_foldl_env_eq_of_len_eq (pairs : List (String × Val))
    (h_a h_b : Heap) (env : Env) (h_len : h_a.length = h_b.length) :
    (pairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
      (h_a, env)).2 =
    (pairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2))
      (h_b, env)).2 := by
  induction pairs generalizing h_a h_b env with
  | nil => simp [List.foldl]
  | cons p rest ih =>
      simp only [List.foldl]
      have h_step_len : (h_a ++ [p.2]).length = (h_b ++ [p.2]).length := by
        simp [List.length_append, h_len]
      have h_idx_eq : (Env.cons p.1 h_a.length env : Env)
                    = Env.cons p.1 h_b.length env := by
        rw [h_len]
      rw [h_idx_eq]
      exact ih _ _ _ h_step_len

/-- `freshLevelEnv h |>.2` depends only on `h.length`, not on the heap's
    contents. Now provable thanks to `primPairs`'s `@[irreducible]`
    annotation — Lean's `whnf` no longer tries to inline the 13-element
    list during the proof. -/
theorem freshLevelEnv_env_eq (h_a h_b : Heap) (h_len : h_a.length = h_b.length) :
    (freshLevelEnv h_a).2 = (freshLevelEnv h_b).2 := by
  have h_envPrims := buildBindings_foldl_env_eq_of_len_eq primPairs h_a h_b .nil h_len
  have h_inner_a := buildBindings_foldl_length primPairs h_a (.nil : Env)
  have h_inner_b := buildBindings_foldl_length primPairs h_b (.nil : Env)
  unfold freshLevelEnv
  simp only [Heap.alloc]
  rw [h_envPrims, h_inner_a, h_inner_b, h_len]

/-- `freshLevelEnv h` produces a heap with exactly 14 more cells than `h`. -/
theorem freshLevelEnv_heap_length (h : Heap) :
    (freshLevelEnv h).1.length = h.length + 14 := by
  have h_inner := buildBindings_foldl_length primPairs h (.nil : Env)
  rw [primPairs_length] at h_inner
  unfold freshLevelEnv
  simp only [Heap.alloc] at h_inner ⊢
  simp [List.length_append, h_inner]

/-! ### Cross-side parallelism for `materialize`

    These lemmas express that `materialize` is "deterministic up to
    bisimulation": if two tower states have equal heap-length and
    equal envAt? at all indices, then materialize behaves the same
    cross-side. The proof structure is:

    1. `materialize` only fails at `n ≥ maxDepth` (independent of T).
    2. The "no extension" case (`T.levels.length > n`): result is T
       unchanged on both sides.
    3. The "extension" case: each fold step appends a level whose env
       depends only on `T.heap.length` (via `freshLevelEnv`), and a
       heap suffix of 14 deterministic cells. Cross-side these match.

    Both lemmas needed by `frame_tower`'s `.em` and `applyVia` cases
    to construct the inductive step at level+1. Proofs sketched but
    sorry'd — the bookkeeping involves Lean's `Option`/`List.getElem?`
    interaction which is fiddly. -/

/-- Cross-side: `materialize` succeeds on both or fails on both. -/
theorem TowerState.materialize_cross_side_some_iff
    (T_a T_b : TowerState) (n : Nat) :
    T_a.materialize n = none ↔ T_b.materialize n = none := by
  unfold materialize
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1]
  · simp [h1]
    constructor <;> (intro h; split at h <;> simp at h)

/-- Cross-side: parallel materialize results have equal heap.length
    and equal envAt? at all indices. -/
theorem TowerState.materialize_cross_side_envs_eq
    (T_a T_b T_a' T_b' : TowerState) (n : Nat)
    (_h_heap_len : T_a.heap.length = T_b.heap.length)
    (_h_envs : ∀ m, T_a.envAt? m = T_b.envAt? m)
    (_h_mat_a : T_a.materialize n = some T_a')
    (_h_mat_b : T_b.materialize n = some T_b') :
    T_a'.heap.length = T_b'.heap.length ∧
    ∀ m, T_a'.envAt? m = T_b'.envAt? m :=
  sorry

/-! ## RunState compatibility shim

    The bisim infrastructure ported from lean-green is written
    against `RunState`. To reuse it, `RunState` is defined as an
    alias for `TowerState` and a `.policy` projection is provided
    that returns the level-0 policy by default.

    This shim is *adequate for the framing infrastructure* (where
    the policy carried in `WFCtx.policy_resp` only needs to be
    deterministic and stable). The truly cross-level lift —
    `StateExt` / `WFCtx` parameterized by level — is the work of
    `TowerBisim.lean` (forthcoming), which will refine this shim. -/

abbrev RunState := TowerState

/-- Project a single `BlackPolicy` from a `TowerState`. Defaults to
    level 0; returns `acceptAllPolicy` if level 0 is unmaterialized
    (which never happens for `initTower`-rooted runs). -/
def TowerState.policy (T : TowerState) : BlackPolicy :=
  (T.policyAt? 0).getD acceptAllPolicy
