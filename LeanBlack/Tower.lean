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

/-- Allocate a fresh "level" worth of cells in the heap: one cell
    per standard primitive plus a `base-apply` cell. Returns the
    extended heap and the env for the new level. -/
def freshLevelEnv (h : Heap) : Heap × Env :=
  let pairs : List (String × Val) :=
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
  let (h', envPrims) :=
    pairs.foldl
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

/-- Ensure level `n` is materialized in `T`. Returns the (potentially
    extended) tower, or `none` if `n ≥ maxDepth`. -/
def TowerState.materialize (T : TowerState) (n : Nat) : Option TowerState :=
  if n ≥ Tower.maxDepth then none
  else if T.levels.length > n then some T
  else
    let needed := n + 1 - T.levels.length
    let extended : TowerState :=
      Nat.fold needed (fun _ _ T' =>
        let (h', env) := freshLevelEnv T'.heap
        { heap := h', levels := T'.levels ++ [{ env := env, policy := acceptAllPolicy }] })
        T
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
