/-
  lean-sage: Contextual β-equivalence — first phase.

  Long-term goal: for any context C and operational β-redex pair
  (M, N), `evalProgram (C.plug M)` and `evalProgram (C.plug N)`
  produce bisim-related observables, under a policy table whose
  admissions are all kernel-certified conservative extensions.

  ## Status

  - **L1** (`eval_beta_builtin`, this file): sorry-free. At
    sufficient fuel, with level+1's `base-apply` cell still bound
    to `.builtinBaseApply`, the β-redex `((λx. body) v_expr)`
    reduces operationally to body-in-extended-env. Pure unfolding;
    no CE consumed.

  - **L2/L3/L4/T1**: not formalized in this file. Blocked on the
    architectural finding below.

  ## Architectural finding (blocker for the CE-leveraging path)

  `CE_weak_strong level h_ref old new` carries the premise
  `HeapPrefix h_ref T.heap` — *content*-prefix at the first
  `h_ref.length` cells. An approval `am ∈ approvals` is constructed
  with `am.heap = T.heap_at_admission`, and `am.heap` is the
  reference heap for `am.proof : CE_weak_strong level am.heap …`.

  After a `.set "base-apply"` fires and updates the heap at the
  base-apply cell index `idx_ba`, we have
  `T_new.heap = T.heap.update idx_ba newVal`. Since `idx_ba <
  am.heap.length` (the base-apply cell was allocated before
  admission), `T_new.heap[idx_ba] = newVal` but
  `am.heap[idx_ba] = .builtinBaseApply`. Therefore
  `HeapPrefix am.heap T_new.heap` is *false*.

  Consequence: `CE_weak_strong_heap_mono` cannot lift the approval's
  CE certificate from `am.heap` to `T_new.heap`. The certificate is
  consumable *only at the admission moment* — but β-equivalence
  questions arise at future eval steps, after the heap has drifted.

  The multn proof's actual cell lookups only touch the prim cells
  (`num?`, `*`, …), never the base-apply cell. So the proof remains
  morally valid at `T_new.heap`. The `HeapPrefix` premise is
  *stronger than necessary* — it demands content-equality on cells
  the proof doesn't read.

  ## Unblocks needed (any one of)

  1. Weaken `HeapPrefix` to a selective form
     (content-equality at a specific index set), and rerun the
     multn proof under the weakened premise.
  2. Add a separate predicate `CE_weak_strong_stable` that's
     robust to base-apply mutations, with a bridge from existing
     approvals.
  3. Rebuild the multn-style argument at post-mutation heaps by
     hand, treating each approval's bisim claim as a local fact
     rather than a re-derivable theorem.

  Without one of these, L1 stands as the most useful structural
  fact this file can deliver; the contextual β-equivalence proof
  cannot consume CE certificates beyond the moment of admission.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Soundness
import LeanBlack.Policies
import LeanBlack.ProofBased

/-! ## L1 — Builtin β unfolding

If `T.envAt? (level+1)` is materialized and binds `base-apply` to the
builtin, then evaluating `((λx. body) v_expr)` at level `level`
factors operationally into:

  1. evaluate `v_expr` → `(v_val, T')`,
  2. materialize level+1 (a no-op if already materialized) → `T_m`,
  3. allocate `v_val` in `T_m`'s heap → idx = `T_m.heap.length`,
  4. evaluate `body` in env `(.cons x idx env)`, heap `T_m.heap ++ [v_val]`.

No CE machinery used here; the policy gate isn't consulted along the
`.app`/`.lam`/`applyVia`-builtin/`applyDirect` path. -/

/-- The result of "operational β at the redex":
    eval body in the env extended with `x ↦ idx`, in a heap where
    `v_val` has been allocated at `idx`. -/
def betaContractEval
    (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (body : Expr) (env : Env) (T : TowerState) (v_val : Val)
    : Option (Val × TowerState) :=
  let h'   := T.heap ++ [v_val]
  let idx  := T.heap.length
  let env' := Env.cons x idx env
  eval fuel ptable level body env' { T with heap := h' }

/-- Shorthand: "level+1's base-apply, in T's tower, is the builtin." -/
def builtinBaseApplyAt (level : Nat) (T : TowerState) : Prop :=
  ∃ upEnv idx,
    T.envAt? (level + 1) = some upEnv ∧
    upEnv.lookup "base-apply" = some idx ∧
    T.heap[idx]? = some .builtinBaseApply


/-! ### Step 1: `.lam` returns its closure cheaply.

Direct from the eval clause for `.lam`. -/

theorem eval_lam (n : Nat) (ptable : PolicyTable) (level : Nat)
    (ps : List String) (body : Expr) (env : Env) (T : TowerState) :
    eval (n + 1) ptable level (.lam ps body) env T
      = some (.closure ps body env, T) := by
  simp [eval]

/-! ### Step 2: `evalList` on a single-element list with sufficient fuel. -/

theorem evalList_single (n : Nat) (ptable : PolicyTable) (level : Nat)
    (e : Expr) (env : Env) (T : TowerState) :
    evalList (n + 2) ptable level [e] env T
      = match eval (n + 1) ptable level e env T with
        | none => none
        | some (v, T') => some ([v], T') := by
  simp [evalList]
  cases h : eval (n + 1) ptable level e env T with
  | none => simp [h]
  | some r =>
      obtain ⟨v, T'⟩ := r
      simp [h, evalList]

/-! ### Step 3: `applyVia` on a closure, when level+1 base-apply is
the builtin and level+1 is already materialized, factors to
`applyDirect`. -/

theorem applyVia_builtin_factors (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T : TowerState)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat : T.levels.length > level + 1)
    (h_builtin : builtinBaseApplyAt level T) :
    applyVia (n + 1) ptable level op args T
      = applyDirect n ptable level op args T := by
  obtain ⟨upEnv, idx, h_env, h_lookup, h_cell⟩ := h_builtin
  have h_materialize : T.materialize (level + 1) = some T := by
    unfold TowerState.materialize
    have h1 : ¬ (level + 1 ≥ Tower.maxDepth) := Nat.not_le_of_lt h_depth
    simp [h1, h_mat]
  unfold applyVia
  simp [h_materialize, h_env, h_lookup, h_cell]

/-! ### Step 4: `applyDirect` on a closure with one parameter. -/

theorem applyDirect_closure_one (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (body : Expr) (cenv : Env) (v_val : Val) (T : TowerState) :
    applyDirect (n + 1) ptable level (.closure [x] body cenv) [v_val] T
      = eval n ptable level body
          (Env.cons x T.heap.length cenv)
          { T with heap := T.heap ++ [v_val] } := by
  simp [applyDirect, allocStep, Heap.alloc]

/-! ### L1 — Full builtin β unfolding.

Combines steps 1–4. At sufficient fuel, with level+1's `base-apply`
bound to the builtin and level+1 already materialized, `eval`
of a β-redex `(λx. body) v_expr` factors into the contracted form. -/

/-- One-step unfold of `eval` on `.app [.lam .., v_expr]`. Stepping
    stone for `eval_beta_builtin`. -/
theorem eval_app_lam_v_step (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (body : Expr) (v_expr : Expr) (env : Env) (T : TowerState) :
    eval (n + 1) ptable level (.app [.lam [x] body, v_expr]) env T
    = match eval n ptable level (.lam [x] body) env T with
      | none => none
      | some (fv, T₁) =>
          match evalList n ptable level [v_expr] env T₁ with
          | none => none
          | some (avs, T₂) => applyVia n ptable level fv avs T₂ := by
  simp [eval]; rfl

theorem eval_beta_builtin
    (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (body : Expr) (v_expr : Expr) (env : Env) (T : TowerState)
    (h_depth : level + 1 < Tower.maxDepth)
    (v_val : Val) (T' : TowerState)
    (h_eval_v : eval (n + 1) ptable level v_expr env T = some (v_val, T'))
    (h_mat' : T'.levels.length > level + 1)
    (h_builtin' : builtinBaseApplyAt level T') :
    eval (n + 3) ptable level (.app [.lam [x] body, v_expr]) env T
      = eval n ptable level body
          (Env.cons x T'.heap.length env)
          { T' with heap := T'.heap ++ [v_val] } := by
  show eval ((n + 2) + 1) ptable level _ env T = _
  rw [eval_app_lam_v_step (n + 2) ptable level x body v_expr env T]
  show (match eval (n + 2) ptable level (.lam [x] body) env T with
        | none => none
        | some (fv, T₁) =>
            match evalList (n + 2) ptable level [v_expr] env T₁ with
            | none => none
            | some (avs, T₂) => applyVia (n + 2) ptable level fv avs T₂) = _
  rw [eval_lam (n + 1) ptable level [x] body env T]
  show (match evalList (n + 2) ptable level [v_expr] env T with
        | none => none
        | some (avs, T₂) => applyVia (n + 2) ptable level (.closure [x] body env) avs T₂) = _
  rw [evalList_single n ptable level v_expr env T, h_eval_v]
  show applyVia (n + 2) ptable level (.closure [x] body env) [v_val] T' = _
  rw [applyVia_builtin_factors (n + 1) ptable level _ _ T' h_depth h_mat' h_builtin',
      applyDirect_closure_one n ptable level x body env v_val T']
