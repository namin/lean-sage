/-
  lean-sage: Contextual β-equivalence — first phase.

  Long-term goal: for any context C and operational β-redex pair
  (M, N), `evalProgram (C.plug M)` and `evalProgram (C.plug N)`
  produce bisim-related observables, under a policy table whose
  admissions are all kernel-certified conservative extensions.

  ## Status

  - **L1** (`eval_beta_builtin`): sorry-free. At sufficient fuel,
    with level+1's `base-apply` cell still bound to
    `.builtinBaseApply`, the β-redex `((λx. body) v_expr)` reduces
    operationally to body-in-extended-env. Pure unfolding; no CE
    consumed.

  - **CE→β bridges**: sorry-free. Given a CE certificate for the
    installed user `base-apply`, the apply path produces a
    bisim-equivalent result to the counterfactual builtin apply.
    Two forms:
    - `ce_apply_bisim_builtin` — consumes `CE_weak_strong`
      (full-prefix). Applicable at admission moment.
    - `ce_apply_bisim_builtin_at` — consumes `CE_weak_strong_at`
      (selective-prefix, from `HeapAgree.lean`). Applicable at any
      heap preserving `HeapAgreeAt indices`, including
      post-admission.
    The full-prefix admission corollary
    `admission_applyVia_bisim_builtin` packages
    `approvedPolicy_soundForCE_weak_strong` directly.

  - **`multn_postAdmit_apply_bisim`**: sorry-free. End-to-end
    multn post-admission β-bisim. Combines `multnApproval_at_proof`
    (in `HeapAgree.lean`) with `ce_apply_bisim_builtin_at` here.
    For any multn-shape admitted modification, at any
    post-admission heap preserving `HeapAgreeAt [idx_o, idx_n]`
    on the closure's `orig` and `num?` cells, the applyVia path
    through the installed multn closure produces a
    bisim-equivalent result to the counterfactual builtin apply.

  - **L4 (parallel-bisim eval congruence)**, **T1 (contextual β)**:
    not yet formalized. The CE-certificate flow past admission is
    no longer the blocker; what remains is threading a
    `ParallelBisim` invariant through `eval` / `evalList` /
    `applyVia` / `applyDirect` by joint induction on fuel, then
    assembling per-Ctx-constructor congruence on top.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Soundness
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.HeapAgree

open LeanBlack

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

/-! ## Phase B — CE→β bridge (single-use form)

The companion to L1 for the non-builtin case: when level+1's
`base-apply` is bound to a *user* closure `bc` and we have a
`CE_weak_strong` certificate for `bc` over the current heap, the
β-redex's apply path produces a bisim-equivalent result to the
counterfactual builtin-apply.

This is the "single-use" form: the CE certificate is consumed
exactly once at a heap snapshot where its `HeapPrefix` premise
holds. The natural such moment is admission (where `T.heap = am.heap`
by construction). The deferred contextual-β goal generalizes this
to all future heap snapshots, which requires either weakening
`HeapPrefix` or maintaining bisim by other means. -/

/-! ### Structural lemma: applyVia with user base-apply factors. -/

theorem applyVia_user_factors (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T : TowerState)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat : T.levels.length > level + 1)
    (upEnv : Env) (idx : Nat) (bc : Val)
    (h_env : T.envAt? (level + 1) = some upEnv)
    (h_lookup : upEnv.lookup "base-apply" = some idx)
    (h_cell : T.heap[idx]? = some bc)
    (h_bc : bc ≠ .builtinBaseApply) :
    applyVia (n + 1) ptable level op args T
      = applyDirect n ptable level bc [op, listToVal args] T := by
  have h_materialize : T.materialize (level + 1) = some T := by
    unfold TowerState.materialize
    have h1 : ¬ (level + 1 ≥ Tower.maxDepth) := Nat.not_le_of_lt h_depth
    simp [h1, h_mat]
  unfold applyVia
  rw [h_materialize]
  cases bc with
  | builtinBaseApply => exact absurd rfl h_bc
  | num _ => simp [h_env, h_lookup, h_cell]
  | bool _ => simp [h_env, h_lookup, h_cell]
  | nilV => simp [h_env, h_lookup, h_cell]
  | cons _ _ => simp [h_env, h_lookup, h_cell]
  | sym _ => simp [h_env, h_lookup, h_cell]
  | closure _ _ _ => simp [h_env, h_lookup, h_cell]
  | prim _ => simp [h_env, h_lookup, h_cell]

/-! ### Unfolding `callAsBaseApply` for both branches -/

theorem callAsBaseApply_builtin (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (operands : List Val) (T : TowerState) :
    callAsBaseApply fuel ptable level .builtinBaseApply op operands T
      = applyDirect fuel ptable level op operands T := by
  unfold callAsBaseApply; rfl

theorem callAsBaseApply_user (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (bc : Val) (h_bc : bc ≠ .builtinBaseApply)
    (op : Val) (operands : List Val) (T : TowerState) :
    callAsBaseApply fuel ptable level bc op operands T
      = applyDirect fuel ptable level bc [op, listToVal operands] T := by
  unfold callAsBaseApply
  cases bc with
  | builtinBaseApply => exact absurd rfl h_bc
  | num _ => rfl
  | bool _ => rfl
  | nilV => rfl
  | cons _ _ => rfl
  | sym _ => rfl
  | closure _ _ _ => rfl
  | prim _ => rfl

/-! ### The bridge

Given a `CE_weak_strong` certificate for `bc` over the current heap,
the apply path through the user-installed base-apply produces a
bisim-equivalent result to the counterfactual builtin apply. -/

theorem ce_apply_bisim_builtin
    (level : Nat) (ptable : PolicyTable) (op : Val) (operands : List Val) (T : TowerState)
    (bc : Val) (h_bc : bc ≠ .builtinBaseApply)
    (upEnv : Env) (idx : Nat)
    (h_env : T.envAt? (level + 1) = some upEnv)
    (h_lookup : upEnv.lookup "base-apply" = some idx)
    (h_cell : T.heap[idx]? = some bc)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat : T.levels.length > level + 1)
    (h_ce : CE_weak_strong level T.heap .builtinBaseApply bc)
    -- CE side conditions on T:
    (h_heap : HeapValid T.heap)
    (h_op : ValValid op T.heap)
    (h_operands : ListValValid operands T.heap)
    (h_old_valid : ValValid .builtinBaseApply T.heap)
    (h_new_valid : ValValid bc T.heap)
    (h_ptable : PolicyTableRespectsBisimT ptable)
    (h_lvl_pol : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_env_valid : ∀ n env, T.envAt? n = some env → EnvValid env T.heap)
    (h_pol_bisim : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_env_bisim : ∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap)
    (h_heap_deep : HeapDeep T.heap)
    (h_op_deep : ValDeep op T.heap)
    (h_operands_deep : ListValDeep operands T.heap)
    (h_env_deep : ∀ n env, T.envAt? n = some env → EnvDeep env T.heap)
    (h_pt_shift : PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable)
    (h_pol_shift : ∀ n p, T.policyAt? n = some p →
                    PolicyRespectsShift T.heap.length [op, listToVal operands] p)
    -- builtin call succeeds:
    (fuel : Nat) (r : Val) (T' : TowerState)
    (h_call : applyDirect fuel ptable level op operands T = some (r, T')) :
    ∃ fuel' T'' r',
      applyVia (fuel' + 1) ptable level op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length := by
  have h_call' :
      callAsBaseApply fuel ptable level .builtinBaseApply op operands T = some (r, T') := by
    rw [callAsBaseApply_builtin]; exact h_call
  have h_prefix : HeapPrefix T.heap T.heap := HeapPrefix.refl _
  obtain ⟨fuel', T'', r', h_new_call, h_bisim, h_pol_eq, h_heap_valid, h_len⟩ :=
    h_ce fuel ptable op operands T r T' h_prefix
      h_heap h_op h_operands h_old_valid h_new_valid
      h_ptable h_lvl_pol h_env_valid h_pol_bisim h_env_bisim
      h_heap_deep h_op_deep h_operands_deep h_env_deep
      h_pt_shift h_pol_shift h_call'
  refine ⟨fuel', T'', r', ?_, h_bisim, h_pol_eq, h_heap_valid, h_len⟩
  rw [applyVia_user_factors fuel' ptable level op operands T
        h_depth h_mat upEnv idx bc h_env h_lookup h_cell h_bc]
  rw [← callAsBaseApply_user fuel' ptable level bc h_bc op operands T]
  exact h_new_call

/-! ### Admission-moment corollary

Consumes `approvedPolicy_soundForCE_weak_strong` directly. At the
moment a `.set "base-apply"` is admitted by `approvedPolicy approvals`
with new value `bc`, the apply path through `bc` (once installed)
produces a bisim-equivalent result to the counterfactual builtin
apply, evaluated at the admission-moment heap.

This is the "single-use" form: applicable at the heap snapshot
where `T.heap = ctx.heap` (the admission moment). Generalizing
beyond admission requires either weakening `HeapPrefix` in
`CE_weak_strong` (deferred) or maintaining bisim by other means. -/

theorem admission_applyVia_bisim_builtin
    (approvals : List ApprovedModification)
    (level : Nat) (h_levels : ∀ am ∈ approvals, am.level = level)
    (ctx : MutationCtx)
    (bc : Val) (h_bc : bc ≠ .builtinBaseApply)
    (h_admit : approvedPolicy approvals ctx .builtinBaseApply bc = true)
    (T : TowerState) (h_heap_eq : T.heap = ctx.heap)
    (upEnv : Env) (idx : Nat)
    (h_env : T.envAt? (level + 1) = some upEnv)
    (h_lookup : upEnv.lookup "base-apply" = some idx)
    (h_cell : T.heap[idx]? = some bc)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat : T.levels.length > level + 1)
    (ptable : PolicyTable) (op : Val) (operands : List Val)
    -- CE side conditions on T:
    (h_heap : HeapValid T.heap)
    (h_op : ValValid op T.heap)
    (h_operands : ListValValid operands T.heap)
    (h_old_valid : ValValid .builtinBaseApply T.heap)
    (h_new_valid : ValValid bc T.heap)
    (h_ptable : PolicyTableRespectsBisimT ptable)
    (h_lvl_pol : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_env_valid : ∀ n env, T.envAt? n = some env → EnvValid env T.heap)
    (h_pol_bisim : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_env_bisim : ∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap)
    (h_heap_deep : HeapDeep T.heap)
    (h_op_deep : ValDeep op T.heap)
    (h_operands_deep : ListValDeep operands T.heap)
    (h_env_deep : ∀ n env, T.envAt? n = some env → EnvDeep env T.heap)
    (h_pt_shift : PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable)
    (h_pol_shift : ∀ n p, T.policyAt? n = some p →
                    PolicyRespectsShift T.heap.length [op, listToVal operands] p)
    (fuel : Nat) (r : Val) (T' : TowerState)
    (h_call : applyDirect fuel ptable level op operands T = some (r, T')) :
    ∃ fuel' T'' r',
      applyVia (fuel' + 1) ptable level op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length := by
  have h_ce_at_ctx : CE_weak_strong level ctx.heap .builtinBaseApply bc :=
    approvedPolicy_soundForCE_weak_strong approvals level h_levels
      ctx .builtinBaseApply bc h_admit
  have h_ce : CE_weak_strong level T.heap .builtinBaseApply bc := by
    rw [h_heap_eq]; exact h_ce_at_ctx
  exact ce_apply_bisim_builtin level ptable op operands T bc h_bc
    upEnv idx h_env h_lookup h_cell h_depth h_mat h_ce
    h_heap h_op h_operands h_old_valid h_new_valid
    h_ptable h_lvl_pol h_env_valid h_pol_bisim h_env_bisim
    h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift fuel r T' h_call

/-! ## Phase C — CE→β bridge with selective premise (`CE_weak_strong_at`)

Mirrors `ce_apply_bisim_builtin` but consumes `CE_weak_strong_at`
(selective-prefix predicate from `HeapAgree.lean`) instead of
`CE_weak_strong`. Usable post-admission as long as the runtime
preserves agreement on the index list — which it does for any
mutation outside that set, including `.set "base-apply"` (the
`installMultnOneUp` pattern keeps `idx_o` and `idx_n` disjoint
from `idx_ba`).

This is the bridge that the L4/T1 contextual β path can consume
once L4's bisim invariant tracks `HeapAgreeAt` through eval steps. -/

theorem ce_apply_bisim_builtin_at
    (level : Nat) (ptable : PolicyTable) (op : Val) (operands : List Val) (T : TowerState)
    (bc : Val) (h_bc : bc ≠ .builtinBaseApply)
    (upEnv : Env) (idx : Nat)
    (h_env : T.envAt? (level + 1) = some upEnv)
    (h_lookup : upEnv.lookup "base-apply" = some idx)
    (h_cell : T.heap[idx]? = some bc)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat : T.levels.length > level + 1)
    -- Selective CE certificate + the witness it applies at this heap:
    (indices : List Nat) (h_ref : Heap)
    (h_ce_at : CE_weak_strong_at level indices h_ref .builtinBaseApply bc)
    (h_len_le : h_ref.length ≤ T.heap.length)
    (h_agree : HeapAgreeAt indices h_ref T.heap)
    -- CE side conditions on T (unchanged from the full-prefix version):
    (h_heap : HeapValid T.heap)
    (h_op : ValValid op T.heap)
    (h_operands : ListValValid operands T.heap)
    (h_old_valid : ValValid .builtinBaseApply T.heap)
    (h_new_valid : ValValid bc T.heap)
    (h_ptable : PolicyTableRespectsBisimT ptable)
    (h_lvl_pol : ∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_env_valid : ∀ n env, T.envAt? n = some env → EnvValid env T.heap)
    (h_pol_bisim : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_env_bisim : ∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap)
    (h_heap_deep : HeapDeep T.heap)
    (h_op_deep : ValDeep op T.heap)
    (h_operands_deep : ListValDeep operands T.heap)
    (h_env_deep : ∀ n env, T.envAt? n = some env → EnvDeep env T.heap)
    (h_pt_shift : PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable)
    (h_pol_shift : ∀ n p, T.policyAt? n = some p →
                    PolicyRespectsShift T.heap.length [op, listToVal operands] p)
    (fuel : Nat) (r : Val) (T' : TowerState)
    (h_call : applyDirect fuel ptable level op operands T = some (r, T')) :
    ∃ fuel' T'' r',
      applyVia (fuel' + 1) ptable level op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length := by
  have h_call' :
      callAsBaseApply fuel ptable level .builtinBaseApply op operands T = some (r, T') := by
    rw [callAsBaseApply_builtin]; exact h_call
  obtain ⟨fuel', T'', r', h_new_call, h_bisim, h_pol_eq, h_heap_valid, h_len⟩ :=
    h_ce_at fuel ptable op operands T r T' h_len_le h_agree
      h_heap h_op h_operands h_old_valid h_new_valid
      h_ptable h_lvl_pol h_env_valid h_pol_bisim h_env_bisim
      h_heap_deep h_op_deep h_operands_deep h_env_deep
      h_pt_shift h_pol_shift h_call'
  refine ⟨fuel', T'', r', ?_, h_bisim, h_pol_eq, h_heap_valid, h_len⟩
  rw [applyVia_user_factors fuel' ptable level op operands T
        h_depth h_mat upEnv idx bc h_env h_lookup h_cell h_bc]
  rw [← callAsBaseApply_user fuel' ptable level bc h_bc op operands T]
  exact h_new_call

/-! ## Phase D — packaged post-admission β-bisim for multn

The end-to-end statement combining `multnApproval_at_proof`
(`HeapAgree.lean`) and `ce_apply_bisim_builtin_at` (above): for any
multn-shape admitted modification, at any post-admission heap
preserving agreement on the closure's `orig` and `num?` cells, the
apply path through the installed multn closure produces a
bisim-equivalent result to the counterfactual builtin apply.

This is the headline result enabled by the HeapPrefix weakening:
the CE certificate fires *post*-admission, not only at admission
moment. Useful as a building block for the L4/T1 contextual lift,
and standalone as the first end-to-end "CE under mutation" theorem
in the repo. -/

theorem multn_postAdmit_apply_bisim
    -- The approval shape:
    (level : Nat) (admit_heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : multnExactPolicy
                 { target := "base-apply", heap := admit_heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true)
    (idx_o idx_n : Nat)
    (h_shape_o : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "orig" = some idx_o)
    (h_shape_n : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "num?" = some idx_n)
    (h_bc : newClosure ≠ .builtinBaseApply)
    -- The runtime state post-installation:
    (T_post : TowerState) (ptable : PolicyTable)
    (h_len : admit_heap.length ≤ T_post.heap.length)
    (h_agree : HeapAgreeAt [idx_o, idx_n] admit_heap T_post.heap)
    -- newClosure is installed at level+1's base-apply:
    (upEnv : Env) (idx_ba : Nat)
    (h_env : T_post.envAt? (level + 1) = some upEnv)
    (h_lookup : upEnv.lookup "base-apply" = some idx_ba)
    (h_cell : T_post.heap[idx_ba]? = some newClosure)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat : T_post.levels.length > level + 1)
    -- CE side conditions on T_post:
    (op : Val) (operands : List Val)
    (h_heap : HeapValid T_post.heap)
    (h_op : ValValid op T_post.heap)
    (h_operands : ListValValid operands T_post.heap)
    (h_old_valid : ValValid .builtinBaseApply T_post.heap)
    (h_new_valid : ValValid newClosure T_post.heap)
    (h_ptable : PolicyTableRespectsBisimT ptable)
    (h_lvl_pol : ∀ p, T_post.policyAt? level = some p → PolicyRespectsBisimT p)
    (h_env_valid : ∀ n env, T_post.envAt? n = some env → EnvValid env T_post.heap)
    (h_pol_bisim : ∀ n p, T_post.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_env_bisim : ∀ n env, T_post.envAt? n = some env → EnvVis env env T_post.heap T_post.heap)
    (h_heap_deep : HeapDeep T_post.heap)
    (h_op_deep : ValDeep op T_post.heap)
    (h_operands_deep : ListValDeep operands T_post.heap)
    (h_env_deep : ∀ n env, T_post.envAt? n = some env → EnvDeep env T_post.heap)
    (h_pt_shift : PolicyTableRespectsShift T_post.heap.length [op, listToVal operands] ptable)
    (h_pol_shift : ∀ n p, T_post.policyAt? n = some p →
                    PolicyRespectsShift T_post.heap.length [op, listToVal operands] p)
    -- If the builtin path succeeds:
    (fuel : Nat) (r : Val) (T' : TowerState)
    (h_call : applyDirect fuel ptable level op operands T_post = some (r, T')) :
    -- The applyVia (which now routes through multn) produces a bisim-equivalent result:
    ∃ fuel' T'' r',
      applyVia (fuel' + 1) ptable level op operands T_post = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T_post.heap.length ≤ T''.heap.length := by
  have h_ce_at : CE_weak_strong_at level [idx_o, idx_n] admit_heap
                   .builtinBaseApply newClosure :=
    multnApproval_at_proof level admit_heap env metaEnv index newClosure
      h_admit idx_o idx_n h_shape_o h_shape_n
  exact ce_apply_bisim_builtin_at level ptable op operands T_post
    newClosure h_bc upEnv idx_ba h_env h_lookup h_cell h_depth h_mat
    [idx_o, idx_n] admit_heap h_ce_at h_len h_agree
    h_heap h_op h_operands h_old_valid h_new_valid
    h_ptable h_lvl_pol h_env_valid h_pol_bisim h_env_bisim
    h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift fuel r T' h_call
