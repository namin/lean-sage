/-
  lean-sage: Fuel monotonicity for `eval` / `evalList` /
  `applyVia` / `applyDirect`.

  A "one-step bump" lemma: if these functions succeed at fuel `n`
  with some result, they also succeed at fuel `n+1` with the same
  result. By induction, any fuel ≥ n works.

  Why we need it: `eval_beta_builtin` (in `ContextualBeta.lean`)
  is stated at a *specific* fuel (`n+3` for the β-redex, `n` for
  the contractum body). To compare evaluations of a β-redex M
  and its contractum N (e.g., `.letE x v_expr body`) inside a
  larger context, the fuel arithmetic on the two sides differs.
  Fuel monotonicity lets us reconcile.

  ## Joint structure

  The four functions are mutually recursive, so monotonicity is a
  joint claim, proved by induction on fuel. Mirrors
  `allPureIndep` in `ProofBased.lean` structurally: same fuel-
  joint shape, but the claim is one-step bump instead of policy-
  independence.

  ## Status

  Definitions + base case `n = 0` proven. The inductive step is
  the bulk of the work (~600 LOC of casework per Expr/Val
  constructor, parallel to `allPureIndep_succ`). Not in this file
  yet — left as a TODO with a clear structural template.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval

namespace LeanBlack

/-- Joint fuel-bump claim across the four mutually-recursive
    evaluation functions. -/
def EvalFuelBump (n : Nat) : Prop :=
  (∀ (ptable : PolicyTable) (level : Nat) (e : Expr) (env : Env) (T : TowerState)
       (v : Val) (T' : TowerState),
       eval n ptable level e env T = some (v, T') →
       eval (n + 1) ptable level e env T = some (v, T')) ∧
  (∀ (ptable : PolicyTable) (level : Nat) (es : List Expr) (env : Env) (T : TowerState)
       (vs : List Val) (T' : TowerState),
       evalList n ptable level es env T = some (vs, T') →
       evalList (n + 1) ptable level es env T = some (vs, T')) ∧
  (∀ (ptable : PolicyTable) (level : Nat) (op : Val) (args : List Val) (T : TowerState)
       (v : Val) (T' : TowerState),
       applyVia n ptable level op args T = some (v, T') →
       applyVia (n + 1) ptable level op args T = some (v, T')) ∧
  (∀ (ptable : PolicyTable) (level : Nat) (op : Val) (args : List Val) (T : TowerState)
       (v : Val) (T' : TowerState),
       applyDirect n ptable level op args T = some (v, T') →
       applyDirect (n + 1) ptable level op args T = some (v, T'))

/-- Base case: at fuel 0, none of the functions succeed, so the
    implication is vacuously true. -/
theorem evalFuelBump_zero : EvalFuelBump 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ h; simp [eval] at h
  · intro _ _ _ _ _ _ _ h; simp [evalList] at h
  · intro _ _ _ _ _ _ _ h; simp [applyVia] at h
  · intro _ _ _ _ _ _ _ h; simp [applyDirect] at h

/-! ## Inductive step

`evalFuelBump_succ : ∀ n, EvalFuelBump n → EvalFuelBump (n+1)` —
joint induction on `n` with casework per `Expr` constructor (for
`eval`), per cons/nil (for `evalList`), and per `Val` constructor
(for `applyDirect`).

Structurally mirrors `allPureIndep_succ` in `ProofBased.lean`:
destructure the hypothesis, apply the IH to sub-evaluations,
recombine. Simpler because we lift "success at fuel n → success at
fuel n+1" without policy substitution or purity bookkeeping. -/

theorem evalFuelBump_succ (n : Nat) (IH : EvalFuelBump n) :
    EvalFuelBump (n + 1) := by
  obtain ⟨IH_eval, IH_evalList, IH_applyVia, IH_applyDirect⟩ := IH
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- eval clause
    intro ptable level e env T v T' h_some
    cases e with
    | num i =>
        simp only [eval] at h_some ⊢; exact h_some
    | bool b =>
        simp only [eval] at h_some ⊢; exact h_some
    | quote vq =>
        simp only [eval] at h_some ⊢; exact h_some
    | var x =>
        simp only [eval] at h_some ⊢; exact h_some
    | lam ps body =>
        simp only [eval] at h_some ⊢; exact h_some
    | ifte c t e =>
        simp only [eval] at h_some ⊢
        generalize h_ec : eval n ptable level c env T = ec at h_some
        cases ec with
        | none => simp at h_some
        | some pair =>
            obtain ⟨vc, Tc⟩ := pair
            have h_ec' := IH_eval ptable level c env T vc Tc h_ec
            rw [h_ec']
            cases vc with
            | bool b' =>
                cases b' with
                | true =>
                    simp at h_some ⊢
                    exact IH_eval ptable level t env Tc v T' h_some
                | false =>
                    simp at h_some ⊢
                    exact IH_eval ptable level e env Tc v T' h_some
            | num _ =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
            | nilV =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
            | sym _ =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
            | cons _ _ =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
            | closure _ _ _ =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
            | prim _ =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
            | builtinBaseApply =>
                simp at h_some ⊢
                exact IH_eval ptable level t env Tc v T' h_some
    | app exps =>
        cases exps with
        | nil => simp [eval] at h_some
        | cons f args =>
            simp only [eval] at h_some ⊢
            generalize h_ef : eval n ptable level f env T = ef at h_some
            cases ef with
            | none => simp at h_some
            | some pair =>
                obtain ⟨fv, T₁⟩ := pair
                have h_ef' := IH_eval ptable level f env T fv T₁ h_ef
                rw [h_ef']; simp at h_some ⊢
                generalize h_el : evalList n ptable level args env T₁ = el at h_some
                cases el with
                | none => simp at h_some
                | some pair' =>
                    obtain ⟨avs, T₂⟩ := pair'
                    have h_el' := IH_evalList ptable level args env T₁ avs T₂ h_el
                    rw [h_el']; simp at h_some ⊢
                    exact IH_applyVia ptable level fv avs T₂ v T' h_some
    | set x e =>
        simp only [eval] at h_some ⊢
        generalize h_ee : eval n ptable level e env T = ee at h_some
        cases ee with
        | none => simp at h_some
        | some pair =>
            obtain ⟨v_e, T''⟩ := pair
            have h_ee' := IH_eval ptable level e env T v_e T'' h_ee
            rw [h_ee']
            exact h_some
    | em b =>
        simp only [eval] at h_some ⊢
        cases h_mat : T.materialize (level + 1) with
        | none => simp [h_mat] at h_some
        | some T₁ =>
            simp [h_mat] at h_some ⊢
            cases h_env : T₁.envAt? (level + 1) with
            | none => simp [h_env] at h_some
            | some upEnv =>
                simp [h_env] at h_some ⊢
                exact IH_eval ptable (level+1) b upEnv T₁ v T' h_some
    | primApp f args =>
        simp only [eval] at h_some ⊢
        generalize h_ef : eval n ptable level f env T = ef at h_some
        cases ef with
        | none => simp at h_some
        | some pair =>
            obtain ⟨fv, T₁⟩ := pair
            have h_ef' := IH_eval ptable level f env T fv T₁ h_ef
            rw [h_ef']; simp at h_some ⊢
            generalize h_el : evalList n ptable level args env T₁ = el at h_some
            cases el with
            | none => simp at h_some
            | some pair' =>
                obtain ⟨avs, T₂⟩ := pair'
                have h_el' := IH_evalList ptable level args env T₁ avs T₂ h_el
                rw [h_el']; simp at h_some ⊢
                exact IH_applyDirect ptable level fv avs T₂ v T' h_some
    | letE x e body =>
        simp only [eval] at h_some ⊢
        generalize h_ee : eval n ptable level e env T = ee at h_some
        cases ee with
        | none => simp at h_some
        | some pair =>
            obtain ⟨v_e, T''⟩ := pair
            have h_ee' := IH_eval ptable level e env T v_e T'' h_ee
            rw [h_ee']; simp at h_some ⊢
            exact IH_eval ptable level body _ _ v T' h_some
    | seq exps =>
        cases exps with
        | nil =>
            simp only [eval] at h_some ⊢; exact h_some
        | cons e rest =>
            cases rest with
            | nil =>
                simp only [eval] at h_some ⊢
                exact IH_eval ptable level e env T v T' h_some
            | cons e2 rest2 =>
                simp only [eval] at h_some ⊢
                generalize h_ee : eval n ptable level e env T = ee at h_some
                cases ee with
                | none => simp at h_some
                | some pair =>
                    obtain ⟨v_e, T₁⟩ := pair
                    have h_ee' := IH_eval ptable level e env T v_e T₁ h_ee
                    rw [h_ee']; simp at h_some ⊢
                    exact IH_eval ptable level (.seq (e2 :: rest2)) env T₁ v T' h_some
    | installPolicy idx =>
        simp only [eval] at h_some ⊢; exact h_some
  · -- evalList clause
    intro ptable level es env T vs T' h_some
    cases es with
    | nil => simp only [evalList] at h_some ⊢; exact h_some
    | cons hd tl =>
        simp only [evalList] at h_some ⊢
        generalize h_e : eval n ptable level hd env T = e_res at h_some
        cases e_res with
        | none => simp at h_some
        | some pair =>
            obtain ⟨vh, T₁⟩ := pair
            have h_e' := IH_eval ptable level hd env T vh T₁ h_e
            rw [h_e']; simp at h_some ⊢
            generalize h_el : evalList n ptable level tl env T₁ = el at h_some
            cases el with
            | none => simp at h_some
            | some pair' =>
                obtain ⟨vts, T₂⟩ := pair'
                have h_el' := IH_evalList ptable level tl env T₁ vts T₂ h_el
                rw [h_el']
                exact h_some
  · -- applyVia clause
    intro ptable level op args T v T' h_some
    simp only [applyVia] at h_some ⊢
    cases h_mat : T.materialize (level + 1) with
    | none => simp [h_mat] at h_some
    | some T₁ =>
        simp [h_mat] at h_some ⊢
        cases h_env : T₁.envAt? (level + 1) with
        | none =>
            simp [h_env] at h_some ⊢
            exact IH_applyDirect ptable level op args T₁ v T' h_some
        | some upEnv =>
            simp [h_env] at h_some ⊢
            cases h_la : upEnv.lookup "base-apply" with
            | none =>
                simp [h_la] at h_some ⊢
                exact IH_applyDirect ptable level op args T₁ v T' h_some
            | some idx =>
                simp [h_la] at h_some ⊢
                cases h_cell : T₁.heap[idx]? with
                | none => simp [h_cell] at h_some
                | some baseApply =>
                    simp [h_cell] at h_some ⊢
                    cases baseApply with
                    | builtinBaseApply =>
                        simp at h_some ⊢
                        exact IH_applyDirect ptable level op args T₁ v T' h_some
                    | num _ =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
                    | bool _ =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
                    | nilV =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
                    | sym _ =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
                    | cons _ _ =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
                    | closure _ _ _ =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
                    | prim _ =>
                        exact IH_applyDirect ptable level _ [op, listToVal args] T₁ v T' h_some
  · -- applyDirect clause
    intro ptable level op args T v T' h_some
    cases op with
    | num _ => simp [applyDirect] at h_some
    | bool _ => simp [applyDirect] at h_some
    | nilV => simp [applyDirect] at h_some
    | sym _ => simp [applyDirect] at h_some
    | cons _ _ => simp [applyDirect] at h_some
    | prim name =>
        simp only [applyDirect] at h_some ⊢
        cases h_pa : applyPrim name args with
        | none => simp [h_pa] at h_some
        | some v' => simp [h_pa] at h_some ⊢; exact h_some
    | builtinBaseApply =>
        cases args with
        | nil => simp [applyDirect] at h_some
        | cons actualOp tl =>
            cases tl with
            | nil => simp [applyDirect] at h_some
            | cons opList tl2 =>
                cases tl2 with
                | nil =>
                    simp only [applyDirect] at h_some ⊢
                    cases h_vtl : valToList opList with
                    | none => simp [h_vtl] at h_some
                    | some operands =>
                        simp [h_vtl] at h_some ⊢
                        exact IH_applyDirect ptable level actualOp operands T v T' h_some
                | cons _ _ => simp [applyDirect] at h_some
    | closure ps body cenv =>
        simp only [applyDirect] at h_some ⊢
        by_cases h_len : ps.length = args.length
        · simp [h_len] at h_some ⊢
          exact IH_eval ptable level body _ _ v T' h_some
        · simp [h_len] at h_some

theorem evalFuelBump : ∀ n, EvalFuelBump n
  | 0     => evalFuelBump_zero
  | n + 1 => evalFuelBump_succ n (evalFuelBump n)

/-- Fuel monotonicity for `eval`: any fuel ≥ `n` produces the same
    result. By induction on `m - n` using `evalFuelBump`. -/
theorem eval_fuel_mono {n m : Nat} (h_le : n ≤ m)
    {ptable : PolicyTable} {level : Nat} {e : Expr} {env : Env}
    {T : TowerState} {v : Val} {T' : TowerState}
    (h_some : eval n ptable level e env T = some (v, T')) :
    eval m ptable level e env T = some (v, T') := by
  induction h_le with
  | refl => exact h_some
  | step _ ih => exact (evalFuelBump _).1 ptable level e env T v T' ih

/-- Fuel monotonicity for `evalList`. -/
theorem evalList_fuel_mono {n m : Nat} (h_le : n ≤ m)
    {ptable : PolicyTable} {level : Nat} {es : List Expr} {env : Env}
    {T : TowerState} {vs : List Val} {T' : TowerState}
    (h_some : evalList n ptable level es env T = some (vs, T')) :
    evalList m ptable level es env T = some (vs, T') := by
  induction h_le with
  | refl => exact h_some
  | step _ ih => exact (evalFuelBump _).2.1 ptable level es env T vs T' ih

/-- Fuel monotonicity for `applyVia`. -/
theorem applyVia_fuel_mono {n m : Nat} (h_le : n ≤ m)
    {ptable : PolicyTable} {level : Nat} {op : Val} {args : List Val}
    {T : TowerState} {v : Val} {T' : TowerState}
    (h_some : applyVia n ptable level op args T = some (v, T')) :
    applyVia m ptable level op args T = some (v, T') := by
  induction h_le with
  | refl => exact h_some
  | step _ ih => exact (evalFuelBump _).2.2.1 ptable level op args T v T' ih

/-- Fuel monotonicity for `applyDirect`. -/
theorem applyDirect_fuel_mono {n m : Nat} (h_le : n ≤ m)
    {ptable : PolicyTable} {level : Nat} {op : Val} {args : List Val}
    {T : TowerState} {v : Val} {T' : TowerState}
    (h_some : applyDirect n ptable level op args T = some (v, T')) :
    applyDirect m ptable level op args T = some (v, T') := by
  induction h_le with
  | refl => exact h_some
  | step _ ih => exact (evalFuelBump _).2.2.2 ptable level op args T v T' ih

end LeanBlack
