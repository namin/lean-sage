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

/-! ## Inductive step (TODO)

`evalFuelBump_succ : ∀ n, EvalFuelBump n → EvalFuelBump (n+1)` is
the substantive proof — joint induction on `n` with casework per
`Expr` constructor (for `eval`), per cons/nil (for `evalList`),
and per `Val` constructor (for `applyDirect`).

Each case structure mirrors `allPureIndep_succ` in
`ProofBased.lean`: destructure the hypothesis, apply the IH to
sub-evaluations, recombine. The arithmetic is one-step bumping
rather than policy-substitution.

Estimated ~600 LOC. Not in this turn. -/

end LeanBlack
