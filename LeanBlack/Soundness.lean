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

/-- `TowerCE` is reflexive (every tower CE-extends itself).
    Body deferred — needs `ValVis_aux_self_extend` and
    `applyDirect_preserves_HeapValid` which lives in the
    post-frame Bisim sections (not yet ported). -/
theorem TowerCE.refl (T : TowerState) : TowerCE T T :=
  sorry

/-! ## Safe evolution -/

/-- Every materialized level's policy is universally sound (at its
    own level), and every policy in the table is universally sound
    at every level. The latter is needed because `(installPolicy n)`
    can swap any table policy into any materialized level. -/
def SafeEvolution (ptable : PolicyTable) (T : TowerState) : Prop :=
  (∀ n p, T.policyAt? n = some p → p.UnivSoundAt n) ∧
  (∀ p, p ∈ ptable → ∀ level, p.UnivSoundAt level)

/-! ## The headline theorem (statement; body deferred) -/

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
    (h_safe : SafeEvolution ptable T)
    (v : Val) (T' : TowerState)
    (h_eval : eval fuel ptable level exp env T = some (v, T')) :
    TowerCE T T' ∧ SafeEvolution ptable T' :=
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
    obtain ⟨fuel', T'', r', h_call, _⟩ :=
      h_ce 10 [] (.prim "+") [.num 1, .num 2] cex_T (.num 3) cex_T h_witness
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
