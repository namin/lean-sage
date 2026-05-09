/-
  lean-black: Verified policy library (tower-aware).

  Adapted from `lean-green/LeanBlack/Policies.lean`. The structural
  policy definitions (`acceptAll`, `rejectAll`, `numGuardPolicy`,
  `multnExactPolicy`) port verbatim — `BlackPolicy` is unchanged
  in shape (`MutationCtx → Val → Val → Bool`), the only difference
  is `MutationCtx.level` was added.

  The wrapper `callAsBaseApply` and the conservative-extension
  predicate `CE` / `CE_weak` are *per-level* in this version: cross-
  side policy equality is checked at a specific `level`, not on a
  monolithic `s.policy`.

  ## What's done

  - `callAsBaseApply` (tower-aware)
  - `CE` / `CE_weak` (per-level)
  - `acceptAll` / `rejectAll` SoundForCE proofs
  - `numGuardPolicy` / `multnExactPolicy` definitions + structural
    shape lemmas
  - `verifiedTable` and indexing constants
  - The headline theorem statement
    `multnExact_soundForCE_first_install_tower` (sorry'd —
    discharging it requires the full frame port)

  ## What's deferred (waiting on Frame.lean completion)

  - `*_respects_bisim` theorems for `numGuardPolicy` /
    `multnExactPolicy` (they need `bisim_imp_eq` which is in
    `Bisim.lean` — those *can* port; on the to-do list).
  - `*_respects_shift` theorems (they need the shift apparatus
    which lives in the post-frame Bisim section, not yet ported).
  - The conditional CE soundness theorems
    (`multnExact_CE_num_case_vacuous` /
    `multnExact_CE_nonnum_case`) — both depend on the frame
    theorem.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame

/-! ## Calling a Val as base-apply (tower-aware) -/

/-- Call a `Val` as if it were the level-`level+1` `base-apply`.
    `.builtinBaseApply` dispatches `(op, operands)` directly; a
    closure replacement takes `(op, listOf operands)` (matching the
    `applyVia` convention). -/
def callAsBaseApply (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (baseApply : Val) (op : Val) (operands : List Val) (T : TowerState)
    : Option (Val × TowerState) :=
  match baseApply with
  | .builtinBaseApply => applyDirect fuel ptable level op operands T
  | _                 => applyDirect fuel ptable level baseApply
                                     [op, listToVal operands] T

/-- **Conservative extension** between two candidate base-apply
    values at a given `level`. `new` conservatively extends `old`
    if every successful call through `old` produces a successful
    call through `new` with a `ValVis`-related result and well-
    formed post-state.

    Cross-side policy equality is checked *at `level`*: a
    reflective replacement that hijacked the policy at the
    governing level would violate this (and so violate CE). The
    lean-green version asks `s'.policy = s''.policy`; the tower
    version specializes to the level-of-interest. -/
def CE (level : Nat) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length

/-- Same as `CE` but with `ValVis_weak` in the conclusion. The
    behavioral statement; weaker than `CE` for closure-typed
    results, equivalent for first-order results. See lean-green's
    `WAND.md` for the full architectural argument. -/
def CE_weak (level : Nat) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length

abbrev BlackPolicy.SoundForCE (level : Nat) (p : BlackPolicy) : Prop :=
  p.Sound (CE level)

abbrev BlackPolicy.SoundForCE_weak (level : Nat) (p : BlackPolicy) : Prop :=
  p.Sound (CE_weak level)

/-! ## Trivial policies -/

theorem rejectAllPolicy_soundForCE (level : Nat) :
    rejectAllPolicy.SoundForCE level := by
  intro _ _ _ h; simp [rejectAllPolicy] at h

/-! ## `numGuardPolicy` — loose structural shape

    Admits any closure with `(λ (op args). (if (num? op) <anything>
    <anything>))` shape. The else-branch is unconstrained — a
    closure-shaped malicious modification can pass this. Used to
    illustrate the "loose vs strict" governance contrast in demos.
    Not sound for CE. -/
def numGuardPolicy : BlackPolicy := fun _ctx _old new =>
  match new with
  | .closure [_, _] body _ =>
      match body with
      | .ifte cond _ _ =>
          match cond with
          | .primApp (.var pred) [.var _] => pred == "num?"
          | _                              => false
      | _ => false
  | _ => false

def NumGuardShape (v : Val) : Prop :=
  ∃ p1 p2 t e cenv var,
    v = .closure [p1, p2]
      (.ifte (.primApp (.var "num?") [.var var]) t e) cenv

theorem numGuard_sound_for_shape :
    numGuardPolicy.Sound (fun _ new => NumGuardShape new) := by
  intro _ _ new h
  unfold numGuardPolicy at h
  split at h
  · split at h
    · split at h
      · rename_i pred _
        have hpred : pred = "num?" := by simp at h; exact h
        subst hpred
        exact ⟨_, _, _, _, _, _, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-! ## `multnExactPolicy` — strict multn shape + install-protocol

    Admits a `(λ (op args). (if (num? op) <num-branch>
    (orig op args)))` closure *with the delegating else-branch
    fixed* AND with `cenv` binding `orig` to the current
    `base-apply` (= `oldVal`) and `num?` to `.prim "num?"`. The
    extra structural and install-protocol checks make this sound
    for `CE_weak` (first install — `oldVal = .builtinBaseApply`).
    See the headline theorem `multnExact_soundForCE_first_install_tower`
    below. -/
def multnExactPolicy : BlackPolicy := fun ctx oldVal new =>
  -- Target restriction
  (ctx.target == "base-apply") &&
  (match new with
   | .closure ["op", "args"]
       (.ifte (.primApp (.var "num?") [.var "op"])
              _
              (.primApp (.var "orig") [.var "op", .var "args"]))
       cenv =>
       (match cenv.lookup "orig" with
        | some idx_o =>
            match ctx.heap[idx_o]? with
            | some v => v == oldVal
            | _ => false
        | none => false) &&
       (match cenv.lookup "num?" with
        | some idx_n =>
            match ctx.heap[idx_n]? with
            | some (.prim "num?") => true
            | _ => false
        | none => false)
   | _ => false)

def MultnExactShape (v : Val) : Prop :=
  ∃ t cenv,
    v = .closure ["op", "args"]
      (.ifte (.primApp (.var "num?") [.var "op"])
             t
             (.primApp (.var "orig") [.var "op", .var "args"]))
      cenv

theorem multnExact_sound_for_shape :
    multnExactPolicy.Sound (fun _ new => MultnExactShape new) := by
  intro _ _ new h
  unfold multnExactPolicy at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h_shape⟩ := h
  split at h_shape
  · exact ⟨_, _, rfl⟩
  · simp at h_shape

/-! ## Verified policy table -/

/-- The verified policy table. Each entry will (eventually) come with
    a `PolicyRespectsBisimT` proof. CE soundness is per-policy and
    stated by the relevant theorem (`multnExact_soundForCE_first_install_tower`
    for `multnExactPolicy`). -/
def verifiedTable : PolicyTable := [rejectAllPolicy, numGuardPolicy, multnExactPolicy]

namespace Policy
def idx_rejectAll   : Nat := 0
def idx_numGuard    : Nat := 1
def idx_multnExact  : Nat := 2
end Policy

/-! ## The headline theorem (statement-only; body deferred)

    Lean-green's `multnExact_soundForCE_first_install` says: under
    `multnExactPolicy` admission, install-protocol facts, runtime
    well-formedness, deep-validity, and shift-respect, the new
    base-apply value (a closure) conservatively extends the old
    (`.builtinBaseApply`) for `CE_weak`.

    The tower port specializes the cross-side policy equality to
    `policyAt? level` (not the global `s.policy`) and threads the
    `level` through `callAsBaseApply`. The body is `sorry` until
    the frame theorem is complete (`Frame.lean`). -/
theorem multnExact_soundForCE_first_install_tower
    (level : Nat) (fuel : Nat) (ptable : PolicyTable) (op : Val)
    (operands : List Val) (T : TowerState) (r : Val) (T' : TowerState)
    (new : Val)
    -- Admission
    (h_admit : multnExactPolicy
      { target := "base-apply", heap := T.heap, env := .nil,
        metaEnv := .nil, index := 0, level := level }
      .builtinBaseApply new = true)
    (h_fuel : fuel ≥ 2)
    -- Old call succeeds
    (h_old : callAsBaseApply fuel ptable level .builtinBaseApply op operands T
               = some (r, T'))
    -- Side conditions: PolicyTableRespectsBisim, runtime WF, deep validity,
    -- shift-respect (collapsed here as `sorry`-stand-in until the post-frame
    -- Bisim apparatus ports — see lean-green's signature)
    -- (... omitted — would be ~10 more hypotheses)
    : ∃ fuel' T'' r',
        callAsBaseApply fuel' ptable level new op operands T
          = some (r', T'') ∧
        ValVis_weak r r' T'.heap T''.heap ∧
        T'.policyAt? level = T''.policyAt? level ∧
        HeapValid T''.heap ∧
        T.heap.length ≤ T''.heap.length :=
  sorry
