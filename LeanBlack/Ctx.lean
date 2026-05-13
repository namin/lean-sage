/-
  lean-sage: Term contexts and a first cut at contextual β.

  A `Ctx` is an `Expr` with a single hole. `Ctx.plug` fills the hole.
  `EvalEquiv M N` says `M` and `N` produce the same set of outcomes
  across all initial states, at sufficient fuel — the most natural
  shape for an observational-equivalence claim that's stable under
  the existing fuel-monotonicity machinery.

  ## What this file gives you

  - The `Ctx` inductive (hole + per-`Expr`-constructor wrappers).
  - `Ctx.plug : Ctx → Expr → Expr`.
  - `EvalEquiv` and its closure under reflexivity, symmetry, transitivity.
  - `EvalEquiv.plug_hole` — trivial congruence at the hole.

  ## What's deferred

  Per-constructor congruence (`EvalEquiv.plug_ifteCond`, etc.) is the
  substantive work of T1 / contextual β. Each case unfolds the
  surrounding `eval` one step and applies the IH at the recursive
  sub-eval position, using `eval_fuel_mono` (from `EvalFuelMono.lean`)
  to bridge the differing fuel arithmetic between the LHS and RHS
  expressions. Not in this turn; the scaffolding is here.
-/

import LeanBlack.Black
import LeanBlack.Eval
import LeanBlack.EvalFuelMono

namespace LeanBlack

/-! ## Term contexts -/

/-- A term context: an `Expr` with a single hole. One constructor
    per `Expr`-shape with a recursive sub-expression position. -/
inductive Ctx where
  | hole       : Ctx
  | ifteCond   : Ctx → Expr → Expr → Ctx
  | ifteThen   : Expr → Ctx → Expr → Ctx
  | ifteElse   : Expr → Expr → Ctx → Ctx
  | lam        : List String → Ctx → Ctx
  /-- `.app (pre ++ hole :: post)`. Hole occupies position
      `pre.length` in the argument list. -/
  | app        : List Expr → Ctx → List Expr → Ctx
  | set        : String → Ctx → Ctx
  | em         : Ctx → Ctx
  | primAppFun : Ctx → List Expr → Ctx
  /-- `.primApp f (pre ++ hole :: post)`. -/
  | primAppArg : Expr → List Expr → Ctx → List Expr → Ctx
  | letEVal    : String → Ctx → Expr → Ctx
  | letEBody   : String → Expr → Ctx → Ctx
  /-- `.seq (pre ++ hole :: post)`. -/
  | seq        : List Expr → Ctx → List Expr → Ctx

/-- Fill the hole. -/
def Ctx.plug : Ctx → Expr → Expr
  | .hole, e => e
  | .ifteCond c et ee, e => .ifte (c.plug e) et ee
  | .ifteThen ec c ee, e => .ifte ec (c.plug e) ee
  | .ifteElse ec et c, e => .ifte ec et (c.plug e)
  | .lam ps c, e => .lam ps (c.plug e)
  | .app pre c post, e => .app (pre ++ c.plug e :: post)
  | .set x c, e => .set x (c.plug e)
  | .em c, e => .em (c.plug e)
  | .primAppFun c args, e => .primApp (c.plug e) args
  | .primAppArg f pre c post, e => .primApp f (pre ++ c.plug e :: post)
  | .letEVal x c body, e => .letE x (c.plug e) body
  | .letEBody x ev c, e => .letE x ev (c.plug e)
  | .seq pre c post, e => .seq (pre ++ c.plug e :: post)

@[simp] theorem Ctx.plug_hole (e : Expr) : Ctx.plug .hole e = e := rfl

/-! ## Observational equivalence (eval-convergence form)

`EvalEquiv M N` says: for every initial state and every observable
outcome `(v, T')`, the set of fuels under which `M` reaches that
outcome and the set of fuels under which `N` reaches it are
*non-empty* together or empty together — i.e., they converge to the
same observable.

By `eval_fuel_mono`, the existential-fuel formulation is equivalent
to "they agree at all sufficient fuel". -/

/-- Observational equivalence: same convergent outcomes across all
    starting states and policy tables. -/
def EvalEquiv (M N : Expr) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v : Val) (T' : TowerState),
    (∃ k, eval k ptable level M env T = some (v, T')) ↔
    (∃ k, eval k ptable level N env T = some (v, T'))

theorem EvalEquiv.refl (M : Expr) : EvalEquiv M M :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem EvalEquiv.symm {M N : Expr} (h : EvalEquiv M N) : EvalEquiv N M :=
  fun p l env T v T' => (h p l env T v T').symm

theorem EvalEquiv.trans {M N P : Expr}
    (h_MN : EvalEquiv M N) (h_NP : EvalEquiv N P) : EvalEquiv M P :=
  fun p l env T v T' => Iff.trans (h_MN p l env T v T') (h_NP p l env T v T')

/-! ## Plug compositionality

The substantive content of contextual β: `EvalEquiv M N` lifts
through any context. -/

/-- The hole case: trivial, since `plug .hole = id`. -/
theorem EvalEquiv.plug_hole {M N : Expr} (h : EvalEquiv M N) :
    EvalEquiv (Ctx.hole.plug M) (Ctx.hole.plug N) := by
  simp only [Ctx.plug_hole]; exact h

/-! ### Per-`Ctx`-constructor congruence

Each theorem below proves:
  `EvalEquiv M N → EvalEquiv (C.plug M) (C.plug N)`
for one `Ctx` constructor. The proof template:

1. `simp only [eval] at h_some` unfolds one `eval` step on the LHS,
   exposing the recursive sub-eval at the hole position.
2. Destructure the sub-eval result; the `none` branch is a
   contradiction with success of the outer eval.
3. Apply the IH (`EvalEquiv` hypothesis) to lift the sub-eval to
   the N-side, then use `eval_fuel_mono` to align fuels when
   re-assembling.
4. Reduce the outer match on the N-side; the post-sub-eval logic is
   identical on both sides (deterministic given the sub-eval result).

`.set x ·` is the simplest impure case: the hole occupies the only
recursive eval position, and the gate / env-lookup / heap-update
logic that follows is fully determined by `(v, T')`. -/

/-- `.set x ·`: contextual closure for the value position. -/
theorem EvalEquiv.plug_set {M N : Expr} (h : EvalEquiv M N) (x : String) :
    EvalEquiv (.set x M) (.set x N) := by
  intro ptable level env T v_final T_final
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_eM : eval k' ptable level M env T with
        | none => rw [h_eM] at h_some; simp at h_some
        | some pair =>
            obtain ⟨v_M, T_M⟩ := pair
            have h_N_ex : ∃ k_N, eval k_N ptable level N env T = some (v_M, T_M) :=
              (h ptable level env T v_M T_M).mp ⟨k', h_eM⟩
            obtain ⟨k_N, h_N⟩ := h_N_ex
            refine ⟨k_N + 1, ?_⟩
            rw [h_eM] at h_some
            simp only [eval, h_N]
            exact h_some
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_eN : eval k' ptable level N env T with
        | none => rw [h_eN] at h_some; simp at h_some
        | some pair =>
            obtain ⟨v_N, T_N⟩ := pair
            have h_M_ex : ∃ k_M, eval k_M ptable level M env T = some (v_N, T_N) :=
              (h ptable level env T v_N T_N).mpr ⟨k', h_eN⟩
            obtain ⟨k_M, h_M⟩ := h_M_ex
            refine ⟨k_M + 1, ?_⟩
            rw [h_eN] at h_some
            simp only [eval, h_M]
            exact h_some

/-- `.em ·`: hole in the body. Both sides materialize identically
    (deterministic given `T`); the IH fires at the new level. -/
theorem EvalEquiv.em_cong {M N : Expr} (h : EvalEquiv M N) :
    EvalEquiv (.em M) (.em N) := by
  intro ptable level env T v_final T_final
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_mat : T.materialize (level + 1) with
        | none => rw [h_mat] at h_some; simp at h_some
        | some T_mat =>
            rw [h_mat] at h_some
            simp at h_some
            cases h_env : T_mat.envAt? (level + 1) with
            | none => rw [h_env] at h_some; simp at h_some
            | some upEnv =>
                rw [h_env] at h_some
                simp at h_some
                have h_N_ex :=
                  (h ptable (level+1) upEnv T_mat v_final T_final).mp ⟨k', h_some⟩
                obtain ⟨k_N, h_N⟩ := h_N_ex
                refine ⟨k_N + 1, ?_⟩
                simp only [eval, h_mat]
                simp [h_env, h_N]
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_mat : T.materialize (level + 1) with
        | none => rw [h_mat] at h_some; simp at h_some
        | some T_mat =>
            rw [h_mat] at h_some
            simp at h_some
            cases h_env : T_mat.envAt? (level + 1) with
            | none => rw [h_env] at h_some; simp at h_some
            | some upEnv =>
                rw [h_env] at h_some
                simp at h_some
                have h_M_ex :=
                  (h ptable (level+1) upEnv T_mat v_final T_final).mpr ⟨k', h_some⟩
                obtain ⟨k_M, h_M⟩ := h_M_ex
                refine ⟨k_M + 1, ?_⟩
                simp only [eval, h_mat]
                simp [h_env, h_M]

/-- `.letE x · body`: hole in the value position. -/
theorem EvalEquiv.letEVal_cong {M N : Expr} (h : EvalEquiv M N)
    (x : String) (body : Expr) :
    EvalEquiv (.letE x M body) (.letE x N body) := by
  intro ptable level env T v_final T_final
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_eM : eval k' ptable level M env T with
        | none => rw [h_eM] at h_some; simp at h_some
        | some pair =>
            obtain ⟨v_M, T_M⟩ := pair
            rw [h_eM] at h_some
            simp only at h_some
            have h_N_ex : ∃ k_N, eval k_N ptable level N env T = some (v_M, T_M) :=
              (h ptable level env T v_M T_M).mp ⟨k', h_eM⟩
            obtain ⟨k_N, h_N⟩ := h_N_ex
            let K := max k' k_N
            have h_le1 : k' ≤ K := Nat.le_max_left _ _
            have h_le2 : k_N ≤ K := Nat.le_max_right _ _
            refine ⟨K + 1, ?_⟩
            simp only [eval, eval_fuel_mono h_le2 h_N]
            exact eval_fuel_mono h_le1 h_some
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_eN : eval k' ptable level N env T with
        | none => rw [h_eN] at h_some; simp at h_some
        | some pair =>
            obtain ⟨v_N, T_N⟩ := pair
            rw [h_eN] at h_some
            simp only at h_some
            have h_M_ex : ∃ k_M, eval k_M ptable level M env T = some (v_N, T_N) :=
              (h ptable level env T v_N T_N).mpr ⟨k', h_eN⟩
            obtain ⟨k_M, h_M⟩ := h_M_ex
            let K := max k' k_M
            have h_le1 : k' ≤ K := Nat.le_max_left _ _
            have h_le2 : k_M ≤ K := Nat.le_max_right _ _
            refine ⟨K + 1, ?_⟩
            simp only [eval, eval_fuel_mono h_le2 h_M]
            exact eval_fuel_mono h_le1 h_some

/-- `.letE x ev ·`: hole in the body. The `ev` sub-eval is identical
    on both sides; the IH fires on the body in the post-alloc state. -/
theorem EvalEquiv.letEBody_cong {M N : Expr} (h : EvalEquiv M N)
    (x : String) (ev : Expr) :
    EvalEquiv (.letE x ev M) (.letE x ev N) := by
  intro ptable level env T v_final T_final
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_ev : eval k' ptable level ev env T with
        | none => rw [h_ev] at h_some; simp at h_some
        | some pair =>
            obtain ⟨v_ev, T_ev⟩ := pair
            rw [h_ev] at h_some
            simp only at h_some
            -- h_some : eval k' ptable level M
            --   (.cons x T_ev.heap.length env)
            --   {T_ev with heap := T_ev.heap ++ [v_ev]} = some(v_final, T_final)
            have h_N_ex := (h ptable level
              (.cons x T_ev.heap.length env)
              {T_ev with heap := T_ev.heap ++ [v_ev]}
              v_final T_final).mp ⟨k', h_some⟩
            obtain ⟨k_N, h_N⟩ := h_N_ex
            let K := max k' k_N
            have h_le1 : k' ≤ K := Nat.le_max_left _ _
            have h_le2 : k_N ≤ K := Nat.le_max_right _ _
            refine ⟨K + 1, ?_⟩
            simp only [eval, eval_fuel_mono h_le1 h_ev]
            exact eval_fuel_mono h_le2 h_N
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_ev : eval k' ptable level ev env T with
        | none => rw [h_ev] at h_some; simp at h_some
        | some pair =>
            obtain ⟨v_ev, T_ev⟩ := pair
            rw [h_ev] at h_some
            simp only at h_some
            have h_M_ex := (h ptable level
              (.cons x T_ev.heap.length env)
              {T_ev with heap := T_ev.heap ++ [v_ev]}
              v_final T_final).mpr ⟨k', h_some⟩
            obtain ⟨k_M, h_M⟩ := h_M_ex
            let K := max k' k_M
            have h_le1 : k' ≤ K := Nat.le_max_left _ _
            have h_le2 : k_M ≤ K := Nat.le_max_right _ _
            refine ⟨K + 1, ?_⟩
            simp only [eval, eval_fuel_mono h_le1 h_ev]
            exact eval_fuel_mono h_le2 h_M

/-- Helper for `.ifteCond_cong`: lifts the one-directional forward
    implication of the `EvalEquiv` iff. -/
private theorem ifteCond_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (t e : Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.ifte M t e) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.ifte N t e) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_ec : eval k' ptable level M env T with
      | none => rw [h_ec] at h_some; simp at h_some
      | some pair =>
          obtain ⟨v_c, T_c⟩ := pair
          have h_N_ex : ∃ k_N, eval k_N ptable level N env T = some (v_c, T_c) :=
            (h ptable level env T v_c T_c).mp ⟨k', h_ec⟩
          obtain ⟨k_N, h_N⟩ := h_N_ex
          rw [h_ec] at h_some
          let K := max k' k_N
          have h_le1 : k' ≤ K := Nat.le_max_left _ _
          have h_le2 : k_N ≤ K := Nat.le_max_right _ _
          refine ⟨K + 1, ?_⟩
          simp only [eval, eval_fuel_mono h_le2 h_N]
          cases v_c with
          | bool b =>
              cases b with
              | false => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
              | true  => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | num _            => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | nilV             => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | sym _            => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | cons _ _         => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | closure _ _ _    => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | prim _           => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some
          | builtinBaseApply => simp at h_some ⊢; exact eval_fuel_mono h_le1 h_some

/-- `.ifte · t e`: hole in the condition. The branch eval (`t` or
    `e`) depends on the cond's value but is identical on both sides
    once the value matches; the IH lifts the cond eval. -/
theorem EvalEquiv.ifteCond_cong {M N : Expr} (h : EvalEquiv M N)
    (t e : Expr) :
    EvalEquiv (.ifte M t e) (.ifte N t e) := by
  intro ptable level env T v_final T_final
  exact ⟨ifteCond_cong_forward h t e ptable level env T v_final T_final,
         ifteCond_cong_forward h.symm t e ptable level env T v_final T_final⟩

/-- Helper for `.ifteThen_cong`: lifts the one-directional forward
    implication. The IH on `M ≡ N` fires when `v_c ≠ .bool false`
    (then-branch active); the `.bool false` case is independent of
    the hole. -/
private theorem ifteThen_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (ec ee : Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.ifte ec M ee) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.ifte ec N ee) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_ec : eval k' ptable level ec env T with
      | none => rw [h_ec] at h_some; simp at h_some
      | some pair =>
          obtain ⟨v_c, T_c⟩ := pair
          rw [h_ec] at h_some
          -- After rw + cases v_c, iota reduces h_some to the active branch's eval.
          -- The .bool false branch picks `ee`; every other branch picks `M`.
          cases v_c with
          | bool b =>
              cases b with
              | false =>
                  -- h_some : eval k' ptable level ee env T_c = some (v_final, T_final)
                  refine ⟨k' + 1, ?_⟩
                  simp only [eval, h_ec]
                  exact h_some
              | true =>
                  have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
                  obtain ⟨k_N, h_N⟩ := h_N_ex
                  refine ⟨max k' k_N + 1, ?_⟩
                  simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
                  exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | num _ =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | nilV =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | sym _ =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | cons _ _ =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | closure _ _ _ =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | prim _ =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | builtinBaseApply =>
              have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N

/-- `.ifte ec · ee`: hole in the then-branch. IH fires for any
    `v_c ≠ .bool false`; the false-branch is independent. -/
theorem EvalEquiv.ifteThen_cong {M N : Expr} (h : EvalEquiv M N)
    (ec ee : Expr) :
    EvalEquiv (.ifte ec M ee) (.ifte ec N ee) := by
  intro ptable level env T v_final T_final
  exact ⟨ifteThen_cong_forward h ec ee ptable level env T v_final T_final,
         ifteThen_cong_forward h.symm ec ee ptable level env T v_final T_final⟩

/-- Helper for `.ifteElse_cong`. -/
private theorem ifteElse_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (ec t : Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.ifte ec t M) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.ifte ec t N) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_ec : eval k' ptable level ec env T with
      | none => rw [h_ec] at h_some; simp at h_some
      | some pair =>
          obtain ⟨v_c, T_c⟩ := pair
          rw [h_ec] at h_some
          cases v_c with
          | bool b =>
              cases b with
              | false =>
                  -- M branch (else): apply IH
                  have h_N_ex := (h ptable level env T_c v_final T_final).mp ⟨k', h_some⟩
                  obtain ⟨k_N, h_N⟩ := h_N_ex
                  refine ⟨max k' k_N + 1, ?_⟩
                  simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
                  exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
              | true =>
                  refine ⟨k' + 1, ?_⟩
                  simp only [eval, h_ec]; exact h_some
          | num _ =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some
          | nilV =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some
          | sym _ =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some
          | cons _ _ =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some
          | closure _ _ _ =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some
          | prim _ =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some
          | builtinBaseApply =>
              refine ⟨k' + 1, ?_⟩
              simp only [eval, h_ec]; exact h_some

/-- `.ifte ec t ·`: hole in the else-branch. IH fires only on
    `v_c = .bool false`; other cases take `t`. -/
theorem EvalEquiv.ifteElse_cong {M N : Expr} (h : EvalEquiv M N)
    (ec t : Expr) :
    EvalEquiv (.ifte ec t M) (.ifte ec t N) := by
  intro ptable level env T v_final T_final
  exact ⟨ifteElse_cong_forward h ec t ptable level env T v_final T_final,
         ifteElse_cong_forward h.symm ec t ptable level env T v_final T_final⟩

/-- Helper for `.primAppFun_cong`. -/
private theorem primAppFun_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (args : List Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.primApp M args) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.primApp N args) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_ef : eval k' ptable level M env T with
      | none => rw [h_ef] at h_some; simp at h_some
      | some pair =>
          obtain ⟨fv, T_f⟩ := pair
          have h_N_ex := (h ptable level env T fv T_f).mp ⟨k', h_ef⟩
          obtain ⟨k_N, h_N⟩ := h_N_ex
          rw [h_ef] at h_some
          simp only at h_some
          cases h_el : evalList k' ptable level args env T_f with
          | none => rw [h_el] at h_some; simp at h_some
          | some pair' =>
              obtain ⟨avs, T_a⟩ := pair'
              rw [h_el] at h_some
              simp only at h_some
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_right k' k_N) h_N,
                         evalList_fuel_mono (Nat.le_max_left k' k_N) h_el]
              exact applyDirect_fuel_mono (Nat.le_max_left k' k_N) h_some

/-- `.primApp · args`: hole in the function position. -/
theorem EvalEquiv.primAppFun_cong {M N : Expr} (h : EvalEquiv M N)
    (args : List Expr) :
    EvalEquiv (.primApp M args) (.primApp N args) := by
  intro ptable level env T v_final T_final
  exact ⟨primAppFun_cong_forward h args ptable level env T v_final T_final,
         primAppFun_cong_forward h.symm args ptable level env T v_final T_final⟩

/-- Helper for `.appHead_cong`. Mirrors `primAppFun_cong_forward`
    but with `applyVia` in place of `applyDirect`. -/
private theorem appHead_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (args : List Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.app (M :: args)) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.app (N :: args)) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_ef : eval k' ptable level M env T with
      | none => rw [h_ef] at h_some; simp at h_some
      | some pair =>
          obtain ⟨fv, T_f⟩ := pair
          have h_N_ex := (h ptable level env T fv T_f).mp ⟨k', h_ef⟩
          obtain ⟨k_N, h_N⟩ := h_N_ex
          rw [h_ef] at h_some
          simp only at h_some
          cases h_el : evalList k' ptable level args env T_f with
          | none => rw [h_el] at h_some; simp at h_some
          | some pair' =>
              obtain ⟨avs, T_a⟩ := pair'
              rw [h_el] at h_some
              simp only at h_some
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_right k' k_N) h_N,
                         evalList_fuel_mono (Nat.le_max_left k' k_N) h_el]
              exact applyVia_fuel_mono (Nat.le_max_left k' k_N) h_some

/-- `.app (· :: args)`: hole at the function position of an app. -/
theorem EvalEquiv.appHead_cong {M N : Expr} (h : EvalEquiv M N)
    (args : List Expr) :
    EvalEquiv (.app (M :: args)) (.app (N :: args)) := by
  intro ptable level env T v_final T_final
  exact ⟨appHead_cong_forward h args ptable level env T v_final T_final,
         appHead_cong_forward h.symm args ptable level env T v_final T_final⟩

/-- Helper for `.seqHead_cong`. Splits on whether `rest` is empty
    (single-element `.seq [M]`) or not (multi-element). -/
private theorem seqHead_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (rest : List Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.seq (M :: rest)) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.seq (N :: rest)) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      cases rest with
      | nil =>
          -- .seq [M] reduces to eval M directly.
          simp only [eval] at h_some
          have h_N_ex := (h ptable level env T v_final T_final).mp ⟨k', h_some⟩
          obtain ⟨k_N, h_N⟩ := h_N_ex
          refine ⟨k_N + 1, ?_⟩
          simp only [eval]; exact h_N
      | cons e2 rest' =>
          simp only [eval] at h_some
          cases h_eM : eval k' ptable level M env T with
          | none => rw [h_eM] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_M, T_M⟩ := pair
              have h_N_ex := (h ptable level env T v_M T_M).mp ⟨k', h_eM⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              rw [h_eM] at h_some
              simp only at h_some
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_right k' k_N) h_N]
              exact eval_fuel_mono (Nat.le_max_left k' k_N) h_some

/-- `.seq (· :: rest)`: hole at the head of a seq. -/
theorem EvalEquiv.seqHead_cong {M N : Expr} (h : EvalEquiv M N)
    (rest : List Expr) :
    EvalEquiv (.seq (M :: rest)) (.seq (N :: rest)) := by
  intro ptable level env T v_final T_final
  exact ⟨seqHead_cong_forward h rest ptable level env T v_final T_final,
         seqHead_cong_forward h.symm rest ptable level env T v_final T_final⟩

/-! ### List-position congruence

`evalList_EvalEquiv_forward` is the list-traversal helper: if
`M ≡ N`, then for any prefix and suffix lists, `evalList` produces
the same outcomes on `pre ++ M :: post` and `pre ++ N :: post`.

Induction on `pre`:
- `pre = []`: hole at head of list. Eval M, evalList post.
- `pre = h_pre :: pre_rest`: eval h_pre (same on both sides),
  then IH applies on `pre_rest`. -/

private theorem evalList_EvalEquiv_forward {M N : Expr} (h : EvalEquiv M N) :
    ∀ (pre post : List Expr) (ptable : PolicyTable) (level : Nat)
      (env : Env) (T : TowerState) (vs : List Val) (T' : TowerState),
      (∃ k, evalList k ptable level (pre ++ M :: post) env T = some (vs, T')) →
      (∃ k, evalList k ptable level (pre ++ N :: post) env T = some (vs, T')) := by
  intro pre
  induction pre with
  | nil =>
      intro post ptable level env T vs T' ⟨k, h_some⟩
      cases k with
      | zero => simp [evalList] at h_some
      | succ k' =>
          simp only [List.nil_append, evalList] at h_some
          cases h_eM : eval k' ptable level M env T with
          | none => rw [h_eM] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_M, T_M⟩ := pair
              have h_N_ex := (h ptable level env T v_M T_M).mp ⟨k', h_eM⟩
              obtain ⟨k_N, h_N⟩ := h_N_ex
              rw [h_eM] at h_some
              simp only at h_some
              cases h_eList : evalList k' ptable level post env T_M with
              | none => rw [h_eList] at h_some; simp at h_some
              | some pair' =>
                  obtain ⟨vs_rest, T_rest⟩ := pair'
                  rw [h_eList] at h_some
                  simp only at h_some
                  refine ⟨max k' k_N + 1, ?_⟩
                  simp only [List.nil_append, evalList,
                             eval_fuel_mono (Nat.le_max_right k' k_N) h_N,
                             evalList_fuel_mono (Nat.le_max_left k' k_N) h_eList]
                  exact h_some
  | cons h_pre pre_rest ih =>
      intro post ptable level env T vs T' ⟨k, h_some⟩
      cases k with
      | zero => simp [evalList] at h_some
      | succ k' =>
          simp only [List.cons_append, evalList] at h_some
          cases h_eH : eval k' ptable level h_pre env T with
          | none => rw [h_eH] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_h, T_h⟩ := pair
              rw [h_eH] at h_some
              simp only at h_some
              cases h_eList : evalList k' ptable level (pre_rest ++ M :: post) env T_h with
              | none => rw [h_eList] at h_some; simp at h_some
              | some pair' =>
                  obtain ⟨vs_rest, T_rest⟩ := pair'
                  rw [h_eList] at h_some
                  simp only at h_some
                  have h_ih := ih post ptable level env T_h vs_rest T_rest ⟨k', h_eList⟩
                  obtain ⟨k_N_inner, h_eList_N⟩ := h_ih
                  refine ⟨max k' k_N_inner + 1, ?_⟩
                  simp only [List.cons_append, evalList,
                             eval_fuel_mono (Nat.le_max_left k' k_N_inner) h_eH,
                             evalList_fuel_mono (Nat.le_max_right k' k_N_inner) h_eList_N]
                  exact h_some

theorem evalList_EvalEquiv {M N : Expr} (h : EvalEquiv M N)
    (pre post : List Expr) (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState) (vs : List Val) (T' : TowerState) :
    (∃ k, evalList k ptable level (pre ++ M :: post) env T = some (vs, T')) ↔
    (∃ k, evalList k ptable level (pre ++ N :: post) env T = some (vs, T')) :=
  ⟨evalList_EvalEquiv_forward h pre post ptable level env T vs T',
   evalList_EvalEquiv_forward h.symm pre post ptable level env T vs T'⟩

/-- Helper for `.appArg_cong`. -/
private theorem appArg_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (head : Expr) (pre' post : List Expr) (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState) (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.app (head :: (pre' ++ M :: post))) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.app (head :: (pre' ++ N :: post))) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_eH : eval k' ptable level head env T with
      | none => rw [h_eH] at h_some; simp at h_some
      | some pair =>
          obtain ⟨fv, T_h⟩ := pair
          rw [h_eH] at h_some
          simp only at h_some
          cases h_eL : evalList k' ptable level (pre' ++ M :: post) env T_h with
          | none => rw [h_eL] at h_some; simp at h_some
          | some pair' =>
              obtain ⟨avs, T_a⟩ := pair'
              rw [h_eL] at h_some
              simp only at h_some
              obtain ⟨k_N, h_eL_N⟩ :=
                (evalList_EvalEquiv h pre' post ptable level env T_h avs T_a).mp ⟨k', h_eL⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_eH,
                         evalList_fuel_mono (Nat.le_max_right k' k_N) h_eL_N]
              exact applyVia_fuel_mono (Nat.le_max_left k' k_N) h_some

/-- `.app (head :: pre ++ · :: post)`: hole at an arg position. -/
theorem EvalEquiv.appArg_cong {M N : Expr} (h : EvalEquiv M N)
    (head : Expr) (pre' post : List Expr) :
    EvalEquiv (.app (head :: (pre' ++ M :: post)))
              (.app (head :: (pre' ++ N :: post))) := by
  intro ptable level env T v_final T_final
  exact ⟨appArg_cong_forward h head pre' post ptable level env T v_final T_final,
         appArg_cong_forward h.symm head pre' post ptable level env T v_final T_final⟩

/-- Helper for `.primAppArg_cong`. Same as `appArg` with `applyDirect` instead of `applyVia`. -/
private theorem primAppArg_cong_forward {M N : Expr} (h : EvalEquiv M N)
    (f : Expr) (pre' post : List Expr) (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState) (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.primApp f (pre' ++ M :: post)) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.primApp f (pre' ++ N :: post)) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      simp only [eval] at h_some
      cases h_eF : eval k' ptable level f env T with
      | none => rw [h_eF] at h_some; simp at h_some
      | some pair =>
          obtain ⟨fv, T_f⟩ := pair
          rw [h_eF] at h_some
          simp only at h_some
          cases h_eL : evalList k' ptable level (pre' ++ M :: post) env T_f with
          | none => rw [h_eL] at h_some; simp at h_some
          | some pair' =>
              obtain ⟨avs, T_a⟩ := pair'
              rw [h_eL] at h_some
              simp only at h_some
              obtain ⟨k_N, h_eL_N⟩ :=
                (evalList_EvalEquiv h pre' post ptable level env T_f avs T_a).mp ⟨k', h_eL⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_eF,
                         evalList_fuel_mono (Nat.le_max_right k' k_N) h_eL_N]
              exact applyDirect_fuel_mono (Nat.le_max_left k' k_N) h_some

/-- `.primApp f (pre ++ · :: post)`: hole at an arg position. -/
theorem EvalEquiv.primAppArg_cong {M N : Expr} (h : EvalEquiv M N)
    (f : Expr) (pre' post : List Expr) :
    EvalEquiv (.primApp f (pre' ++ M :: post))
              (.primApp f (pre' ++ N :: post)) := by
  intro ptable level env T v_final T_final
  exact ⟨primAppArg_cong_forward h f pre' post ptable level env T v_final T_final,
         primAppArg_cong_forward h.symm f pre' post ptable level env T v_final T_final⟩

/-! ### Sub-language with full coverage

`SimpleCtx` is the fragment of `Ctx` whose constructors all have
proven congruence lemmas above. Its `plug_cong` follows by
induction. -/

inductive SimpleCtx where
  | hole       : SimpleCtx
  | ifteCond   : SimpleCtx → Expr → Expr → SimpleCtx
  | ifteThen   : Expr → SimpleCtx → Expr → SimpleCtx
  | ifteElse   : Expr → Expr → SimpleCtx → SimpleCtx
  | set        : String → SimpleCtx → SimpleCtx
  | em         : SimpleCtx → SimpleCtx
  | letEVal    : String → SimpleCtx → Expr → SimpleCtx
  | letEBody   : String → Expr → SimpleCtx → SimpleCtx
  | appHead    : SimpleCtx → List Expr → SimpleCtx
  | appArg     : Expr → List Expr → SimpleCtx → List Expr → SimpleCtx
  | primAppFun : SimpleCtx → List Expr → SimpleCtx
  | primAppArg : Expr → List Expr → SimpleCtx → List Expr → SimpleCtx
  | seqHead    : SimpleCtx → List Expr → SimpleCtx

def SimpleCtx.plug : SimpleCtx → Expr → Expr
  | .hole,             e => e
  | .ifteCond c t' e', e => .ifte (c.plug e) t' e'
  | .ifteThen ec c ee, e => .ifte ec (c.plug e) ee
  | .ifteElse ec t c,  e => .ifte ec t (c.plug e)
  | .set x c,          e => .set x (c.plug e)
  | .em c,             e => .em (c.plug e)
  | .letEVal x c b,    e => .letE x (c.plug e) b
  | .letEBody x ev c,  e => .letE x ev (c.plug e)
  | .appHead c args,   e => .app (c.plug e :: args)
  | .appArg hd pre c post, e => .app (hd :: (pre ++ c.plug e :: post))
  | .primAppFun c args,e => .primApp (c.plug e) args
  | .primAppArg f pre c post, e => .primApp f (pre ++ c.plug e :: post)
  | .seqHead c rest,   e => .seq (c.plug e :: rest)

theorem SimpleCtx.plug_cong : ∀ (C : SimpleCtx) {M N : Expr},
    EvalEquiv M N → EvalEquiv (C.plug M) (C.plug N) := by
  intro C
  induction C with
  | hole =>
      intros M N h
      simp only [SimpleCtx.plug]; exact h
  | ifteCond c t' e' ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.ifteCond_cong (ih h) t' e'
  | ifteThen ec c ee ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.ifteThen_cong (ih h) ec ee
  | ifteElse ec t c ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.ifteElse_cong (ih h) ec t
  | set x c ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.plug_set (ih h) x
  | em c ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.em_cong (ih h)
  | letEVal x c b ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.letEVal_cong (ih h) x b
  | letEBody x ev c ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.letEBody_cong (ih h) x ev
  | appHead c args ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.appHead_cong (ih h) args
  | appArg hd pre c post ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.appArg_cong (ih h) hd pre post
  | primAppFun c args ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.primAppFun_cong (ih h) args
  | primAppArg f pre c post ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.primAppArg_cong (ih h) f pre post
  | seqHead c rest ih =>
      intros M N h
      simp only [SimpleCtx.plug]
      exact EvalEquiv.seqHead_cong (ih h) rest

/-! ### Remaining per-`Ctx` cases — TODO

`.lam ps ·`: the body appears under a closure value. Strict
equality fails because `eval (.lam ps M) = some (.closure ps M env, T)`
and the closure value embeds `M` literally — so the two closures
on the two sides differ syntactically. The right closure form
under contextual β is `ValVis`-style syntactic refinement.

`.app pre · post`, `.primAppFun`, `.primAppArg`, `.seq`:
case-split on list traversal at the hole position; analogous to
`.letEVal` for the head case and `.letEBody` for tail positions. -/

end LeanBlack
