/-
  lean-sage: Term contexts, observational equivalence, and the
  per-constructor congruence lemmas.

  A `Ctx` is an `Expr` with a single hole — THE context language
  (there is exactly one). `Ctx.plug` fills the hole. `EvalEquiv M N`
  says `M` and `N` produce the same set of outcomes across all
  initial states, at sufficient fuel; `EvalEquivAt P` is the
  conditional form, restricted to states satisfying a predicate.

  ## What this file gives you

  - The `Ctx` inductive (hole + per-`Expr`-constructor wrappers)
    and `Ctx.plug`.
  - `EvalEquiv` / `EvalEquivAt` with their equivalence-relation
    structure, and concrete unconditional witnesses.
  - The per-constructor `EvalEquivAt` congruence lemmas: the six
    "easy" positions (hole's sub-eval sees the outer state) and the
    "hard" positions (`.ifteThen`, `.ifteElse`, `.letEBody`), the
    latter parameterized by explicit preservation hypotheses.

  The list-position congruences, the side conditions on a context
  (`lamFree` / `emDepth` / `sidesOK`), and the single master
  congruence `Ctx.plug_cong_master` with its tier instantiations
  live in `LeanBlack/CtxPure.lean`. The sole uncovered position is
  `.lam` (hole under a binder) — see `SCOPE.md`.
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

/-! ### Unconditional `EvalEquiv` witnesses

These are concrete `EvalEquiv` proofs that hold across all states.
They demonstrate the framework and act as building blocks for
constructing β-equivalences via `EvalEquiv.trans`. The β-redex /
`.letE` pair is *not* in this list — it depends on the surrounding
state (specifically, `builtinBaseApplyAt level T'` for the post-
`v_expr` state), so the natural shape there is a conditional
`EvalEquivAt`. -/

/-- `eval (.seq [e]) ≡ eval e`: a single-element seq is observably
    the same as its content. The fuel offsets by 1 but
    `eval_fuel_mono` aligns. -/
theorem EvalEquiv.seq_singleton (e : Expr) : EvalEquiv (.seq [e]) e := by
  intro ptable level env T v T'
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        exact ⟨k', h_some⟩
  · rintro ⟨k, h_some⟩
    refine ⟨k + 1, ?_⟩
    simp only [eval]; exact h_some

/-- `eval (.seq []) ≡ eval (.quote .nilV)`: the empty seq is
    observationally equivalent to a quoted nil. -/
theorem EvalEquiv.seq_nil : EvalEquiv (.seq []) (.quote .nilV) := by
  intro ptable level env T v T'
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        exact ⟨k' + 1, by simp only [eval, closedValB]; exact h_some⟩
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval, closedValB] at h_some
        exact ⟨k' + 1, by simp only [eval]; exact h_some⟩

/-- `eval (.ifte (.bool true) t e) ≡ eval t`: the `if` of a true
    literal reduces to its then-branch. -/
theorem EvalEquiv.ifte_true (t e : Expr) :
    EvalEquiv (.ifte (.bool true) t e) t := by
  intro ptable level env T v T'
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        cases k' with
        | zero => simp [eval] at h_some
        | succ k'' =>
            simp only [eval] at h_some
            exact ⟨k'' + 1, h_some⟩
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        refine ⟨k' + 2, ?_⟩
        simp only [eval]; exact h_some

/-- `eval (.ifte (.bool false) t e) ≡ eval e`: the `if` of a false
    literal reduces to its else-branch. -/
theorem EvalEquiv.ifte_false (t e : Expr) :
    EvalEquiv (.ifte (.bool false) t e) e := by
  intro ptable level env T v T'
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        cases k' with
        | zero => simp [eval] at h_some
        | succ k'' =>
            simp only [eval] at h_some
            exact ⟨k'' + 1, h_some⟩
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        refine ⟨k' + 2, ?_⟩
        simp only [eval]; exact h_some

/-! ## Conditional `EvalEquivAt` — state-predicate-parameterized equivalence

`EvalEquivAt P M N` says: at every starting state satisfying `P`,
`M` and `N` produce the same convergent outcomes. The `Ctx`
congruence lemmas come in two flavors:

- **"Easy" cases** — the hole's sub-eval position has the *same*
  state as the outer call (`.set`, `.ifteCond`, `.letEVal`,
  `.appHead`, `.primAppFun`, `.seqHead`). For these, `P` at the
  outer state implies `P` at the inner state trivially; the proof
  threads `hP` through the IH and is otherwise identical to the
  `EvalEquiv` version.

- **"Hard" cases** — the hole's sub-eval happens at a *different*
  state (after evaluating a sibling sub-expression: `.ifteThen`,
  `.ifteElse`, `.em`, `.letEBody`, `.appArg`, `.primAppArg`,
  `.seqTail`). These need an explicit hypothesis that `P` is
  preserved by the relevant intermediate evaluation. Provided as
  separate lemmas with `P`-preservation hypotheses; the user
  supplies the per-`P` preservation proof.

The framework lets you combine `beta_letE_conv_equiv` (the base
case at the hole) with `EvalEquivAt.plug_*_cong` for any `Ctx`
satisfying the relevant preservation properties, yielding
contextually-quantified β-equivalence. -/

/-- A state predicate over `ptable`, `level`, `env`, and `T`.
    Includes `PolicyTable` so predicates can reference `eval` of
    auxiliary expressions (e.g., the L1 conditions for β-redex). -/
abbrev StatePred := PolicyTable → Nat → Env → TowerState → Prop

/-- Conditional observational equivalence: same convergent outcomes
    across starting states *satisfying `P`*. -/
def EvalEquivAt (P : StatePred) (M N : Expr) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState),
    P ptable level env T →
    ∀ (v : Val) (T' : TowerState),
      (∃ k, eval k ptable level M env T = some (v, T')) ↔
      (∃ k, eval k ptable level N env T = some (v, T'))

/-- Strict `EvalEquiv` lifts to any `EvalEquivAt`: a stronger
    hypothesis. -/
theorem EvalEquiv.toEvalEquivAt {M N : Expr} (h : EvalEquiv M N)
    (P : StatePred) : EvalEquivAt P M N :=
  fun ptable level env T _ v T' => h ptable level env T v T'

theorem EvalEquivAt.refl (P : StatePred) (M : Expr) : EvalEquivAt P M M :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem EvalEquivAt.symm {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) : EvalEquivAt P N M :=
  fun ptable level env T hP v T' => (h ptable level env T hP v T').symm

theorem EvalEquivAt.trans {P : StatePred} {M N R : Expr}
    (h1 : EvalEquivAt P M N) (h2 : EvalEquivAt P N R) : EvalEquivAt P M R :=
  fun ptable level env T hP v T' =>
    Iff.trans (h1 ptable level env T hP v T') (h2 ptable level env T hP v T')

/-! ### "Easy" cases — inner state equals outer state -/

/-- `.set x ·`: the hole's eval position is the outer state. `P`
    at outer ⇒ `P` at inner trivially. -/
theorem EvalEquivAt.set_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (x : String) :
    EvalEquivAt P (.set x M) (.set x N) := by
  intro ptable level env T hP v_final T_final
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
            obtain ⟨k_N, h_N⟩ := (h ptable level env T hP v_M T_M).mp ⟨k', h_eM⟩
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
            obtain ⟨k_M, h_M⟩ := (h ptable level env T hP v_N T_N).mpr ⟨k', h_eN⟩
            refine ⟨k_M + 1, ?_⟩
            rw [h_eN] at h_some
            simp only [eval, h_M]
            exact h_some

/-- `.ifte · t e`: hole in the condition (same outer state). -/
private theorem ifteCond_cong_at_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N)
    (t e : Expr) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
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
          obtain ⟨k_N, h_N⟩ := (h ptable level env T hP v_c T_c).mp ⟨k', h_ec⟩
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

theorem EvalEquivAt.ifteCond_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (t e : Expr) :
    EvalEquivAt P (.ifte M t e) (.ifte N t e) := by
  intro ptable level env T hP v_final T_final
  exact ⟨ifteCond_cong_at_forward h t e ptable level env T hP v_final T_final,
         ifteCond_cong_at_forward h.symm t e ptable level env T hP v_final T_final⟩

/-- `.letE x · body`: hole in the value position (same outer state). -/
theorem EvalEquivAt.letEVal_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (x : String) (body : Expr) :
    EvalEquivAt P (.letE x M body) (.letE x N body) := by
  intro ptable level env T hP v_final T_final
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
              (h ptable level env T hP v_M T_M).mp ⟨k', h_eM⟩
            obtain ⟨k_N, h_N⟩ := h_N_ex
            refine ⟨max k' k_N + 1, ?_⟩
            simp only [eval, eval_fuel_mono (Nat.le_max_right k' k_N) h_N]
            exact eval_fuel_mono (Nat.le_max_left k' k_N) h_some
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
              (h ptable level env T hP v_N T_N).mpr ⟨k', h_eN⟩
            obtain ⟨k_M, h_M⟩ := h_M_ex
            refine ⟨max k' k_M + 1, ?_⟩
            simp only [eval, eval_fuel_mono (Nat.le_max_right k' k_M) h_M]
            exact eval_fuel_mono (Nat.le_max_left k' k_M) h_some

/-- `.app (· :: args)`: hole at the function position (same outer state). -/
private theorem appHead_cong_at_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (args : List Expr)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
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
          obtain ⟨k_N, h_N⟩ := (h ptable level env T hP fv T_f).mp ⟨k', h_ef⟩
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

theorem EvalEquivAt.appHead_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (args : List Expr) :
    EvalEquivAt P (.app (M :: args)) (.app (N :: args)) := by
  intro ptable level env T hP v_final T_final
  exact ⟨appHead_cong_at_forward h args ptable level env T hP v_final T_final,
         appHead_cong_at_forward h.symm args ptable level env T hP v_final T_final⟩

/-- `.primApp · args`: hole at the function position (same outer state). -/
private theorem primAppFun_cong_at_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (args : List Expr)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
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
          obtain ⟨k_N, h_N⟩ := (h ptable level env T hP fv T_f).mp ⟨k', h_ef⟩
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

theorem EvalEquivAt.primAppFun_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (args : List Expr) :
    EvalEquivAt P (.primApp M args) (.primApp N args) := by
  intro ptable level env T hP v_final T_final
  exact ⟨primAppFun_cong_at_forward h args ptable level env T hP v_final T_final,
         primAppFun_cong_at_forward h.symm args ptable level env T hP v_final T_final⟩

/-- `.seq (· :: rest)`: hole at the head of a seq (same outer state). -/
private theorem seqHead_cong_at_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (rest : List Expr)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.seq (M :: rest)) env T = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.seq (N :: rest)) env T = some (v_final, T_final) := by
  obtain ⟨k, h_some⟩ := h_ex
  cases k with
  | zero => simp [eval] at h_some
  | succ k' =>
      cases rest with
      | nil =>
          simp only [eval] at h_some
          obtain ⟨k_N, h_N⟩ := (h ptable level env T hP v_final T_final).mp ⟨k', h_some⟩
          refine ⟨k_N + 1, ?_⟩
          simp only [eval]; exact h_N
      | cons e2 rest' =>
          simp only [eval] at h_some
          cases h_eM : eval k' ptable level M env T with
          | none => rw [h_eM] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_M, T_M⟩ := pair
              obtain ⟨k_N, h_N⟩ := (h ptable level env T hP v_M T_M).mp ⟨k', h_eM⟩
              rw [h_eM] at h_some
              simp only at h_some
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_right k' k_N) h_N]
              exact eval_fuel_mono (Nat.le_max_left k' k_N) h_some

theorem EvalEquivAt.seqHead_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (rest : List Expr) :
    EvalEquivAt P (.seq (M :: rest)) (.seq (N :: rest)) := by
  intro ptable level env T hP v_final T_final
  exact ⟨seqHead_cong_at_forward h rest ptable level env T hP v_final T_final,
         seqHead_cong_at_forward h.symm rest ptable level env T hP v_final T_final⟩

/-! ### "Hard" cases — inner state differs from outer

These congruence lemmas take an explicit `P`-preservation
hypothesis for the pre-hole sub-eval. The user supplies the
preservation proof per choice of `P`. -/

/-- `.letE x ev ·`: hole in the body. Inner eval is at the
    post-alloc state. -/
theorem EvalEquivAt.letEBody_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (x : String) (ev : Expr)
    (h_preserve : ∀ ptable level env T, P ptable level env T →
                  ∀ k v T', eval k ptable level ev env T = some (v, T') →
                  P ptable level (.cons x T'.heap.length env)
                                  {T' with heap := T'.heap ++ [v]}) :
    EvalEquivAt P (.letE x ev M) (.letE x ev N) := by
  intro ptable level env T hP v_final T_final
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
            have hP' := h_preserve ptable level env T hP k' v_ev T_ev h_ev
            obtain ⟨k_N, h_N⟩ := (h ptable level _ _ hP' v_final T_final).mp
              ⟨k', h_some⟩
            refine ⟨max k' k_N + 1, ?_⟩
            simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ev]
            exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
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
            have hP' := h_preserve ptable level env T hP k' v_ev T_ev h_ev
            obtain ⟨k_M, h_M⟩ := (h ptable level _ _ hP' v_final T_final).mpr
              ⟨k', h_some⟩
            refine ⟨max k' k_M + 1, ?_⟩
            simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_M) h_ev]
            exact eval_fuel_mono (Nat.le_max_right k' k_M) h_M

/-- Helper for `.ifteThen_cong_at`. -/
private theorem ifteThen_cong_at_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (ec ee : Expr)
    (h_preserve : ∀ ptable level env T, P ptable level env T →
                  ∀ k v_c T_c, eval k ptable level ec env T = some (v_c, T_c) →
                  P ptable level env T_c)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
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
          have hP_Tc := h_preserve ptable level env T hP k' v_c T_c h_ec
          cases v_c with
          | bool b =>
              cases b with
              | false =>
                  refine ⟨k' + 1, ?_⟩
                  simp only [eval, h_ec]; exact h_some
              | true =>
                  obtain ⟨k_N, h_N⟩ :=
                    (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
                  refine ⟨max k' k_N + 1, ?_⟩
                  simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
                  try simp
                  exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | num _ =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | nilV =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | sym _ =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | cons _ _ =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | closure _ _ _ =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | prim _ =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
          | builtinBaseApply =>
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
              try simp
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N

/-- `.ifte ec · ee`: hole in the then-branch. -/
theorem EvalEquivAt.ifteThen_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (ec ee : Expr)
    (h_preserve : ∀ ptable level env T, P ptable level env T →
                  ∀ k v_c T_c, eval k ptable level ec env T = some (v_c, T_c) →
                  P ptable level env T_c) :
    EvalEquivAt P (.ifte ec M ee) (.ifte ec N ee) := by
  intro ptable level env T hP v_final T_final
  exact ⟨ifteThen_cong_at_forward h ec ee h_preserve ptable level env T hP
            v_final T_final,
         ifteThen_cong_at_forward h.symm ec ee h_preserve ptable level env T hP
            v_final T_final⟩

/-- Helper for `.ifteElse_cong_at`. -/
private theorem ifteElse_cong_at_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (ec t : Expr)
    (h_preserve : ∀ ptable level env T, P ptable level env T →
                  ∀ k v_c T_c, eval k ptable level ec env T = some (v_c, T_c) →
                  P ptable level env T_c)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
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
          have hP_Tc := h_preserve ptable level env T hP k' v_c T_c h_ec
          cases v_c with
          | bool b =>
              cases b with
              | false =>
                  obtain ⟨k_N, h_N⟩ :=
                    (h ptable level env T_c hP_Tc v_final T_final).mp ⟨k', h_some⟩
                  refine ⟨max k' k_N + 1, ?_⟩
                  simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_ec]
                  exact eval_fuel_mono (Nat.le_max_right k' k_N) h_N
              | true =>
                  refine ⟨k' + 1, ?_⟩
                  simp only [eval, h_ec]; exact h_some
          | num _ =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some
          | nilV =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some
          | sym _ =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some
          | cons _ _ =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some
          | closure _ _ _ =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some
          | prim _ =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some
          | builtinBaseApply =>
              refine ⟨k' + 1, ?_⟩; simp only [eval, h_ec]; exact h_some

/-- `.ifte ec t ·`: hole in the else-branch. -/
theorem EvalEquivAt.ifteElse_cong {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (ec t : Expr)
    (h_preserve : ∀ ptable level env T, P ptable level env T →
                  ∀ k v_c T_c, eval k ptable level ec env T = some (v_c, T_c) →
                  P ptable level env T_c) :
    EvalEquivAt P (.ifte ec t M) (.ifte ec t N) := by
  intro ptable level env T hP v_final T_final
  exact ⟨ifteElse_cong_at_forward h ec t h_preserve ptable level env T hP
            v_final T_final,
         ifteElse_cong_at_forward h.symm ec t h_preserve ptable level env T hP
            v_final T_final⟩

/-! ## Everything else lives in `CtxPure.lean`

The list-position congruences (generic in a sibling class `S`), the
predicate-shifting `em` congruence, the side conditions on a context
(`Ctx.lamFree`, `Ctx.emDepth`, `Ctx.sidesOK`), and the single master
congruence `Ctx.plug_cong_master` — together with its tier
instantiations (`Ctx.plug_cong` for the unconditional strict track,
`Ctx.plug_cong_at_easy` for constant predicates over sibling-free
contexts) — are in `LeanBlack/CtxPure.lean`. -/

end LeanBlack
