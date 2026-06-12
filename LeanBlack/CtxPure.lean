/-
  lean-sage: The master context congruence.

  ONE context language (`Ctx`, `Ctx.lean`) and ONE congruence
  theorem (`Ctx.plug_cong_master`), parameterized by:

  - a **sibling class** `S : Expr → Prop` — what the context's
    pre-hole siblings are allowed to be (post-hole siblings are
    always unconstrained); and
  - a **predicate family** `P : Nat → StatePred`, indexed by
    remaining `em`-depth margin (each `em` on the hole path trades
    one unit of margin for one level).

  The historical tiers are instantiations:

  | tier (formerly)        | `S`                  | family       |
  |------------------------|----------------------|--------------|
  | strict (`SimpleCtx`)   | `fun _ => True`      | trivial      |
  | easy (`EasyCtx`)       | `fun _ => False`     | constant     |
  | wide (`WideCtx`)       | `fun _ => True`      | constant     |
  | pure (`PureCtx`)       | `(Pure · = true)`    | `BuiltinReadyP` |

  `S := False` admits only contexts with *no* pre-hole siblings, so
  every preservation hypothesis is vacuous — the easy tier costs
  nothing, as it should. `S := True` demands closure under arbitrary
  evaluation. `S := Pure` demands closure under pure evaluation
  (`PureExt.lean` supplies it for `BuiltinReady`-style predicates).

  Side conditions on the context: `C.lamFree` (the hole is not under
  a binder — the one position contextual β does not yet cover; see
  `SCOPE.md`), `C.sidesOK S`, and — only if the context actually
  `em`-nests — the family's descent step.
-/

import LeanBlack.Black
import LeanBlack.Eval
import LeanBlack.EvalFuelMono
import LeanBlack.Ctx
import LeanBlack.ProofBased
import LeanBlack.PureExt

namespace LeanBlack

/-! ## Predicate weakening -/

/-- `EvalEquivAt` is antitone in the predicate: a stronger
    precondition gives the same equivalence. -/
theorem EvalEquivAt.mono {P Q : StatePred} {M N : Expr}
    (h_imp : ∀ ptable level env T, P ptable level env T → Q ptable level env T)
    (h : EvalEquivAt Q M N) : EvalEquivAt P M N :=
  fun ptable level env T hP => h ptable level env T (h_imp ptable level env T hP)

/-! ## Closure under evaluation of a sibling class -/

/-- `P` is preserved by successful evaluation of expressions in the
    sibling class `S`. With `S := fun _ => True` this is closure
    under arbitrary evaluation; with `S := (Pure · = true)` it is
    closure under pure evaluation (which `BuiltinReady`-style
    predicates satisfy, via `PureExt.lean`); with
    `S := fun _ => False` it is vacuous. -/
def ClosedUnderEvalOf (S : Expr → Prop) (P : StatePred) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (e : Expr) (env : Env) (T : TowerState),
    S e → P ptable level env T →
    ∀ k v T', eval k ptable level e env T = some (v, T') →
    P ptable level env T'

/-- Closure under pure evaluation — the instantiation
    `BuiltinReadyP`-style predicates satisfy. -/
abbrev ClosedUnderPureEval (P : StatePred) : Prop :=
  ClosedUnderEvalOf (fun e => Pure e = true) P

/-! ## `.em` congruence with predicate shift

Copy of `EvalEquivAt.em_cong` (`Ctx.lean`) except that the hole's
predicate `Q` may differ from the outer predicate `P`; the
preservation hypothesis bridges the two across the level shift. This
is what lets a depth-indexed predicate family thread through
`em`-nesting. -/

theorem EvalEquivAt.em_cong_shift {P Q : StatePred} {M N : Expr}
    (h : EvalEquivAt Q M N)
    (h_preserve : ∀ ptable level env T, P ptable level env T →
                  ∀ T_mat, T.materialize (level + 1) = some T_mat →
                  ∀ upEnv, T_mat.envAt? (level + 1) = some upEnv →
                  Q ptable (level + 1) upEnv T_mat) :
    EvalEquivAt P (.em M) (.em N) := by
  intro ptable level env T hP v_final T_final
  constructor
  · rintro ⟨k, h_some⟩
    cases k with
    | zero => simp [eval] at h_some
    | succ k' =>
        simp only [eval] at h_some
        cases h_mat : T.materialize (level + 1) with
        | none => rw [h_mat] at h_some; simp at h_some
        | some T_mat =>
            simp [h_mat] at h_some
            cases h_env : T_mat.envAt? (level + 1) with
            | none => simp [h_env] at h_some
            | some upEnv =>
                simp [h_env] at h_some
                have hP' := h_preserve ptable level env T hP T_mat h_mat upEnv h_env
                obtain ⟨k_N, h_N⟩ := (h ptable (level+1) upEnv T_mat hP'
                  v_final T_final).mp ⟨k', h_some⟩
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
            simp [h_mat] at h_some
            cases h_env : T_mat.envAt? (level + 1) with
            | none => simp [h_env] at h_some
            | some upEnv =>
                simp [h_env] at h_some
                have hP' := h_preserve ptable level env T hP T_mat h_mat upEnv h_env
                obtain ⟨k_M, h_M⟩ := (h ptable (level+1) upEnv T_mat hP'
                  v_final T_final).mpr ⟨k', h_some⟩
                refine ⟨k_M + 1, ?_⟩
                simp only [eval, h_mat]
                simp [h_env, h_M]

/-! ## List-position congruences, generic in the sibling class -/

private theorem evalList_EvalEquivAt_of_forward {S : Expr → Prop}
    {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P) :
    ∀ (pre post : List Expr), (∀ e ∈ pre, S e) →
      ∀ (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState),
      P ptable level env T →
      ∀ (vs : List Val) (T' : TowerState),
      (∃ k, evalList k ptable level (pre ++ M :: post) env T = some (vs, T')) →
      (∃ k, evalList k ptable level (pre ++ N :: post) env T = some (vs, T')) := by
  intro pre
  induction pre with
  | nil =>
      intro post _ ptable level env T hP vs T' ⟨k, h_some⟩
      cases k with
      | zero => simp [evalList] at h_some
      | succ k' =>
          simp only [List.nil_append, evalList] at h_some
          cases h_eM : eval k' ptable level M env T with
          | none => rw [h_eM] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_M, T_M⟩ := pair
              obtain ⟨k_N, h_N⟩ :=
                (h ptable level env T hP v_M T_M).mp ⟨k', h_eM⟩
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
      intro post h_S ptable level env T hP vs T' ⟨k, h_some⟩
      have h_S1 : S h_pre := h_S h_pre (by simp)
      have h_Srest : ∀ e ∈ pre_rest, S e := fun e he => h_S e (by simp [he])
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
                  have hP_Th := h_closed ptable level h_pre env T h_S1 hP k' v_h T_h h_eH
                  obtain ⟨k_N_inner, h_eList_N⟩ :=
                    ih post h_Srest ptable level env T_h hP_Th vs_rest T_rest
                      ⟨k', h_eList⟩
                  refine ⟨max k' k_N_inner + 1, ?_⟩
                  simp only [List.cons_append, evalList,
                             eval_fuel_mono (Nat.le_max_left k' k_N_inner) h_eH,
                             evalList_fuel_mono (Nat.le_max_right k' k_N_inner) h_eList_N]
                  exact h_some

theorem evalList_EvalEquivAt_of {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P)
    (pre post : List Expr) (h_pre : ∀ e ∈ pre, S e)
    (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState) (hP : P ptable level env T)
    (vs : List Val) (T' : TowerState) :
    (∃ k, evalList k ptable level (pre ++ M :: post) env T = some (vs, T')) ↔
    (∃ k, evalList k ptable level (pre ++ N :: post) env T = some (vs, T')) :=
  ⟨evalList_EvalEquivAt_of_forward h h_closed pre post h_pre ptable level env T hP vs T',
   evalList_EvalEquivAt_of_forward h.symm h_closed pre post h_pre ptable level env T hP vs T'⟩

/-- `.app (head :: pre ++ · :: post)` with `S`-classed head and
    pre-hole args. -/
private theorem appArg_cong_of_forward {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P)
    (head : Expr) (h_head : S head)
    (pre' post : List Expr) (h_pre : ∀ e ∈ pre', S e)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.app (head :: (pre' ++ M :: post))) env T
                  = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.app (head :: (pre' ++ N :: post))) env T
          = some (v_final, T_final) := by
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
          have hP_Th := h_closed ptable level head env T h_head hP k' fv T_h h_eH
          cases h_eL : evalList k' ptable level (pre' ++ M :: post) env T_h with
          | none => rw [h_eL] at h_some; simp at h_some
          | some pair' =>
              obtain ⟨avs, T_a⟩ := pair'
              rw [h_eL] at h_some
              simp only at h_some
              obtain ⟨k_N, h_eL_N⟩ :=
                (evalList_EvalEquivAt_of h h_closed pre' post h_pre ptable level env T_h
                  hP_Th avs T_a).mp ⟨k', h_eL⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_eH,
                         evalList_fuel_mono (Nat.le_max_right k' k_N) h_eL_N]
              exact applyVia_fuel_mono (Nat.le_max_left k' k_N) h_some

theorem EvalEquivAt.appArg_cong_of {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P)
    (head : Expr) (h_head : S head)
    (pre' post : List Expr) (h_pre : ∀ e ∈ pre', S e) :
    EvalEquivAt P (.app (head :: (pre' ++ M :: post)))
                  (.app (head :: (pre' ++ N :: post))) := by
  intro ptable level env T hP v_final T_final
  exact ⟨appArg_cong_of_forward h h_closed head h_head pre' post h_pre
            ptable level env T hP v_final T_final,
         appArg_cong_of_forward h.symm h_closed head h_head pre' post h_pre
            ptable level env T hP v_final T_final⟩

/-- `.primApp f (pre ++ · :: post)` with `S`-classed `f` and
    pre-hole args. -/
private theorem primAppArg_cong_of_forward {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P)
    (f : Expr) (h_f : S f)
    (pre' post : List Expr) (h_pre : ∀ e ∈ pre', S e)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (hP : P ptable level env T)
    (v_final : Val) (T_final : TowerState)
    (h_ex : ∃ k, eval k ptable level (.primApp f (pre' ++ M :: post)) env T
                  = some (v_final, T_final)) :
    ∃ k, eval k ptable level (.primApp f (pre' ++ N :: post)) env T
          = some (v_final, T_final) := by
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
          have hP_Tf := h_closed ptable level f env T h_f hP k' fv T_f h_eF
          cases h_eL : evalList k' ptable level (pre' ++ M :: post) env T_f with
          | none => rw [h_eL] at h_some; simp at h_some
          | some pair' =>
              obtain ⟨avs, T_a⟩ := pair'
              rw [h_eL] at h_some
              simp only at h_some
              obtain ⟨k_N, h_eL_N⟩ :=
                (evalList_EvalEquivAt_of h h_closed pre' post h_pre ptable level env T_f
                  hP_Tf avs T_a).mp ⟨k', h_eL⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_eF,
                         evalList_fuel_mono (Nat.le_max_right k' k_N) h_eL_N]
              exact applyDirect_fuel_mono (Nat.le_max_left k' k_N) h_some

theorem EvalEquivAt.primAppArg_cong_of {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P)
    (f : Expr) (h_f : S f)
    (pre' post : List Expr) (h_pre : ∀ e ∈ pre', S e) :
    EvalEquivAt P (.primApp f (pre' ++ M :: post))
                  (.primApp f (pre' ++ N :: post)) := by
  intro ptable level env T hP v_final T_final
  exact ⟨primAppArg_cong_of_forward h h_closed f h_f pre' post h_pre
            ptable level env T hP v_final T_final,
         primAppArg_cong_of_forward h.symm h_closed f h_f pre' post h_pre
            ptable level env T hP v_final T_final⟩

/-- `.seq (head :: pre ++ · :: post)` with `S`-classed head and
    pre-hole elements. -/
private theorem seqTail_cong_of_forward {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P) :
    ∀ (pre post : List Expr) (head : Expr),
      S head → (∀ e ∈ pre, S e) →
      ∀ (ptable : PolicyTable) (level : Nat)
      (env : Env) (T : TowerState),
      P ptable level env T →
      ∀ (v_final : Val) (T_final : TowerState),
      (∃ k, eval k ptable level (.seq (head :: pre ++ M :: post)) env T
              = some (v_final, T_final)) →
      (∃ k, eval k ptable level (.seq (head :: pre ++ N :: post)) env T
              = some (v_final, T_final)) := by
  intro pre
  induction pre with
  | nil =>
      intro post head h_head _ ptable level env T hP v_final T_final ⟨k, h_some⟩
      cases k with
      | zero => simp [eval] at h_some
      | succ k' =>
          simp only [List.cons_append, List.nil_append, eval] at h_some
          cases h_eH : eval k' ptable level head env T with
          | none => rw [h_eH] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_h, T_h⟩ := pair
              rw [h_eH] at h_some
              simp only at h_some
              have hP_Th := h_closed ptable level head env T h_head hP k' v_h T_h h_eH
              obtain ⟨k_N, h_seq_N⟩ :=
                (EvalEquivAt.seqHead_cong h post ptable level env T_h hP_Th
                  v_final T_final).mp ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [List.cons_append, List.nil_append, eval,
                         eval_fuel_mono (Nat.le_max_left k' k_N) h_eH]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_seq_N
  | cons h_pre pre_rest ih =>
      intro post head h_head h_S ptable level env T hP v_final T_final ⟨k, h_some⟩
      have h_S1 : S h_pre := h_S h_pre (by simp)
      have h_Srest : ∀ e ∈ pre_rest, S e := fun e he => h_S e (by simp [he])
      cases k with
      | zero => simp [eval] at h_some
      | succ k' =>
          simp only [List.cons_append, eval] at h_some
          cases h_eH : eval k' ptable level head env T with
          | none => rw [h_eH] at h_some; simp at h_some
          | some pair =>
              obtain ⟨v_h, T_h⟩ := pair
              rw [h_eH] at h_some
              simp only at h_some
              have hP_Th := h_closed ptable level head env T h_head hP k' v_h T_h h_eH
              obtain ⟨k_N, h_seq_N⟩ :=
                ih post h_pre h_S1 h_Srest ptable level env T_h hP_Th v_final T_final
                  ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [List.cons_append, eval,
                         eval_fuel_mono (Nat.le_max_left k' k_N) h_eH]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_seq_N

theorem EvalEquivAt.seqTail_cong_of {S : Expr → Prop} {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderEvalOf S P)
    (head : Expr) (h_head : S head)
    (pre post : List Expr) (h_pre : ∀ e ∈ pre, S e) :
    EvalEquivAt P (.seq (head :: pre ++ M :: post))
                  (.seq (head :: pre ++ N :: post)) := by
  intro ptable level env T hP v_final T_final
  exact ⟨seqTail_cong_of_forward h h_closed pre post head h_head h_pre
            ptable level env T hP v_final T_final,
         seqTail_cong_of_forward h.symm h_closed pre post head h_head h_pre
            ptable level env T hP v_final T_final⟩

/-! ## Side conditions on a context -/

/-- The hole is not under a binder. (The `.lam` position is the one
    place contextual β does not yet cover; see `SCOPE.md`.) -/
def Ctx.lamFree : Ctx → Bool
  | .hole             => true
  | .ifteCond c _ _   => c.lamFree
  | .ifteThen _ c _   => c.lamFree
  | .ifteElse _ _ c   => c.lamFree
  | .lam _ _          => false
  | .app _ c _        => c.lamFree
  | .set _ c          => c.lamFree
  | .em c             => c.lamFree
  | .primAppFun c _   => c.lamFree
  | .primAppArg _ _ c _ => c.lamFree
  | .letEVal _ c _    => c.lamFree
  | .letEBody _ _ c   => c.lamFree
  | .seq _ c _        => c.lamFree

/-- Number of `.em` wrappers along the path to the hole — the
    reflective depth the hole sits at, relative to the plug level. -/
def Ctx.emDepth : Ctx → Nat
  | .hole             => 0
  | .ifteCond c _ _   => c.emDepth
  | .ifteThen _ c _   => c.emDepth
  | .ifteElse _ _ c   => c.emDepth
  | .lam _ c          => c.emDepth
  | .app _ c _        => c.emDepth
  | .set _ c          => c.emDepth
  | .em c             => c.emDepth + 1
  | .primAppFun c _   => c.emDepth
  | .primAppArg _ _ c _ => c.emDepth
  | .letEVal _ c _    => c.emDepth
  | .letEBody _ _ c   => c.emDepth
  | .seq _ c _        => c.emDepth

/-- Every sub-expression evaluated *before* the hole along the path
    is in the sibling class `S`. (Post-hole siblings evaluate after
    the hole and are unconstrained.) -/
def Ctx.sidesOK (S : Expr → Prop) : Ctx → Prop
  | .hole             => True
  | .ifteCond c _ _   => c.sidesOK S
  | .ifteThen ec c _  => S ec ∧ c.sidesOK S
  | .ifteElse ec _ c  => S ec ∧ c.sidesOK S
  | .lam _ c          => c.sidesOK S
  | .app pre c _      => (∀ e ∈ pre, S e) ∧ c.sidesOK S
  | .set _ c          => c.sidesOK S
  | .em c             => c.sidesOK S
  | .primAppFun c _   => c.sidesOK S
  | .primAppArg f pre c _ => S f ∧ (∀ e ∈ pre, S e) ∧ c.sidesOK S
  | .letEVal _ c _    => c.sidesOK S
  | .letEBody _ ev c  => S ev ∧ c.sidesOK S
  | .seq pre c _      => (∀ e ∈ pre, S e) ∧ c.sidesOK S

/-- Every context's sides are OK for the trivial class. -/
theorem Ctx.sidesOK_true : ∀ C : Ctx, C.sidesOK (fun _ => True)
  | .hole             => trivial
  | .ifteCond c _ _   => c.sidesOK_true
  | .ifteThen _ c _   => ⟨trivial, c.sidesOK_true⟩
  | .ifteElse _ _ c   => ⟨trivial, c.sidesOK_true⟩
  | .lam _ c          => c.sidesOK_true
  | .app _ c _        => ⟨fun _ _ => trivial, c.sidesOK_true⟩
  | .set _ c          => c.sidesOK_true
  | .em c             => c.sidesOK_true
  | .primAppFun c _   => c.sidesOK_true
  | .primAppArg _ _ c _ => ⟨trivial, fun _ _ => trivial, c.sidesOK_true⟩
  | .letEVal _ c _    => c.sidesOK_true
  | .letEBody _ _ c   => ⟨trivial, c.sidesOK_true⟩
  | .seq _ c _        => ⟨fun _ _ => trivial, c.sidesOK_true⟩

/-! ## The master congruence -/

/-- **The master context congruence.** Equivalence at `P 0` at the
    hole lifts to equivalence at `P (emDepth C)` outside, for any
    lam-free context whose pre-hole siblings are in the class `S`.

    Hypotheses, by feature used:
    - `h_closed`: each `P d` is closed under evaluation of
      `S`-expressions (vacuous for `S := fun _ => False`);
    - `h_alloc`: each `P d` survives the `.letE` binding step for an
      `S`-classed binder (vacuous likewise);
    - `h_em` (demanded only if the context `em`-nests): descending
      into `em` trades one unit of margin for one level. -/
theorem Ctx.plug_cong_master
    (S : Expr → Prop) (P : Nat → StatePred)
    (h_closed : ∀ d, ClosedUnderEvalOf S (P d))
    (h_alloc : ∀ d (ptable : PolicyTable) (level : Nat) (x : String) (ev : Expr)
        (env : Env) (T : TowerState), S ev → P d ptable level env T →
        ∀ k v T', eval k ptable level ev env T = some (v, T') →
        P d ptable level (Env.cons x T'.heap.length env)
          { T' with heap := T'.heap ++ [v] }) :
    ∀ (C : Ctx),
      (C.emDepth ≠ 0 → ∀ d ptable level env T, P (d+1) ptable level env T →
        ∀ T_mat, T.materialize (level + 1) = some T_mat →
        ∀ upEnv, T_mat.envAt? (level + 1) = some upEnv →
        P d ptable (level + 1) upEnv T_mat) →
      C.lamFree = true → C.sidesOK S → ∀ {M N : Expr},
      EvalEquivAt (P 0) M N →
      EvalEquivAt (P C.emDepth) (C.plug M) (C.plug N) := by
  intro C
  induction C with
  | hole =>
      intro _ _ _ M N h
      simpa only [Ctx.plug, Ctx.emDepth] using h
  | ifteCond c t' e' ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.ifteCond_cong (ih h_em h_lam h_sides h) t' e'
  | ifteThen ec c ee ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      obtain ⟨h_Sec, h_sides'⟩ := h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.ifteThen_cong (ih h_em h_lam h_sides' h) ec ee
        (fun ptable level env T hP k v_c T_c h_ec =>
          h_closed c.emDepth ptable level ec env T h_Sec hP k v_c T_c h_ec)
  | ifteElse ec t c ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      obtain ⟨h_Sec, h_sides'⟩ := h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.ifteElse_cong (ih h_em h_lam h_sides' h) ec t
        (fun ptable level env T hP k v_c T_c h_ec =>
          h_closed c.emDepth ptable level ec env T h_Sec hP k v_c T_c h_ec)
  | lam ps c _ih =>
      intro _ h_lam
      exact (Bool.false_ne_true h_lam).elim
  | app pre c post ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      obtain ⟨h_Spre, h_sides'⟩ := h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      cases pre with
      | nil =>
          simpa only [List.nil_append] using
            EvalEquivAt.appHead_cong (ih h_em h_lam h_sides' h) post
      | cons hd pre' =>
          have h_Shd : S hd := h_Spre hd (by simp)
          have h_Spre' : ∀ e ∈ pre', S e := fun e he => h_Spre e (by simp [he])
          simpa only [List.cons_append] using
            EvalEquivAt.appArg_cong_of (ih h_em h_lam h_sides' h)
              (h_closed c.emDepth) hd h_Shd pre' post h_Spre'
  | set x c ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.set_cong (ih h_em h_lam h_sides h) x
  | em c ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      simp only [Ctx.emDepth] at h_em
      have h_em_fact := h_em (Nat.succ_ne_zero _)
      simp only [Ctx.plug, Ctx.emDepth]
      exact EvalEquivAt.em_cong_shift
        (ih (fun _ => h_em_fact) h_lam h_sides h)
        (fun ptable level env T hP T_mat h_mat upEnv h_env =>
          h_em_fact c.emDepth ptable level env T hP T_mat h_mat upEnv h_env)
  | primAppFun c args ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.primAppFun_cong (ih h_em h_lam h_sides h) args
  | primAppArg f pre c post ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      obtain ⟨h_Sf, h_Spre, h_sides'⟩ := h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.primAppArg_cong_of (ih h_em h_lam h_sides' h)
        (h_closed c.emDepth) f h_Sf pre post h_Spre
  | letEVal x c b ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.letEVal_cong (ih h_em h_lam h_sides h) x b
  | letEBody x ev c ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      obtain ⟨h_Sev, h_sides'⟩ := h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      exact EvalEquivAt.letEBody_cong (ih h_em h_lam h_sides' h) x ev
        (fun ptable level env T hP k v T' h_ev =>
          h_alloc c.emDepth ptable level x ev env T h_Sev hP k v T' h_ev)
  | seq pre c post ih =>
      intro h_em h_lam h_sides M N h
      simp only [Ctx.lamFree] at h_lam
      simp only [Ctx.sidesOK] at h_sides
      obtain ⟨h_Spre, h_sides'⟩ := h_sides
      simp only [Ctx.plug, Ctx.emDepth] at h_em ⊢
      cases pre with
      | nil =>
          simpa only [List.nil_append] using
            EvalEquivAt.seqHead_cong (ih h_em h_lam h_sides' h) post
      | cons hd pre' =>
          have h_Shd : S hd := h_Spre hd (by simp)
          have h_Spre' : ∀ e ∈ pre', S e := fun e he => h_Spre e (by simp [he])
          simpa only [List.cons_append] using
            EvalEquivAt.seqTail_cong_of (ih h_em h_lam h_sides' h)
              (h_closed c.emDepth) hd h_Shd pre' post h_Spre'

/-! ## Instantiations: the historical tiers as corollaries -/

/-- **Strict tier** (formerly `SimpleCtx.plug_cong`): unconditional
    observational equivalence is a congruence for every lam-free
    context — no sibling or predicate hypotheses at all. -/
theorem Ctx.plug_cong {M N : Expr} (h : EvalEquiv M N)
    (C : Ctx) (h_lam : C.lamFree = true) :
    EvalEquiv (C.plug M) (C.plug N) := by
  have h_at : EvalEquivAt (fun _ _ _ _ => True) M N :=
    fun ptable level env T _ => h ptable level env T
  have h_master :=
    Ctx.plug_cong_master (fun _ => True) (fun _ _ _ _ _ => True)
      (by intro _ _ _ _ _ _ _ _ _ _ _ _; trivial)
      (by intros; trivial)
      C (by intros; trivial)
      h_lam (C.sidesOK_true) h_at
  exact fun ptable level env T => h_master ptable level env T trivial

/-- **Easy tier** (formerly `EasyCtx.plug_cong_at`): a *constant*
    predicate lifts through any lam-free, `em`-free context with no
    pre-hole siblings — no preservation hypotheses at all
    (`S := fun _ => False` makes them vacuous). -/
theorem Ctx.plug_cong_at_easy {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N)
    (C : Ctx) (h_lam : C.lamFree = true)
    (h_sides : C.sidesOK (fun _ => False)) (h_noem : C.emDepth = 0) :
    EvalEquivAt P (C.plug M) (C.plug N) := by
  have h_master :=
    Ctx.plug_cong_master (fun _ => False) (fun _ => P)
      (by intro _ _ _ _ _ _ h_false; exact h_false.elim)
      (by intro _ _ _ _ _ _ _ h_false; exact h_false.elim)
      C (fun h_ne => absurd h_noem h_ne)
      h_lam h_sides h
  rw [h_noem] at h_master
  exact h_master

end LeanBlack
