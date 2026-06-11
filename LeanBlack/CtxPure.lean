/-
  lean-sage: Pure-sided contexts — congruence machinery for the
  full `Expr` tree except `.lam`.

  `Ctx.lean` covers contexts in three tiers: `EasyCtx` (hole sees
  the outer state), `WideCtx` (adds positions whose preservation
  hypothesis is `PIsClosedUnderEval` — closure under *arbitrary*
  eval), and per-constructor lemmas for `.letEBody` and `.em` with
  bespoke preservation hypotheses.

  This file closes the gap between those tiers for the predicates
  that actually arise in contextual β (`BuiltinReady` and friends),
  which are *not* closed under arbitrary eval (a `.set` on the
  `base-apply` cell breaks them) but *are* closed under evaluation
  of `Pure` expressions (`PureExt.lean`). Three pieces:

  1. `ClosedUnderPureEval P` — the right closure notion — and
     pure-sided variants of the list-position congruences.
  2. `EvalEquivAt.em_cong_shift` — the `.em` congruence with a
     predicate *shift*: the hole's predicate may differ from the
     outer one. This is what lets a depth-indexed predicate family
     thread through `em`-nesting (each `em` consumes one level of
     depth-margin).
  3. `PureCtx` — a context language covering every `Expr` position
     except under `.lam` — and the master congruence
     `PureCtx.plug_cong_family`, generic over any predicate family
     `P : Nat → StatePred` indexed by remaining `em`-depth.

  `.lam` remains excluded: closures embed their bodies
  syntactically, so outcome-equality congruence fails there; the
  `.lam` case needs a `ValVis`-style up-to-bisim equivalence (L4).
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

/-! ## Closure under pure evaluation -/

/-- `P` is preserved by successful evaluation of `Pure` expressions.
    The closure notion that `BuiltinReady`-style predicates satisfy
    (cf. `PIsClosedUnderEval`, which demands closure under arbitrary
    eval and fails for them: an admitted `.set` can rewrite the
    `base-apply` cell). -/
def ClosedUnderPureEval (P : StatePred) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (e : Expr) (env : Env) (T : TowerState),
    Pure e = true → P ptable level env T →
    ∀ k v T', eval k ptable level e env T = some (v, T') →
    P ptable level env T'

/-! ## `.em` congruence with predicate shift

Copy of `EvalEquivAt.em_cong` (`Ctx.lean`) except that the hole's
predicate `Q` may differ from the outer predicate `P`; the
preservation hypothesis bridges the two across the level shift. -/

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

/-! ## Pure-sided list-position congruences

Copies of `evalList_EvalEquivAt` / `appArg_cong` / `primAppArg_cong`
/ `seqTail_cong` (`Ctx.lean`) with `PIsClosedUnderEval` replaced by
`ClosedUnderPureEval` plus purity of the pre-hole siblings. -/

private theorem evalList_EvalEquivAt_pure_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P) :
    ∀ (pre post : List Expr), PureList pre = true →
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
      intro post h_pure ptable level env T hP vs T' ⟨k, h_some⟩
      simp only [PureList, Bool.and_eq_true] at h_pure
      obtain ⟨h_p1, h_prest⟩ := h_pure
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
                  have hP_Th := h_closed ptable level h_pre env T h_p1 hP k' v_h T_h h_eH
                  obtain ⟨k_N_inner, h_eList_N⟩ :=
                    ih post h_prest ptable level env T_h hP_Th vs_rest T_rest
                      ⟨k', h_eList⟩
                  refine ⟨max k' k_N_inner + 1, ?_⟩
                  simp only [List.cons_append, evalList,
                             eval_fuel_mono (Nat.le_max_left k' k_N_inner) h_eH,
                             evalList_fuel_mono (Nat.le_max_right k' k_N_inner) h_eList_N]
                  exact h_some

theorem evalList_EvalEquivAt_pure {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P)
    (pre post : List Expr) (h_pre : PureList pre = true)
    (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState) (hP : P ptable level env T)
    (vs : List Val) (T' : TowerState) :
    (∃ k, evalList k ptable level (pre ++ M :: post) env T = some (vs, T')) ↔
    (∃ k, evalList k ptable level (pre ++ N :: post) env T = some (vs, T')) :=
  ⟨evalList_EvalEquivAt_pure_forward h h_closed pre post h_pre ptable level env T hP vs T',
   evalList_EvalEquivAt_pure_forward h.symm h_closed pre post h_pre ptable level env T hP vs T'⟩

/-- `.app (head :: pre ++ · :: post)` with pure head and pure
    pre-hole args. -/
private theorem appArg_cong_pure_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P)
    (head : Expr) (h_head : Pure head = true)
    (pre' post : List Expr) (h_pre : PureList pre' = true)
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
                (evalList_EvalEquivAt_pure h h_closed pre' post h_pre ptable level env T_h
                  hP_Th avs T_a).mp ⟨k', h_eL⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_eH,
                         evalList_fuel_mono (Nat.le_max_right k' k_N) h_eL_N]
              exact applyVia_fuel_mono (Nat.le_max_left k' k_N) h_some

theorem EvalEquivAt.appArg_cong_pure {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P)
    (head : Expr) (h_head : Pure head = true)
    (pre' post : List Expr) (h_pre : PureList pre' = true) :
    EvalEquivAt P (.app (head :: (pre' ++ M :: post)))
                  (.app (head :: (pre' ++ N :: post))) := by
  intro ptable level env T hP v_final T_final
  exact ⟨appArg_cong_pure_forward h h_closed head h_head pre' post h_pre
            ptable level env T hP v_final T_final,
         appArg_cong_pure_forward h.symm h_closed head h_head pre' post h_pre
            ptable level env T hP v_final T_final⟩

/-- `.primApp f (pre ++ · :: post)` with pure `f` and pure
    pre-hole args. -/
private theorem primAppArg_cong_pure_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P)
    (f : Expr) (h_f : Pure f = true)
    (pre' post : List Expr) (h_pre : PureList pre' = true)
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
                (evalList_EvalEquivAt_pure h h_closed pre' post h_pre ptable level env T_f
                  hP_Tf avs T_a).mp ⟨k', h_eL⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [eval, eval_fuel_mono (Nat.le_max_left k' k_N) h_eF,
                         evalList_fuel_mono (Nat.le_max_right k' k_N) h_eL_N]
              exact applyDirect_fuel_mono (Nat.le_max_left k' k_N) h_some

theorem EvalEquivAt.primAppArg_cong_pure {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P)
    (f : Expr) (h_f : Pure f = true)
    (pre' post : List Expr) (h_pre : PureList pre' = true) :
    EvalEquivAt P (.primApp f (pre' ++ M :: post))
                  (.primApp f (pre' ++ N :: post)) := by
  intro ptable level env T hP v_final T_final
  exact ⟨primAppArg_cong_pure_forward h h_closed f h_f pre' post h_pre
            ptable level env T hP v_final T_final,
         primAppArg_cong_pure_forward h.symm h_closed f h_f pre' post h_pre
            ptable level env T hP v_final T_final⟩

/-- `.seq (head :: pre ++ · :: post)` with pure head and pure
    pre-hole elements. -/
private theorem seqTail_cong_pure_forward {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P) :
    ∀ (pre post : List Expr) (head : Expr),
      Pure head = true → PureList pre = true →
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
      intro post head h_head h_pure ptable level env T hP v_final T_final ⟨k, h_some⟩
      simp only [PureList, Bool.and_eq_true] at h_pure
      obtain ⟨h_p1, h_prest⟩ := h_pure
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
                ih post h_pre h_p1 h_prest ptable level env T_h hP_Th v_final T_final
                  ⟨k', h_some⟩
              refine ⟨max k' k_N + 1, ?_⟩
              simp only [List.cons_append, eval,
                         eval_fuel_mono (Nat.le_max_left k' k_N) h_eH]
              exact eval_fuel_mono (Nat.le_max_right k' k_N) h_seq_N

theorem EvalEquivAt.seqTail_cong_pure {P : StatePred} {M N : Expr}
    (h : EvalEquivAt P M N) (h_closed : ClosedUnderPureEval P)
    (head : Expr) (h_head : Pure head = true)
    (pre post : List Expr) (h_pre : PureList pre = true) :
    EvalEquivAt P (.seq (head :: pre ++ M :: post))
                  (.seq (head :: pre ++ N :: post)) := by
  intro ptable level env T hP v_final T_final
  exact ⟨seqTail_cong_pure_forward h h_closed pre post head h_head h_pre
            ptable level env T hP v_final T_final,
         seqTail_cong_pure_forward h.symm h_closed pre post head h_head h_pre
            ptable level env T hP v_final T_final⟩

/-! ## `PureCtx` — every `Expr` position except under `.lam`

The context language for the master congruence: all thirteen
hole-bearing positions of the `Expr` tree except `.lam`'s body.
List positions are general (`pre ++ · :: post`). -/

inductive PureCtx where
  | hole       : PureCtx
  | ifteCond   : PureCtx → Expr → Expr → PureCtx
  | ifteThen   : Expr → PureCtx → Expr → PureCtx
  | ifteElse   : Expr → Expr → PureCtx → PureCtx
  | set        : String → PureCtx → PureCtx
  | em         : PureCtx → PureCtx
  /-- `.app (pre ++ · :: post)`; the head of the application is
      `pre.head` when `pre ≠ []`, else the hole itself. -/
  | app        : List Expr → PureCtx → List Expr → PureCtx
  | primAppFun : PureCtx → List Expr → PureCtx
  | primAppArg : Expr → List Expr → PureCtx → List Expr → PureCtx
  | letEVal    : String → PureCtx → Expr → PureCtx
  | letEBody   : String → Expr → PureCtx → PureCtx
  | seq        : List Expr → PureCtx → List Expr → PureCtx

def PureCtx.plug : PureCtx → Expr → Expr
  | .hole,             e => e
  | .ifteCond c t' e', e => .ifte (c.plug e) t' e'
  | .ifteThen ec c ee, e => .ifte ec (c.plug e) ee
  | .ifteElse ec t c,  e => .ifte ec t (c.plug e)
  | .set x c,          e => .set x (c.plug e)
  | .em c,             e => .em (c.plug e)
  | .app pre c post,   e => .app (pre ++ c.plug e :: post)
  | .primAppFun c args, e => .primApp (c.plug e) args
  | .primAppArg f pre c post, e => .primApp f (pre ++ c.plug e :: post)
  | .letEVal x c b,    e => .letE x (c.plug e) b
  | .letEBody x ev c,  e => .letE x ev (c.plug e)
  | .seq pre c post,   e => .seq (pre ++ c.plug e :: post)

/-- Number of `.em` wrappers along the path to the hole — the
    reflective depth the hole sits at, relative to the plug level. -/
def PureCtx.emDepth : PureCtx → Nat
  | .hole             => 0
  | .ifteCond c _ _   => c.emDepth
  | .ifteThen _ c _   => c.emDepth
  | .ifteElse _ _ c   => c.emDepth
  | .set _ c          => c.emDepth
  | .em c             => c.emDepth + 1
  | .app _ c _        => c.emDepth
  | .primAppFun c _   => c.emDepth
  | .primAppArg _ _ c _ => c.emDepth
  | .letEVal _ c _    => c.emDepth
  | .letEBody _ _ c   => c.emDepth
  | .seq _ c _        => c.emDepth

/-- All sub-expressions evaluated *before* the hole along the
    path are `Pure`. (Post-hole siblings evaluate after the hole
    and are unconstrained.) -/
def PureCtx.sidesPure : PureCtx → Bool
  | .hole             => true
  | .ifteCond c _ _   => c.sidesPure
  | .ifteThen ec c _  => Pure ec && c.sidesPure
  | .ifteElse ec _ c  => Pure ec && c.sidesPure
  | .set _ c          => c.sidesPure
  | .em c             => c.sidesPure
  | .app pre c _      => PureList pre && c.sidesPure
  | .primAppFun c _   => c.sidesPure
  | .primAppArg f pre c _ => Pure f && PureList pre && c.sidesPure
  | .letEVal _ c _    => c.sidesPure
  | .letEBody _ ev c  => Pure ev && c.sidesPure
  | .seq pre c _      => PureList pre && c.sidesPure

/-! ## The master congruence

Generic over a predicate family `P : Nat → StatePred` indexed by
*remaining `em`-depth margin*. The three family hypotheses:

- `h_closed`: each `P d` is closed under pure evaluation
  (sibling sub-evals don't disturb it);
- `h_em`: descending into `em` trades one unit of margin for one
  level: `P (d+1)` at `level` implies `P d` at `level+1` after
  materialization;
- `h_alloc`: each `P d` survives the `.letE` binding step
  (evaluate a pure binder, allocate the result, extend the env).

The conclusion: equivalence at `P 0` at the hole lifts to
equivalence at `P (emDepth C)` outside. -/

theorem PureCtx.plug_cong_family
    (P : Nat → StatePred)
    (h_closed : ∀ d, ClosedUnderPureEval (P d))
    (h_em : ∀ d ptable level env T, P (d+1) ptable level env T →
        ∀ T_mat, T.materialize (level + 1) = some T_mat →
        ∀ upEnv, T_mat.envAt? (level + 1) = some upEnv →
        P d ptable (level + 1) upEnv T_mat)
    (h_alloc : ∀ d (ptable : PolicyTable) (level : Nat) (x : String) (ev : Expr)
        (env : Env) (T : TowerState), Pure ev = true → P d ptable level env T →
        ∀ k v T', eval k ptable level ev env T = some (v, T') →
        P d ptable level (Env.cons x T'.heap.length env)
          { T' with heap := T'.heap ++ [v] }) :
    ∀ (C : PureCtx), C.sidesPure = true → ∀ {M N : Expr},
      EvalEquivAt (P 0) M N →
      EvalEquivAt (P C.emDepth) (C.plug M) (C.plug N) := by
  intro C
  induction C with
  | hole =>
      intro _ M N h
      simpa only [PureCtx.plug, PureCtx.emDepth] using h
  | ifteCond c t' e' ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure] at h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.ifteCond_cong (ih h_sides h) t' e'
  | ifteThen ec c ee ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure, Bool.and_eq_true] at h_sides
      obtain ⟨h_pec, h_sides'⟩ := h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.ifteThen_cong (ih h_sides' h) ec ee
        (fun ptable level env T hP k v_c T_c h_ec =>
          h_closed c.emDepth ptable level ec env T h_pec hP k v_c T_c h_ec)
  | ifteElse ec t c ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure, Bool.and_eq_true] at h_sides
      obtain ⟨h_pec, h_sides'⟩ := h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.ifteElse_cong (ih h_sides' h) ec t
        (fun ptable level env T hP k v_c T_c h_ec =>
          h_closed c.emDepth ptable level ec env T h_pec hP k v_c T_c h_ec)
  | set x c ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure] at h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.set_cong (ih h_sides h) x
  | em c ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure] at h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.em_cong_shift (ih h_sides h)
        (fun ptable level env T hP T_mat h_mat upEnv h_env =>
          h_em c.emDepth ptable level env T hP T_mat h_mat upEnv h_env)
  | app pre c post ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure, Bool.and_eq_true] at h_sides
      obtain ⟨h_ppre, h_sides'⟩ := h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      cases pre with
      | nil =>
          simpa only [List.nil_append] using
            EvalEquivAt.appHead_cong (ih h_sides' h) post
      | cons hd pre' =>
          simp only [PureList, Bool.and_eq_true] at h_ppre
          obtain ⟨h_phd, h_ppre'⟩ := h_ppre
          simpa only [List.cons_append] using
            EvalEquivAt.appArg_cong_pure (ih h_sides' h)
              (h_closed c.emDepth) hd h_phd pre' post h_ppre'
  | primAppFun c args ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure] at h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.primAppFun_cong (ih h_sides h) args
  | primAppArg f pre c post ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure, Bool.and_eq_true] at h_sides
      obtain ⟨⟨h_pf, h_ppre⟩, h_sides'⟩ := h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.primAppArg_cong_pure (ih h_sides' h)
        (h_closed c.emDepth) f h_pf pre post h_ppre
  | letEVal x c b ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure] at h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.letEVal_cong (ih h_sides h) x b
  | letEBody x ev c ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure, Bool.and_eq_true] at h_sides
      obtain ⟨h_pev, h_sides'⟩ := h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      exact EvalEquivAt.letEBody_cong (ih h_sides' h) x ev
        (fun ptable level env T hP k v T' h_ev =>
          h_alloc c.emDepth ptable level x ev env T h_pev hP k v T' h_ev)
  | seq pre c post ih =>
      intro h_sides M N h
      simp only [PureCtx.sidesPure, Bool.and_eq_true] at h_sides
      obtain ⟨h_ppre, h_sides'⟩ := h_sides
      simp only [PureCtx.plug, PureCtx.emDepth]
      cases pre with
      | nil =>
          simpa only [List.nil_append] using
            EvalEquivAt.seqHead_cong (ih h_sides' h) post
      | cons hd pre' =>
          simp only [PureList, Bool.and_eq_true] at h_ppre
          obtain ⟨h_phd, h_ppre'⟩ := h_ppre
          simpa only [List.cons_append] using
            EvalEquivAt.seqTail_cong_pure (ih h_sides' h)
              (h_closed c.emDepth) hd h_phd pre' post h_ppre'

end LeanBlack
