/-
  lean-sage: scaffolding the `.lam` case of contextual β as a
  CakeML-style simulation — a *typed target*, not a proof.

  `CtxEquiv.lean` shows the `.lam` gap reduces to a *conditional*
  ground-contextual equivalence (the `EvalEquivAt` and unconditional
  `CtxEquiv` targets are both proven impossible there). The route is the
  CakeML method the artifact already instantiates: a value relation
  parametrized over the *closure-body relation*. lean-sage's
  `ValVis_aux_weak` (`Bisim.lean`) is the **equality instance** —
  closures relate when `body_a = body_b` with captured envs
  pointwise-bisimilar. Generalizing that one clause from `=` to a
  β-transform relation is the standard CakeML move (known-call inlining
  is β on known applications, proved exactly this way).

  This file supplies, with **no `sorry` and no axiom**:

  - `BetaRel` — the closure-body relation (the recon found lean-sage has
    no expression-level "equal up to evaluation" relation). PROVEN a
    reflexive–transitive **congruence**, reusing `Ctx.comp`.
  - `ValVisβ_aux` / `ValVisβ`, `EnvVisβ_aux` / `EnvVisβ` — `ValVis_aux_weak`
    / `EnvVis_aux_weak` with the closure-body clause relaxed to `BetaRel`.
  - `FrameStmtβ_eval` — the `frame_tower`-shaped fundamental lemma the
    `.lam` case needs, stated as a `Prop`-valued definition: a
    *different-program* simulation (the two sides run `BetaRel`-related
    code) under the **standard-gate** condition (`BuiltinReady`) that
    distinguishes it from `frame_tower`. Proving `∀ n, FrameStmtβ_eval n`
    is the open core (routes (a) closure-relation + (b) gate threading).

  The weakening `ValVis_weak ⊆ ValVisβ` holds by the same structural
  induction as `Bisim.ValVis_aux_to_weak` with `BetaRel.refl` discharging
  the body clause; it is routine and omitted here.
-/
import LeanBlack.CtxEquiv
import LeanBlack.Bisim
import LeanBlack.ContextualBetaPure

namespace LeanBlack

/-! ## 1. The closure-body relation `BetaRel` (proven a congruence) -/

/-- One contextual β-contraction: `(λx. body) v ↝ let x = v in body`
    at some context position. -/
def BetaStep (e_a e_b : Expr) : Prop :=
  ∃ (C : Ctx) (x : String) (body v : Expr),
    e_a = C.plug (.app [.lam [x] body, v]) ∧ e_b = C.plug (.letE x v body)

/-- The closure-body relation: reflexive–transitive closure of
    contextual β-contraction. Replaces `ValVis_weak`'s `body_a = body_b`. -/
inductive BetaRel : Expr → Expr → Prop
  | refl (e : Expr) : BetaRel e e
  | tail {a b c : Expr} : BetaRel a b → BetaStep b c → BetaRel a c

/-- Redex and contractum are `BetaRel` in any context. -/
theorem BetaRel.beta (C : Ctx) (x : String) (body v : Expr) :
    BetaRel (C.plug (.app [.lam [x] body, v])) (C.plug (.letE x v body)) :=
  .tail (.refl _) ⟨C, x, body, v, rfl, rfl⟩

theorem BetaRel.trans {a b c : Expr}
    (hab : BetaRel a b) (hbc : BetaRel b c) : BetaRel a c := by
  induction hbc with
  | refl => exact hab
  | tail _ step ih => exact .tail ih step

/-- A single β step survives plugging into any context — reusing
    `Ctx.comp` / `plug_comp`. -/
theorem BetaStep.congr {a b : Expr} (h : BetaStep a b) (D : Ctx) :
    BetaStep (D.plug a) (D.plug b) := by
  obtain ⟨C, x, body, v, ha, hb⟩ := h
  exact ⟨D.comp C, x, body, v, by rw [ha, Ctx.plug_comp], by rw [hb, Ctx.plug_comp]⟩

/-- **`BetaRel` is a congruence** — closed under every context former,
    binders included, for the same reason `CtxEquiv` is: composition. -/
theorem BetaRel.congr {a b : Expr} (h : BetaRel a b) (D : Ctx) :
    BetaRel (D.plug a) (D.plug b) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact .tail ih (step.congr D)

/-! ### `BetaRel` inversions — building blocks for the fundamental
    lemma's base and closure cases. -/

/-- β never fires from a numeral (it has no redex position). -/
theorem BetaRel.num_eq {i : Int} {b : Expr} (h : BetaRel (.num i) b) :
    b = .num i := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
      subst ih; obtain ⟨C, _, _, _, hC, _⟩ := step
      cases C <;> simp [Ctx.plug] at hC

/-- β never fires from a boolean. -/
theorem BetaRel.bool_eq {c : Bool} {b : Expr} (h : BetaRel (.bool c) b) :
    b = .bool c := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
      subst ih; obtain ⟨C, _, _, _, hC, _⟩ := step
      cases C <;> simp [Ctx.plug] at hC

/-- β never fires from a variable. -/
theorem BetaRel.var_eq {y : String} {b : Expr} (h : BetaRel (.var y) b) :
    b = .var y := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
      subst ih; obtain ⟨C, _, _, _, hC, _⟩ := step
      cases C <;> simp [Ctx.plug] at hC

/-- **β under a binder stays under the binder, β-relating the body.**
    The closure-case inversion the fundamental lemma needs: relating a
    `λ` yields a `λ` with the same params and a β-related body. -/
theorem BetaRel.lam_inv {ps : List String} {body b : Expr}
    (h : BetaRel (.lam ps body) b) :
    ∃ body', b = .lam ps body' ∧ BetaRel body body' := by
  induction h with
  | refl => exact ⟨body, rfl, .refl _⟩
  | tail _ step ih =>
      obtain ⟨body', rfl, hbody'⟩ := ih
      obtain ⟨C, x, bb, v, hC, hbb⟩ := step
      cases C with
      | lam ps2 C' =>
          simp only [Ctx.plug, Expr.lam.injEq] at hC
          obtain ⟨rfl, rfl⟩ := hC
          exact ⟨C'.plug (.letE x v bb), by rw [hbb]; simp [Ctx.plug],
                 hbody'.tail ⟨C', x, bb, v, rfl, rfl⟩⟩
      | _ => simp [Ctx.plug] at hC

/-! ## 2. The body-relaxed value/env relations -/

/-- `ValVis_aux_weak` with its closure-body clause relaxed from
    `body_a = body_b` to `BetaRel body_a body_b`. Every other case is
    verbatim. -/
def ValVisβ_aux : Nat → Val → Val → Heap → Heap → Prop
  | 0, _, _, _, _ => True
  | _ + 1, .num a,            .num b,            _,  _   => a = b
  | _ + 1, .bool a,           .bool b,           _,  _   => a = b
  | _ + 1, .nilV,             .nilV,             _,  _   => True
  | _ + 1, .sym a,            .sym b,            _,  _   => a = b
  | _ + 1, .prim a,           .prim b,           _,  _   => a = b
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _,  _   => True
  | n + 1, .cons x_a y_a,     .cons x_b y_b,     h_a, h_b =>
      ValVisβ_aux n x_a x_b h_a h_b ∧ ValVisβ_aux n y_a y_b h_a h_b
  | n + 1, .closure ps_a body_a cenv_a,
           .closure ps_b body_b cenv_b, h_a, h_b =>
      ps_a = ps_b ∧ BetaRel body_a body_b ∧
      (∀ x, match cenv_a.lookup x, cenv_b.lookup x with
            | none, none => True
            | some i_a, some i_b =>
                match h_a[i_a]?, h_b[i_b]? with
                | some v_a, some v_b => ValVisβ_aux n v_a v_b h_a h_b
                | _, _ => False
            | _, _ => False)
  | _ + 1, _, _, _, _ => False

def ValVisβ (v_a v_b : Val) (h_a h_b : Heap) : Prop :=
  ∀ n, ValVisβ_aux n v_a v_b h_a h_b

/-- Env relation whose cells are `ValVisβ_aux`-related (mirrors
    `EnvVis_aux_weak`). -/
def EnvVisβ_aux (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ x, match env_a.lookup x, env_b.lookup x with
       | none, none => True
       | some i_a, some i_b =>
           match h_a[i_a]?, h_b[i_b]? with
           | some v_a, some v_b => ValVisβ_aux n v_a v_b h_a h_b
           | _, _ => False
       | _, _ => False

def EnvVisβ (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ n, EnvVisβ_aux n env_a env_b h_a h_b

/-- The closure clause, packaged (validates the def reduces as intended). -/
theorem ValVisβ_aux_closure (n : Nat)
    (ps_a ps_b : List String) (body_a body_b : Expr)
    (cenv_a cenv_b : Env) (h_a h_b : Heap) :
    ValVisβ_aux (n + 1)
        (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b
    ↔ (ps_a = ps_b ∧ BetaRel body_a body_b ∧
       EnvVisβ_aux n cenv_a cenv_b h_a h_b) := by
  simp [ValVisβ_aux, EnvVisβ_aux]

/-- **`ValVisβ` does exactly what it is for.** It relates the
    redex-closure `λ-capturing (λx. x) 0` and the contractum-closure
    `λ-capturing (let x = 0 in x)` — β-related bodies under a binder —
    which `ValVis_weak` *cannot* (it demands `body_a = body_b`). This is
    the artifact's own Wand pair, and it is the whole point of the
    relaxation: the closures that `lam_EvalEquiv_congruence_fails`
    (`CtxEquiv.lean`) shows are distinct *values* are nonetheless related
    by `ValVisβ`. -/
theorem ValVisβ_relates_beta_closures :
    ValVisβ (.closure [] (.app [.lam ["x"] (.var "x"), .num 0]) .nil)
            (.closure [] (.letE "x" (.num 0) (.var "x")) .nil) [] []
    ∧ ¬ ValVis_weak (.closure [] (.app [.lam ["x"] (.var "x"), .num 0]) .nil)
            (.closure [] (.letE "x" (.num 0) (.var "x")) .nil) [] [] := by
  refine ⟨fun n => ?_, fun h => ?_⟩
  · cases n with
    | zero => trivial
    | succ n =>
        rw [ValVisβ_aux_closure]
        exact ⟨rfl, BetaRel.beta .hole "x" (.var "x") (.num 0),
               fun x => by simp [Env.lookup]⟩
  · have h1 := h 1
    simp [ValVis_aux_weak] at h1

/-- **Closure formation respects the body relaxation.** Two closures with
    the same params, `BetaRel`-related bodies, and `ValVisβ`-related
    captured environments are `ValVisβ`-related. This is the relational
    content of the `.lam` case — what lets β-related lambda bodies produce
    related closures (the general lemma behind the concrete witness above). -/
theorem ValVisβ_lam_closures (ps : List String) (body body' : Expr)
    (env_a env_b : Env) (h_a h_b : Heap)
    (hbody : BetaRel body body') (henv : EnvVisβ env_a env_b h_a h_b) :
    ValVisβ (.closure ps body env_a) (.closure ps body' env_b) h_a h_b := by
  intro n
  cases n with
  | zero => trivial
  | succ n => rw [ValVisβ_aux_closure]; exact ⟨rfl, hbody, henv n⟩

/-! ## 3. The fundamental lemma the `.lam` case needs (stated, not proved)

`FrameStmtβ_eval n` is the β-analog of `Frame.FrameStmtT`'s `eval` clause.
Two differences carry all the content:

* the two sides run **`BetaRel`-related** expressions `exp_a` / `exp_b`
  (not one shared `exp`) and the result is **`ValVisβ`**-related — this is
  the closure-relation generalization (route (a)); and
* a **`BuiltinReady`** premise on each side pins the `base-apply` gate to
  the standard builtin — the gate threading (route (b)) that `frame_tower`
  does not need (it is a same-program bisimulation) but β does, since the
  redex applies through the gate and the contractum does not.

A faithful full statement would also thread β-relaxed analogs of
`WFCtxT` / `HeapEvolution` / `ValValid` (mechanical; omitted here for
legibility). `∀ n, FrameStmtβ_eval n` — proved by fuel induction with the
closure/apply case threading the relaxed relation, à la `frame_tower` — is
the open core; `BetaRel.congr` above is the (free) congruence half. -/
def FrameStmtβ_eval (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exp_a exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    BetaRel exp_a exp_b →
    BuiltinReady ptable level env_a T_a →
    BuiltinReady ptable level env_b T_b →
    EnvVisβ env_a env_b T_a.heap T_b.heap →
    eval n ptable level exp_a env_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      eval n ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap

/-- **The scaffold discharges the `.lam` case of the fundamental lemma,
    end-to-end and gate-free.** Evaluating `λps. body` against `env_a` and
    its `BetaRel`-image against a `ValVisβ`-related `env_b` yields
    `ValVisβ`-related closures, with the env relation preserved. No
    `BuiltinReady` premise is needed — forming a closure applies nothing,
    so the gate plays no role.

    This is the function-*introduction* half of `FrameStmtβ_eval`, and it
    is exactly the `.lam` carve-out the artifact left open, now closed at
    the value-relation level. The residual open core is the *elimination*
    side — `.app` / `applyVia`, where the closure is run and the gate
    threading (route (b)) bites — together with the structural cases
    (`.ifte` / `.letE` / `.seq` / `.set` / `.em` / `.primApp`), each a
    `BetaRel`-inversion plus an IH thread. -/
theorem frameβ_lam_case (n : Nat) (ptable : PolicyTable) (level : Nat)
    (ps : List String) (body exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.lam ps body) exp_b)
    (henv : EnvVisβ env_a env_b T_a.heap T_b.heap)
    (heval : eval (n + 1) ptable level (.lam ps body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap := by
  rw [eval_lam_closure] at heval
  injection heval with heval'
  injection heval' with hr ht
  subst hr; subst ht
  obtain ⟨body', rfl, hbody⟩ := hβ.lam_inv
  exact ⟨.closure ps body' env_b, T_b,
         eval_lam_closure n ptable level ps body' env_b T_b,
         ValVisβ_lam_closures ps body body' env_a env_b T_a.heap T_b.heap hbody henv,
         henv⟩

/-- Base case: numerals (non-allocating, gate-free). -/
theorem frameβ_num_case (n : Nat) (ptable : PolicyTable) (level : Nat)
    (i : Int) (exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.num i) exp_b)
    (henv : EnvVisβ env_a env_b T_a.heap T_b.heap)
    (heval : eval (n + 1) ptable level (.num i) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap := by
  have hb := hβ.num_eq; subst hb
  simp only [eval] at heval
  injection heval with h1; injection h1 with hr ht; subst hr; subst ht
  exact ⟨.num i, T_b, by simp [eval],
         fun m => by cases m <;> simp [ValVisβ_aux], henv⟩

/-- Elimination of a variable (non-allocating): `EnvVisβ` threads the
    lookup to a `ValVisβ`-related value on the other side. This exercises
    the env relation, completing the non-allocating fragment. -/
theorem frameβ_var_case (n : Nat) (ptable : PolicyTable) (level : Nat)
    (y : String) (exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.var y) exp_b)
    (henv : EnvVisβ env_a env_b T_a.heap T_b.heap)
    (heval : eval (n + 1) ptable level (.var y) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap := by
  have hb := hβ.var_eq; subst hb
  simp only [eval] at heval
  cases hla : env_a.lookup y with
  | none => simp [hla] at heval
  | some idx_a =>
    simp only [hla] at heval
    cases hpa : T_a.heap[idx_a]? with
    | none => simp [hpa] at heval
    | some va =>
      simp only [hpa] at heval
      injection heval with h1; injection h1 with hr ht; subst hr; subst ht
      have he := henv 1 y
      simp only [hla] at he
      cases hlb : env_b.lookup y with
      | none => simp [hlb] at he
      | some idx_b =>
        simp only [hlb, hpa] at he
        cases hpb : T_b.heap[idx_b]? with
        | none => simp [hpb] at he
        | some vb =>
          refine ⟨vb, T_b, by simp only [eval, hlb, hpb], fun m => ?_, henv⟩
          have hm := henv m y
          simp only [hla, hlb, hpa, hpb] at hm
          exact hm

/-! ### Reach of this (simplified) `FrameStmtβ_eval`, and the boundary

The **non-allocating fragment is now fully discharged**: `frameβ_num_case`
(`.bool` is identical), `frameβ_var_case`, `frameβ_lam_case`. None of them
needs a `BuiltinReady` premise or any heap-evolution invariant — they form
or read values without extending the heap.

The remaining cases do **not** go through on *this* statement, and the
reason is structural, not incidental: `.letE` and `.app` *allocate* (bind
let-values / arguments), so threading the IH requires re-establishing
`EnvVisβ` / `ValVisβ` across the heap extension. The `HeapEvolution` /
`ValValid` invariants dropped above "for legibility" are therefore
**load-bearing** for those cases, not cosmetic. `.app` additionally routes
through `applyVia` (the gate — route (b)). So the faithful obligation is
`Frame.FrameStmtT` with `ValVis ↦ ValVisβ` and the shared expression
replaced by a `BetaRel` pair, the *full* invariant set intact; proving it
(by the same fuel induction, now with `BetaRel` inversions at each case)
is the open core. -/

end LeanBlack
