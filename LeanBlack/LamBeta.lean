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
  - §4: the heap-extension substrate for the allocating cases —
    `ValVisβ_extends` / `EnvVisβ_extends` (faithful ports of `Bisim`'s
    `_weak` extension lemmas) and, the genuine new relational content,
    `EnvVisβ_alloc_cons`: threading `EnvVisβ` across a *cross-side*
    allocation, where `frame_tower` instead proves the two environments
    Lean-equal. Plus the `.ifte` / `.letE` `BetaRel` inversions, and §4d's
    **`BetaRel.app_inv`** — the elimination side's structural primitive (β
    under `.app` is a disjunction: still an `.app`, or a root contraction)
    over `BetaRelList` (the `evalList`-clause relation).
    §5 records precisely what this closes and what stays open.
  - §6: the faithful eval obligation (`HeapEvolutionβ`, `WFβ`,
    `FrameβEvalStmt`) with **every gate-free structural case discharged** —
    `frameβ_letE_eval` (`.letE`, a port of `frame_tower`'s `.letE` with
    `EnvVisβ_alloc_cons` replacing the cons-env equality), `frameβ_ifte_eval`
    (`.ifte`, with `ValVisβ_bool_false_iff` forcing cross-side branch
    agreement), `frameβ_seq_eval` (`.seq`, list-structured via
    `seq_cons_inv`), `frameβ_evalList_eval` (the `evalList` argument-list
    traversal, the two-IH list clause over `ListValVisβ` that bridges into
    `.app`), and `EnvVisβ_allocStep_chain` (§6g, the closure-apply argument
    binding — the gate-free half of `applyDirect`'s closure case, a β-port of
    `Bisim.alloc_chain_bisim`). Proof that the §4 substrate composes into real
    fundamental-lemma cases. Only the `WFCtxTβ` statement-wrapper upgrade and
    the reflective gate dispatch (`applyVia`'s `base-apply` lookup, the
    closure-body eval, `.em`/`.set`) remain (the open core).

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
is the open core.

§4 below builds the part of that substrate that is *independent of the
statement wrapper*: the β heap-extension lemmas and — the genuine new
content — the cross-side allocation lemma `EnvVisβ_alloc_cons` that the
binder needs once the heaps diverge. §4c adds the structural `BetaRel`
inversions the fuel induction consumes case-by-case. -/

/-! ## 4. Faithful β-infrastructure for the *allocating* cases

The §3 scaffold discharges the non-allocating cases against a *sketch*
of `FrameStmtβ_eval` that drops `HeapEvolution` / `ValValid`. The
allocating cases (`.letE`, `.app`) cannot be threaded on that sketch:
binding a value extends the heap, and lifting `ValVisβ` / `EnvVisβ`
across that extension needs the heap-validity invariants. This section
builds the heap-extension substrate for the β-relation and the one
genuinely *new* relational lemma the binder needs.

`ValValid` / `HeapValid` / `EnvValid` (`Bisim.lean`) are **body-agnostic**
— a closure's validity is `EnvValid` of its captured env, never a
predicate on the body — so they transfer to the β-setting *verbatim*.
No β-analog is needed; they are reused unchanged below. Only the
*cross-side* relations (`ValVis`/`EnvVis`, which embed the closure-body
relation) need the `BetaRel` relaxation, already supplied by `ValVisβ`
/ `EnvVisβ` in §2.

**The point of divergence from `frame_tower`.** Its `.letE` case
(`Frame.lean`) proves the two cons-extended environments **Lean-equal**,
from `WFCtxT.env_eq` (same env both sides) and `heap_len_eq` (same fresh
index). For β *both premises fail*: the two sides run different code, and
the redex `(λx.e) v` allocates through the closure-apply while the
contractum `let x = v in e` allocates one cell — *different cell counts*,
so the fresh indices differ. `EnvVisβ_alloc_cons` (§4b) replaces that
equality with `EnvVisβ`-relatedness — the relational content the
different-program (CakeML-style) simulation needs at the binder, and the
step the §3 sketch could not perform. -/

/-! ### 4a. `ValVisβ` / `EnvVisβ` preserved under heap extension

Verbatim ports of `Bisim.ValVis_aux_weak_extends` /
`EnvVis_aux_weak_extends`: the closure-body clause (there `=`, here
`BetaRel`) is heap-independent, so it rides through every case
untouched — the proofs differ from the `_weak` originals only in the
two relation names. -/

mutual

theorem ValVisβ_aux_extends : ∀ (n : Nat) (v_a v_b : Val)
    (h_a h_b ext_a ext_b : Heap),
    HeapValid h_a → HeapValid h_b →
    ValValid v_a h_a → ValValid v_b h_b →
    ValVisβ_aux n v_a v_b h_a h_b →
    ValVisβ_aux n v_a v_b (h_a ++ ext_a) (h_b ++ ext_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, ext_a, ext_b,
      hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨ValVisβ_aux_extends n x_a x_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.1 hv_b.1 h_vis.1,
       ValVisβ_aux_extends n y_a y_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.2 hv_b.2 h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, ext_a, ext_b, hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨h_vis.1, h_vis.2.1,
       EnvVisβ_aux_extends n cenv_a cenv_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a hv_b h_vis.2.2⟩
  -- Mismatched constructor pairs at depth ≥ 1: h_vis is `False`.
  | _ + 1, .num _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .prim _,           _, _, _, _, _, _, _, _, h => h.elim

theorem EnvVisβ_aux_extends (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap),
      HeapValid h_a → HeapValid h_b →
      EnvValid env_a h_a → EnvValid env_b h_b →
      EnvVisβ_aux n env_a env_b h_a h_b →
      EnvVisβ_aux n env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro env_a env_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b h_vis x
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => simp [hl_a, hl_b, EnvVisβ_aux]
      | some _ => rw [hl_b] at h_x; simp at h_x
  | some i_a =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => rw [hl_b] at h_x; simp at h_x
      | some i_b =>
          rw [hl_b] at h_x
          simp only at h_x
          have h_lt_a : i_a < h_a.length := hv_a x i_a hl_a
          have h_lt_b : i_b < h_b.length := hv_b x i_b hl_b
          have h_eq_a : (h_a ++ ext_a)[i_a]? = h_a[i_a]? :=
            getElem?_prefix h_a ext_a i_a h_lt_a
          have h_eq_b : (h_b ++ ext_b)[i_b]? = h_b[i_b]? :=
            getElem?_prefix h_b ext_b i_b h_lt_b
          simp only [hl_a, hl_b]
          rw [h_eq_a, h_eq_b]
          cases hp_a : h_a[i_a]? with
          | none => rw [hp_a] at h_x; simp at h_x
          | some v_a =>
              cases hp_b : h_b[i_b]? with
              | none => rw [hp_a, hp_b] at h_x; simp at h_x
              | some v_b =>
                  rw [hp_a, hp_b] at h_x
                  have hv_va : ValValid v_a h_a := hh_a i_a v_a hp_a
                  have hv_vb : ValValid v_b h_b := hh_b i_b v_b hp_b
                  exact ValVisβ_aux_extends n v_a v_b h_a h_b ext_a ext_b
                    hh_a hh_b hv_va hv_vb h_x

end

/-- Universal-depth heap extension for `ValVisβ`. -/
theorem ValVisβ_extends (v_a v_b : Val) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : ValValid v_a h_a) (hv_b : ValValid v_b h_b)
    (h_vis : ValVisβ v_a v_b h_a h_b) :
    ValVisβ v_a v_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact ValVisβ_aux_extends n v_a v_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b (h_vis n)

/-- Universal-depth heap extension for `EnvVisβ`. -/
theorem EnvVisβ_extends (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : EnvValid env_a h_a) (hv_b : EnvValid env_b h_b)
    (h_vis : EnvVisβ env_a env_b h_a h_b) :
    EnvVisβ env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact EnvVisβ_aux_extends n env_a env_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b (h_vis n)

/-! ### 4b. Threading `EnvVisβ` across a cross-side allocation

`EnvVisβ_cons` mirrors `Bisim.EnvVis_cons`; `EnvVisβ_alloc_cons`
specializes it to the allocation site (`Heap.alloc h v = (h ++ [v],
h.length)`), where each side appends one cell holding `ValVisβ`-related
values at the fresh index `heap.length`. -/

/-- Per-depth cons: a name bound to `ValVisβ`-related fresh cells, over
    `EnvVisβ`-related tails, stays `EnvVisβ`. Mirror of
    `Bisim.EnvVis_aux_cons`. -/
theorem EnvVisβ_aux_cons (d : Nat) (x : String) (idx_a idx_b : Nat)
    (env_a env_b : Env) (h_a h_b : Heap) (v_a v_b : Val)
    (h_lookup_a : h_a[idx_a]? = some v_a)
    (h_lookup_b : h_b[idx_b]? = some v_b)
    (h_vv : ValVisβ_aux d v_a v_b h_a h_b)
    (h_env : EnvVisβ_aux d env_a env_b h_a h_b) :
    EnvVisβ_aux d (.cons x idx_a env_a) (.cons x idx_b env_b) h_a h_b := by
  intro name
  simp only [Env.lookup]
  by_cases h_eq : x = name
  · subst h_eq
    simp only [beq_self_eq_true, ↓reduceIte, h_lookup_a, h_lookup_b]
    exact h_vv
  · have h_neq : (x == name) = false := by rw [beq_eq_false_iff_ne]; exact h_eq
    simp only [h_neq, Bool.false_eq_true, ↓reduceIte]
    exact h_env name

/-- Universal-depth cons. Mirror of `Bisim.EnvVis_cons`. -/
theorem EnvVisβ_cons (x : String) (idx_a idx_b : Nat)
    (env_a env_b : Env) (h_a h_b : Heap) (v_a v_b : Val)
    (h_lookup_a : h_a[idx_a]? = some v_a)
    (h_lookup_b : h_b[idx_b]? = some v_b)
    (h_vv : ValVisβ v_a v_b h_a h_b)
    (h_env : EnvVisβ env_a env_b h_a h_b) :
    EnvVisβ (.cons x idx_a env_a) (.cons x idx_b env_b) h_a h_b := by
  intro d
  exact EnvVisβ_aux_cons d x idx_a idx_b env_a env_b h_a h_b v_a v_b
    h_lookup_a h_lookup_b (h_vv d) (h_env d)

/-- **The cross-side allocation lemma — the binder's relational core.**
    Given `EnvVisβ`-related environments and `ValVisβ`-related values to
    bind, allocating each value (fresh cell at `heap.length`) and
    extending each environment with `x ↦ fresh` yields `EnvVisβ`-related
    environments at the extended heaps. Where `frame_tower`'s `.letE`
    proves the two cons-envs *equal*, this proves them *related* — the
    move from a same-program bisimulation to the different-program (β)
    simulation, with the fresh indices `h_a.length` / `h_b.length`
    free to differ. -/
theorem EnvVisβ_alloc_cons (x : String) (env_a env_b : Env) (v_a v_b : Val)
    (h_a h_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hev_a : EnvValid env_a h_a) (hev_b : EnvValid env_b h_b)
    (hvv_a : ValValid v_a h_a) (hvv_b : ValValid v_b h_b)
    (h_vis_v : ValVisβ v_a v_b h_a h_b)
    (h_env : EnvVisβ env_a env_b h_a h_b) :
    EnvVisβ (.cons x h_a.length env_a) (.cons x h_b.length env_b)
            (h_a ++ [v_a]) (h_b ++ [v_b]) := by
  have h_lookup_a : (h_a ++ [v_a])[h_a.length]? = some v_a := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have h_lookup_b : (h_b ++ [v_b])[h_b.length]? = some v_b := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have h_vis_v' : ValVisβ v_a v_b (h_a ++ [v_a]) (h_b ++ [v_b]) :=
    ValVisβ_extends v_a v_b h_a h_b [v_a] [v_b] hh_a hh_b hvv_a hvv_b h_vis_v
  have h_env' : EnvVisβ env_a env_b (h_a ++ [v_a]) (h_b ++ [v_b]) :=
    EnvVisβ_extends env_a env_b h_a h_b [v_a] [v_b] hh_a hh_b hev_a hev_b h_env
  exact EnvVisβ_cons x h_a.length h_b.length env_a env_b
    (h_a ++ [v_a]) (h_b ++ [v_b]) v_a v_b h_lookup_a h_lookup_b h_vis_v' h_env'

/-! ### 4c. The remaining `BetaRel` structural inversions

`lam_inv` (§1) handles the binder; each *structural* case of the
fundamental lemma needs the analogous inversion — "β under `F` stays an
`F` with `BetaRel`-related children" — to expose the other side's shape.
Here are the two control-flow formers; `.seq` / `.set` / `.primApp`
follow the same template. The `.app` case is the genuinely hard one: it
additionally admits a *root* contraction (the redex *is* an app), so its
inversion is a disjunction, not a congruence — that is the elimination
side of the open core, discharged in §4d. -/

/-- β under `.ifte` stays an `.ifte`, β-relating the three children. -/
theorem BetaRel.ifte_inv {c t e b : Expr}
    (h : BetaRel (.ifte c t e) b) :
    ∃ c' t' e', b = .ifte c' t' e' ∧ BetaRel c c' ∧ BetaRel t t' ∧ BetaRel e e' := by
  induction h with
  | refl => exact ⟨c, t, e, rfl, .refl _, .refl _, .refl _⟩
  | tail _ step ih =>
      obtain ⟨c', t', e', rfl, hc, ht, he⟩ := ih
      obtain ⟨C, y, bb, v, hC, hbb⟩ := step
      cases C with
      | ifteCond cC tt ee =>
          simp only [Ctx.plug, Expr.ifte.injEq] at hC
          obtain ⟨hc_eq, ht_eq, he_eq⟩ := hC
          exact ⟨cC.plug (.letE y v bb), tt, ee, by rw [hbb]; simp [Ctx.plug],
                 (hc_eq ▸ hc).tail ⟨cC, y, bb, v, rfl, rfl⟩, ht_eq ▸ ht, he_eq ▸ he⟩
      | ifteThen ec cC ee =>
          simp only [Ctx.plug, Expr.ifte.injEq] at hC
          obtain ⟨hc_eq, ht_eq, he_eq⟩ := hC
          exact ⟨ec, cC.plug (.letE y v bb), ee, by rw [hbb]; simp [Ctx.plug],
                 hc_eq ▸ hc, (ht_eq ▸ ht).tail ⟨cC, y, bb, v, rfl, rfl⟩, he_eq ▸ he⟩
      | ifteElse ec et cC =>
          simp only [Ctx.plug, Expr.ifte.injEq] at hC
          obtain ⟨hc_eq, ht_eq, he_eq⟩ := hC
          exact ⟨ec, et, cC.plug (.letE y v bb), by rw [hbb]; simp [Ctx.plug],
                 hc_eq ▸ hc, ht_eq ▸ ht, (he_eq ▸ he).tail ⟨cC, y, bb, v, rfl, rfl⟩⟩
      | _ => simp [Ctx.plug] at hC

/-- β under `.letE` stays a `.letE` (same binder), β-relating bound term
    and body. -/
theorem BetaRel.letE_inv {x : String} {e1 body b : Expr}
    (h : BetaRel (.letE x e1 body) b) :
    ∃ e1' body', b = .letE x e1' body' ∧ BetaRel e1 e1' ∧ BetaRel body body' := by
  induction h with
  | refl => exact ⟨e1, body, rfl, .refl _, .refl _⟩
  | tail _ step ih =>
      obtain ⟨e1', body', rfl, h1, h2⟩ := ih
      obtain ⟨C, y, bb, v, hC, hbb⟩ := step
      cases C with
      | letEVal z cC bd =>
          simp only [Ctx.plug, Expr.letE.injEq] at hC
          obtain ⟨hx_eq, he1_eq, hb_eq⟩ := hC
          refine ⟨cC.plug (.letE y v bb), bd, ?_,
                  (he1_eq ▸ h1).tail ⟨cC, y, bb, v, rfl, rfl⟩, hb_eq ▸ h2⟩
          rw [hbb]; simp only [Ctx.plug]; rw [hx_eq]
      | letEBody z ev cC =>
          simp only [Ctx.plug, Expr.letE.injEq] at hC
          obtain ⟨hx_eq, he1_eq, hb_eq⟩ := hC
          refine ⟨ev, cC.plug (.letE y v bb), ?_,
                  he1_eq ▸ h1, (hb_eq ▸ h2).tail ⟨cC, y, bb, v, rfl, rfl⟩⟩
          rw [hbb]; simp only [Ctx.plug]; rw [hx_eq]
      | _ => simp [Ctx.plug] at hC

/-! ### 4d. The `.app` `BetaRel` inversion — the elimination side's
    structural primitive

Unlike the §4c congruences, β under `.app` admits a **root** contraction
(the redex *is* an application), so its inversion is a *disjunction*:
either every contraction stayed internal to the argument list — `b` is
still an `.app` whose arguments are `BetaRelList`-related to the original
— or at some point the application `(λx. body) v` itself contracted, after
which `b` is `BetaRel`-reachable from the contractum `let x = v in body`.

This is the inversion the gated `.app` / `applyVia` eval case consumes
(the elimination side of the open core). `BetaRelList` — pointwise
`BetaRel` on argument lists — is *also* the relation the full mutual
statement's `evalList` clause needs (the `ListValVisβ` mirror at the
expression level), so it is built here once. -/

/-- Pointwise `BetaRel` on argument lists: the `evalList` analog of
    `BetaRel`, relating two lists of the same length elementwise. -/
inductive BetaRelList : List Expr → List Expr → Prop
  | nil : BetaRelList [] []
  | cons {a b : Expr} {as bs : List Expr} :
      BetaRel a b → BetaRelList as bs → BetaRelList (a :: as) (b :: bs)

theorem BetaRelList.refl : ∀ (xs : List Expr), BetaRelList xs xs
  | []      => .nil
  | _ :: xs => .cons (.refl _) (refl xs)

theorem BetaRelList.trans {as bs cs : List Expr}
    (h1 : BetaRelList as bs) (h2 : BetaRelList bs cs) : BetaRelList as cs := by
  induction h1 generalizing cs with
  | nil => exact h2
  | cons hab _ ih =>
      cases h2 with
      | cons hbc hbcs => exact .cons (hab.trans hbc) (ih hbcs)

theorem BetaRelList.append {as as' bs bs' : List Expr}
    (h1 : BetaRelList as as') (h2 : BetaRelList bs bs') :
    BetaRelList (as ++ bs) (as' ++ bs') := by
  induction h1 with
  | nil => exact h2
  | cons hab _ ih => exact .cons hab ih

/-- **β under `.app` — the disjunction inversion.** Either `b` is still an
    application with `BetaRelList`-related arguments (no root contraction
    fired), or the original application β-reduces to a concrete redex
    `(λx. body) v` and `b` is `BetaRel`-reachable from its contractum
    `let x = v in body` (a root contraction fired, and everything after it
    happens in the contractum). -/
theorem BetaRel.app_inv {args : List Expr} {b : Expr}
    (h : BetaRel (.app args) b) :
    (∃ args', b = .app args' ∧ BetaRelList args args')
    ∨ (∃ (x : String) (body v : Expr),
         BetaRel (.app args) (.app [.lam [x] body, v]) ∧
         BetaRel (.letE x v body) b) := by
  induction h with
  | refl => exact Or.inl ⟨args, rfl, BetaRelList.refl args⟩
  | tail hmid step ih =>
      cases ih with
      | inl hl =>
          obtain ⟨margs, rfl, hForall⟩ := hl
          obtain ⟨C, x, body, v, hC, hb⟩ := step
          cases C with
          | hole =>
              simp only [Ctx.plug, Expr.app.injEq] at hC
              subst hC
              exact Or.inr ⟨x, body, v, hmid, by rw [hb]; simp only [Ctx.plug]; exact .refl _⟩
          | app pre C' post =>
              simp only [Ctx.plug, Expr.app.injEq] at hC
              subst hC
              refine Or.inl ⟨pre ++ C'.plug (.letE x v body) :: post, ?_, ?_⟩
              · rw [hb]; simp only [Ctx.plug]
              · exact hForall.trans (BetaRelList.append (BetaRelList.refl pre)
                  (BetaRelList.cons (BetaRel.beta C' x body v) (BetaRelList.refl post)))
          | _ => simp [Ctx.plug] at hC
      | inr hr =>
          obtain ⟨x, body, v, h1, h2⟩ := hr
          exact Or.inr ⟨x, body, v, h1, h2.tail step⟩

/-- **`app_inv` detects the Wand pair's root contraction** — the
    elimination-side analog of `ValVisβ_relates_beta_closures`. For the
    artifact's own redex `(λx. x) 0` reducing to `let x = 0 in x`, the
    contractum is *not* an application, so `app_inv` cannot fall into its
    "still an `.app`" branch; it must (and does) land in the root-
    contraction branch, exposing the very redex `(λx. x) 0` whose
    contractum it reduces through. This pins that the disjunction is not
    vacuously satisfied by the internal branch alone. -/
theorem app_inv_wand_detects_root :
    ∃ (x : String) (body v : Expr),
      BetaRel (.app [.lam ["x"] (.var "x"), .num 0]) (.app [.lam [x] body, v]) ∧
      BetaRel (.letE x v body) (.letE "x" (.num 0) (.var "x")) := by
  have h : BetaRel (.app [.lam ["x"] (.var "x"), .num 0])
                   (.letE "x" (.num 0) (.var "x")) :=
    BetaRel.beta .hole "x" (.var "x") (.num 0)
  rcases h.app_inv with ⟨_, heq, _⟩ | hroot
  · exact absurd heq (by simp)
  · exact hroot

/-! ## 5. What §4 closes, and what is still open

**In hand (this section, sorry-free, axioms ⊆ {propext, Classical.choice,
Quot.sound}).** The body-independent substrate the allocating cases need:

* `ValVisβ_aux_extends` / `EnvVisβ_aux_extends` (and the universal
  `ValVisβ_extends` / `EnvVisβ_extends`) — the β value/env relations are
  preserved under heap extension, the faithful ports of `Bisim`'s `_weak`
  versions.
* `EnvVisβ_cons` and **`EnvVisβ_alloc_cons`** — the binder's relational
  core: an `EnvVisβ`-related environment pair, extended with `x ↦ fresh`
  over `ValVisβ`-related freshly-allocated cells, stays `EnvVisβ`-related.
  This is the exact step `frame_tower`'s `.letE` performs by proving the
  two envs *Lean-equal*; under β they are merely *related* (different code,
  different fresh indices), and this lemma supplies that.
* `BetaRel.ifte_inv` / `BetaRel.letE_inv` — two more structural inversions
  in the `lam_inv` family.
* **`BetaRel.app_inv`** (§4d) — the elimination side's structural primitive,
  now proved: β under `.app` is a *disjunction* — still an `.app` with
  `BetaRelList`-related arguments, or a root contraction to the contractum.
  Built on `BetaRelList` (pointwise `BetaRel` on argument lists, with
  `refl` / `trans` / `append`), which is also the `evalList`-clause relation
  the full mutual statement needs. `app_inv_wand_detects_root` validates that
  the disjunction's root-contraction branch genuinely fires for the Wand pair.

§6 then assembles the eval obligation (`HeapEvolutionβ`, `WFβ`) and
discharges **every gate-free structural case** on it: the allocating
binder (`.letE`, `frameβ_letE_eval`), the branch (`.ifte`,
`frameβ_ifte_eval`), the sequence (`.seq`, `frameβ_seq_eval`), and the
argument-list traversal (`evalList`, `frameβ_evalList_eval` — §6f, the
two-IH list clause producing `ListValVisβ`-related results, the bridge
into `.app`) — the proof that this substrate composes into real
fundamental-lemma cases. Together with the §3 atoms/`.lam`, the **entire
gate-free fragment of the faithful eval/evalList clauses is now closed**.

**Still open (the genuine core, now sharply isolated).**

1. *Upgrade `WFβ` to the full `WFCtxTβ`, and to the mutual statement.*
   §6's `WFβ` carries the load-bearing allocation invariants (`HeapValid`
   / `EnvValid`), all the *structural* cases need. The full wrapper adds
   the policy / materialized-level fields of `Frame.WFCtxT` — relax
   `env_eq` to `EnvVisβ`, drop `heap_len_eq` (β breaks it), relax the
   cross-side level-env fields — which only the reflective `.em` / `.set`
   and gated `.app` read and preserve; plus the `evalList` / `applyVia` /
   `applyDirect` clauses (with a trivial `ListValVisβ`). Deferred
   deliberately, *with* those cases below: a wrapper carrying half-formed
   reflective fields would misstate the boundary.
2. *The elimination side* — `applyVia` / `applyDirect`, the **gate
   threading** (route (b)). The structural and allocation halves are now in
   hand: `app_inv` (§4d) supplies the `BetaRel` inversion (the disjunction
   whose root-contraction branch is the genuine novelty), `BetaRelList` the
   argument relation, `frameβ_evalList_eval` (§6f) discharges the argument-
   list traversal to `ListValVisβ`-related results, and `EnvVisβ_allocStep_chain`
   (§6g) carries `EnvVisβ` through the closure-apply argument binding (the
   gate-free half of `applyDirect`'s closure case). What remains is the
   genuinely reflective core: `applyVia`'s **gate dispatch** — the level-(level+1)
   `base-apply` lookup and cross-level closure call — and, in `applyDirect`'s
   closure case, the body eval (eval IH at fuel `n` over `BetaRel body_a body_b`
   and §6g's `EnvVisβ`). This, with the reflective `.em` / `.set` and the
   policy/level fields of `WFCtxTβ`, is where the real research risk sits;
   `BuiltinReady` (standard gate) is the premise that is meant to tame it. The
   de-risking first target is the concrete Wand pair `(λx. x) 0` / `let x = 0 in x`
   under a binder, whose redex/contractum closures `ValVisβ_relates_beta_closures`
   (§2) already relates.

With every structural case discharged, the remaining work is exactly
(1) the statement wrapper and (2) the gate — no structural plumbing is
left between here and the full `.lam` congruence. -/

/-! ## 6. The faithful eval obligation, and the structural cases

§4 supplies the statement-*independent* substrate. This section assembles
the faithful obligation for the **eval** clause and discharges **every
gate-free structural case** on it — the allocating binder (`.letE`, §6c),
the branch (`.ifte`, §6d), the sequence (`.seq`, §6e), and the
argument-list traversal (`evalList`, §6f) — plus the closure-apply
allocation chain (§6g, the gate-free half of `applyDirect`'s closure case).
The milestone showing the substrate composes into real fundamental-lemma
cases, which the §3 sketch could not.

Pieces: `HeapEvolutionβ` (the cross-side heap-evolution carrier), `WFβ`
(the gate-free fragment's context invariant), `frameβ_letE_eval` (the
`.letE` step, a port of `frame_tower`'s `.letE`), `frameβ_ifte_eval` (the
`.ifte` step, where `ValVisβ_bool_false_iff` forces both sides to the same
branch), `frameβ_seq_eval` (the `.seq` step, list-structured via
`seq_cons_inv`), and `frameβ_evalList_eval` (the `evalList` step, the
two-IH list traversal that bridges into `.app`).

`WFβ` carries the **load-bearing allocation invariants** the §3 sketch
dropped — `HeapValid` / `EnvValid` on both sides — and nothing else. It is
deliberately *not* the full `WFCtxTβ`: the policy / materialized-level
fields of `Frame.WFCtxT` are read and preserved only by the reflective
`.em` / `.set` and the gated `.app`, so they belong with those (open)
cases; bundling half-formed versions now would misstate the boundary. For
the gate-free structural fragment (`.letE` / `.ifte` / `.seq`), `WFβ` +
`EnvVisβ` + `HeapEvolutionβ` + `ValValid` is exactly the faithful invariant
set (`ValValid` / `HeapValid` / `EnvValid` are body-agnostic, reused
verbatim). -/

/-! ### 6a. `HeapEvolutionβ` — cross-side heap-evolution carrier

Mirror of `Bisim.HeapEvolution` with `EnvVisβ_aux` / `ValVisβ_aux` in the
preservation clauses and the `env_a = env_b` precondition **dropped** (β
relates *different* envs). `from_heapExt` reduces to §4's extension
lemmas. -/

structure HeapEvolutionβ (s_a s_b s_a' s_b' : TowerState) : Prop where
  len_a : s_a.heap.length ≤ s_a'.heap.length
  len_b : s_b.heap.length ≤ s_b'.heap.length
  env_preserve : ∀ (n : Nat) (env_a env_b : Env),
    EnvValid env_a s_a.heap → EnvValid env_b s_b.heap →
    EnvVisβ_aux n env_a env_b s_a.heap s_b.heap →
    EnvVisβ_aux n env_a env_b s_a'.heap s_b'.heap
  val_preserve : ∀ (n : Nat) (v_a v_b : Val),
    ValValid v_a s_a.heap → ValValid v_b s_b.heap →
    ValVisβ_aux n v_a v_b s_a.heap s_b.heap →
    ValVisβ_aux n v_a v_b s_a'.heap s_b'.heap

theorem HeapEvolutionβ.refl (s_a s_b : TowerState) :
    HeapEvolutionβ s_a s_b s_a s_b :=
  ⟨Nat.le_refl _, Nat.le_refl _,
   fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem HeapEvolutionβ.trans {s_a s_b s_a' s_b' s_a'' s_b'' : TowerState}
    (h1 : HeapEvolutionβ s_a s_b s_a' s_b')
    (h2 : HeapEvolutionβ s_a' s_b' s_a'' s_b'') :
    HeapEvolutionβ s_a s_b s_a'' s_b'' := by
  refine ⟨Nat.le_trans h1.len_a h2.len_a, Nat.le_trans h1.len_b h2.len_b, ?_, ?_⟩
  · intro n env_a env_b hv_a hv_b h_vis
    have h_vis' := h1.env_preserve n env_a env_b hv_a hv_b h_vis
    exact h2.env_preserve n env_a env_b
      (hv_a.length_mono h1.len_a) (hv_b.length_mono h1.len_b) h_vis'
  · intro n v_a v_b hv_a hv_b h_vis
    have h_vis' := h1.val_preserve n v_a v_b hv_a hv_b h_vis
    exact h2.val_preserve n v_a v_b
      (ValValid.length_mono v_a hv_a h1.len_a) (ValValid.length_mono v_b hv_b h1.len_b) h_vis'

theorem HeapEvolutionβ.from_heapExt {s_a s_b s_a' s_b' : TowerState}
    (hh_a : HeapValid s_a.heap) (hh_b : HeapValid s_b.heap)
    (he_a : HeapExt s_a s_a') (he_b : HeapExt s_b s_b') :
    HeapEvolutionβ s_a s_b s_a' s_b' := by
  obtain ⟨ext_a, hex_a⟩ := he_a
  obtain ⟨ext_b, hex_b⟩ := he_b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex_a, List.length_append]; exact Nat.le_add_right _ _
  · rw [hex_b, List.length_append]; exact Nat.le_add_right _ _
  · intro n env_a env_b hv_a hv_b h_vis
    rw [hex_a, hex_b]
    exact EnvVisβ_aux_extends n env_a env_b s_a.heap s_b.heap ext_a ext_b
      hh_a hh_b hv_a hv_b h_vis
  · intro n v_a v_b hv_a hv_b h_vis
    rw [hex_a, hex_b]
    exact ValVisβ_aux_extends n v_a v_b s_a.heap s_b.heap ext_a ext_b
      hh_a hh_b hv_a hv_b h_vis

/-- Lift a universal-depth `ValVisβ` across `HeapEvolutionβ`. -/
theorem HeapEvolutionβ.valVisβ_preserve {s_a s_b s_a' s_b' : TowerState}
    (h : HeapEvolutionβ s_a s_b s_a' s_b') (v_a v_b : Val)
    (hv_a : ValValid v_a s_a.heap) (hv_b : ValValid v_b s_b.heap)
    (h_vis : ValVisβ v_a v_b s_a.heap s_b.heap) :
    ValVisβ v_a v_b s_a'.heap s_b'.heap :=
  fun n => h.val_preserve n v_a v_b hv_a hv_b (h_vis n)

/-- Lift a universal-depth `EnvVisβ` across `HeapEvolutionβ`. -/
theorem HeapEvolutionβ.envVisβ_preserve {s_a s_b s_a' s_b' : TowerState}
    (h : HeapEvolutionβ s_a s_b s_a' s_b') (env_a env_b : Env)
    (hv_a : EnvValid env_a s_a.heap) (hv_b : EnvValid env_b s_b.heap)
    (h_vis : EnvVisβ env_a env_b s_a.heap s_b.heap) :
    EnvVisβ env_a env_b s_a'.heap s_b'.heap :=
  fun n => h.env_preserve n env_a env_b hv_a hv_b (h_vis n)

/-! ### 6b. `WFβ` and the faithful eval obligation

`WFβ` is the gate-free fragment's context invariant: the four **body-
agnostic** single-side validity facts (`HeapValid` / `EnvValid` on each
side) that allocation threading consumes, taken verbatim from `WFCtxT`.
`FrameβEvalStmt n` is the β-analog of `Frame.FrameStmtT`'s eval clause
(`Frame.lean:899`) — `ValVis ↦ ValVisβ`, `EnvVis ↦ EnvVisβ`,
`WFCtxT ↦ WFβ`, `HeapEvolution ↦ HeapEvolutionβ`, the shared `exp`
replaced by a `BetaRel` pair, and the *full* output invariant set kept
(unlike the §3 sketch). The gate premises (`PolicyTableRespectsBisimT`,
`BuiltinReady`) that the full statement needs for `.app` are absent here:
the structural fragment never applies, so the gate plays no role. -/

structure WFβ (env_a env_b : Env) (T_a T_b : TowerState) : Prop where
  hv_a : HeapValid T_a.heap
  hv_b : HeapValid T_b.heap
  ev_a : EnvValid env_a T_a.heap
  ev_b : EnvValid env_b T_b.heap

def FrameβEvalStmt (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exp_a exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    BetaRel exp_a exp_b →
    WFβ env_a env_b T_a T_b →
    EnvVisβ env_a env_b T_a.heap T_b.heap →
    eval n ptable level exp_a env_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      eval n ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFβ env_a env_b T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

/-! ### 6c. The `.letE` case — first allocating case, faithfully

The inductive step for `.letE`, taking the eval-clause IH as hypothesis
(`ih : FrameβEvalStmt n`), exactly as the `frame_tower` mutual induction
consumes its own `ih_eval`. The port mirrors `Frame.lean:1895`, with two
substitutions carrying all the β-content:

* where `frame_tower` proves the two cons-extended environments **equal**
  (`h_cons_eq`, from `env_eq` + `heap_len_eq`), this uses
  `EnvVisβ_alloc_cons` to prove them **`EnvVisβ`-related** — and never
  needs `heap_len_eq` (the fresh indices `T_a_inner.heap.length` /
  `T_b_inner.heap.length` are free to differ);
* `HeapEvolution` ↦ `HeapEvolutionβ`, `ValVis_extends` ↦ `ValVisβ` via
  `EnvVisβ_alloc_cons`.

The `HeapValid` / `EnvValid` plumbing for the allocated heaps is
body-agnostic and identical to `frame_tower`'s. -/
theorem frameβ_letE_eval (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (e1 body exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmt n)
    (hβ : BetaRel (.letE x e1 body) exp_b)
    (hwf : WFβ env_a env_b T_a T_b)
    (henv : EnvVisβ env_a env_b T_a.heap T_b.heap)
    (heval : eval (n + 1) ptable level (.letE x e1 body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFβ env_a env_b T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨e1', body', rfl, hβ_e, hβ_body⟩ := hβ.letE_inv
  simp only [eval] at heval
  cases he : eval n ptable level e1 env_a T_a with
  | none => rw [he] at heval; simp at heval
  | some pr =>
    obtain ⟨v_a, T_a_inner⟩ := pr
    rw [he] at heval
    obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, hwf_inner, h_he_inner,
            h_env_inner, hv_va, hv_vb⟩ :=
      ih ptable level e1 e1' env_a env_b T_a T_b v_a T_a_inner hβ_e hwf henv he
    simp only [TowerState.alloc, Heap.alloc] at heval
    have h_lookup_a : (T_a_inner.heap ++ [v_a])[T_a_inner.heap.length]? = some v_a := by
      rw [List.getElem?_append_right (Nat.le_refl _)]; simp
    have h_lookup_b : (T_b_inner.heap ++ [v_b])[T_b_inner.heap.length]? = some v_b := by
      rw [List.getElem?_append_right (Nat.le_refl _)]; simp
    -- alloc heaps stay `HeapValid` (body-agnostic; verbatim from frame_tower)
    have hh_a_alloc : HeapValid (T_a_inner.heap ++ [v_a]) := by
      intro i v hp
      by_cases h_lt : i < T_a_inner.heap.length
      · have hp_old : T_a_inner.heap[i]? = some v := by
          have heq := getElem?_prefix T_a_inner.heap [v_a] i h_lt
          rw [← heq]; exact hp
        exact ValValid.heap_extends v (hwf_inner.hv_a i v hp_old) ⟨[v_a], rfl⟩
      · have h_eq : i = T_a_inner.heap.length := by
          have h_le : i < (T_a_inner.heap ++ [v_a]).length := by
            rw [List.getElem?_eq_some_iff] at hp; obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq
        rw [h_lookup_a] at hp; simp only [Option.some.injEq] at hp; subst hp
        exact ValValid.heap_extends v_a hv_va ⟨[v_a], rfl⟩
    have hh_b_alloc : HeapValid (T_b_inner.heap ++ [v_b]) := by
      intro i v hp
      by_cases h_lt : i < T_b_inner.heap.length
      · have hp_old : T_b_inner.heap[i]? = some v := by
          have heq := getElem?_prefix T_b_inner.heap [v_b] i h_lt
          rw [← heq]; exact hp
        exact ValValid.heap_extends v (hwf_inner.hv_b i v hp_old) ⟨[v_b], rfl⟩
      · have h_eq : i = T_b_inner.heap.length := by
          have h_le : i < (T_b_inner.heap ++ [v_b]).length := by
            rw [List.getElem?_eq_some_iff] at hp; obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq
        rw [h_lookup_b] at hp; simp only [Option.some.injEq] at hp; subst hp
        exact ValValid.heap_extends v_b hv_vb ⟨[v_b], rfl⟩
    -- cons-extended envs stay `EnvValid` (body-agnostic; verbatim)
    have hev_a' : EnvValid (.cons x T_a_inner.heap.length env_a) (T_a_inner.heap ++ [v_a]) := by
      intro name i hl
      simp only [List.length_append, List.length_singleton]
      simp only [Env.lookup] at hl
      by_cases h_eq : x = name
      · subst h_eq; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl; omega
      · have h_neq : (x == name) = false := by rw [beq_eq_false_iff_ne]; exact h_eq
        simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
        have := hwf_inner.ev_a name i hl; omega
    have hev_b' : EnvValid (.cons x T_b_inner.heap.length env_b) (T_b_inner.heap ++ [v_b]) := by
      intro name i hl
      simp only [List.length_append, List.length_singleton]
      simp only [Env.lookup] at hl
      by_cases h_eq : x = name
      · subst h_eq; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl; omega
      · have h_neq : (x == name) = false := by rw [beq_eq_false_iff_ne]; exact h_eq
        simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
        have := hwf_inner.ev_b name i hl; omega
    -- WFβ for the body call, and the key §4b env-threading step
    have hwf_alloc : WFβ (.cons x T_a_inner.heap.length env_a)
        (.cons x T_b_inner.heap.length env_b)
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } :=
      ⟨hh_a_alloc, hh_b_alloc, hev_a', hev_b'⟩
    have h_env' : EnvVisβ (.cons x T_a_inner.heap.length env_a)
        (.cons x T_b_inner.heap.length env_b)
        (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) :=
      EnvVisβ_alloc_cons x env_a env_b v_a v_b T_a_inner.heap T_b_inner.heap
        hwf_inner.hv_a hwf_inner.hv_b hwf_inner.ev_a hwf_inner.ev_b
        hv_va hv_vb h_vv_v h_env_inner
    -- IH on body
    obtain ⟨r_b, T_b', h_eval_b_b, h_vv_r, hwf_body, h_he_body, _h_env_body, hv_ra, hv_rb⟩ :=
      ih ptable level body body'
        (.cons x T_a_inner.heap.length env_a) (.cons x T_b_inner.heap.length env_b)
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } r_a T_a'
        hβ_body hwf_alloc h_env' heval
    -- chain the heap evolutions and assemble the outputs
    have h_he_alloc : HeapEvolutionβ T_a_inner T_b_inner
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } :=
      HeapEvolutionβ.from_heapExt hwf_inner.hv_a hwf_inner.hv_b ⟨[v_a], rfl⟩ ⟨[v_b], rfl⟩
    have h_he_chain : HeapEvolutionβ T_a T_b T_a' T_b' :=
      h_he_inner.trans (h_he_alloc.trans h_he_body)
    have hwf_out : WFβ env_a env_b T_a' T_b' :=
      ⟨hwf_body.hv_a, hwf_body.hv_b,
       hwf.ev_a.length_mono h_he_chain.len_a, hwf.ev_b.length_mono h_he_chain.len_b⟩
    have h_env_out : EnvVisβ env_a env_b T_a'.heap T_b'.heap :=
      h_he_chain.envVisβ_preserve env_a env_b hwf.ev_a hwf.ev_b henv
    refine ⟨r_b, T_b', ?_, h_vv_r, hwf_out, h_he_chain, h_env_out, hv_ra, hv_rb⟩
    simp only [eval, h_eval_e_b, TowerState.alloc, Heap.alloc]
    exact h_eval_b_b

/-! ### 6d. The `.ifte` case — branching, non-allocating at the node

The new content here is *cross-side branch agreement*: the condition
values `cv_a` / `cv_b` are `ValVisβ`-related, and `.ifte` branches on
whether the value is `.bool false`; `ValVisβ_bool_false_iff` (the
deferred ground inversion) forces both sides to take the *same* branch.
The value case-bash is localized into `ifteBranch` / `eval_ifte_step`,
keeping the IH-threading proof clean (and shorter than `.letE`: `.ifte`
allocates nothing at its own node). -/

/-- The branch `.ifte` selects on a condition value: `.bool false → e`,
    everything else → `t`. -/
def ifteBranch (cv : Val) (t e : Expr) : Expr :=
  match cv with | .bool false => e | _ => t

theorem ifteBranch_ne {cv : Val} (t e : Expr) (h : cv ≠ .bool false) :
    ifteBranch cv t e = t := by
  cases cv with
  | bool b => cases b with
              | false => exact absurd rfl h
              | true => rfl
  | num _ => rfl
  | nilV => rfl
  | sym _ => rfl
  | prim _ => rfl
  | builtinBaseApply => rfl
  | cons _ _ => rfl
  | closure _ _ _ => rfl

/-- One evaluation step of `.ifte`: once the condition converges to `cv`,
    the whole `.ifte` reduces to evaluating the selected branch. -/
theorem eval_ifte_step (n : Nat) (ptable : PolicyTable) (level : Nat)
    (c t e : Expr) (env : Env) (T T' : TowerState) (cv : Val)
    (hc : eval n ptable level c env T = some (cv, T')) :
    eval (n + 1) ptable level (.ifte c t e) env T
      = eval n ptable level (ifteBranch cv t e) env T' := by
  simp only [eval, hc]
  cases cv with
  | bool b => cases b <;> rfl
  | num _ => rfl
  | nilV => rfl
  | sym _ => rfl
  | prim _ => rfl
  | builtinBaseApply => rfl
  | cons _ _ => rfl
  | closure _ _ _ => rfl

theorem eval_ifte_none (n : Nat) (ptable : PolicyTable) (level : Nat)
    (c t e : Expr) (env : Env) (T : TowerState)
    (hc : eval n ptable level c env T = none) :
    eval (n + 1) ptable level (.ifte c t e) env T = none := by
  simp only [eval, hc]

/-- **Cross-side branch agreement.** `ValVisβ`-related values agree on
    being `.bool false` — so `.ifte` takes the same branch on both sides.
    The ground inversion the branching case needs. -/
theorem ValVisβ_bool_false_iff {a b : Val} {h_a h_b : Heap}
    (h : ValVisβ a b h_a h_b) : a = .bool false ↔ b = .bool false := by
  have h1 := h 1
  cases a <;> cases b <;> simp_all [ValVisβ_aux]

/-- The `.ifte` inductive step on the faithful `FrameβEvalStmt`. -/
theorem frameβ_ifte_eval (n : Nat) (ptable : PolicyTable) (level : Nat)
    (c t e exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmt n)
    (hβ : BetaRel (.ifte c t e) exp_b)
    (hwf : WFβ env_a env_b T_a T_b)
    (henv : EnvVisβ env_a env_b T_a.heap T_b.heap)
    (heval : eval (n + 1) ptable level (.ifte c t e) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFβ env_a env_b T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨c', t', e', rfl, hβ_c, hβ_t, hβ_e⟩ := hβ.ifte_inv
  cases hc : eval n ptable level c env_a T_a with
  | none =>
      rw [eval_ifte_none n ptable level c t e env_a T_a hc] at heval
      simp at heval
  | some pr =>
    obtain ⟨cv_a, T_c_a⟩ := pr
    rw [eval_ifte_step n ptable level c t e env_a T_a T_c_a cv_a hc] at heval
    obtain ⟨cv_b, T_c_b, h_eval_c_b, h_vv_c, hwf_c, h_he_c, h_env_c, _hv_ca, _hv_cb⟩ :=
      ih ptable level c c' env_a env_b T_a T_b cv_a T_c_a hβ_c hwf henv hc
    -- the two sides take the same branch (ValVisβ forces bool-false agreement)
    have hβ_branch : BetaRel (ifteBranch cv_a t e) (ifteBranch cv_b t' e') := by
      by_cases hbf : cv_a = .bool false
      · have hbf_b : cv_b = .bool false := (ValVisβ_bool_false_iff h_vv_c).mp hbf
        subst hbf; subst hbf_b; exact hβ_e
      · have hbf_b : cv_b ≠ .bool false :=
          fun hc' => hbf ((ValVisβ_bool_false_iff h_vv_c).mpr hc')
        rw [ifteBranch_ne t e hbf, ifteBranch_ne t' e' hbf_b]; exact hβ_t
    obtain ⟨r_b, T_b', h_eval_branch_b, h_vv_r, hwf_out, h_he_branch, h_env_out, hv_ra, hv_rb⟩ :=
      ih ptable level (ifteBranch cv_a t e) (ifteBranch cv_b t' e')
        env_a env_b T_c_a T_c_b r_a T_a' hβ_branch hwf_c h_env_c heval
    refine ⟨r_b, T_b', ?_, h_vv_r, hwf_out, h_he_c.trans h_he_branch,
            h_env_out, hv_ra, hv_rb⟩
    rw [eval_ifte_step n ptable level c' t' e' env_b T_b T_c_b cv_b h_eval_c_b]
    exact h_eval_branch_b

/-! ### 6e. The `.seq` case — list-structured, non-allocating at the node

`.seq` is the fiddliest structural former because its `Ctx` (`Ctx.seq
pre c post`) carries `pre`/`post` *lists*. The needed inversions are
list-shaped: `seq_nil_inv` (β can't fire from the empty sequence) and the
cons-style `seq_cons_inv` (β under `.seq (e :: rest)` stays a `.seq`,
β-relating the head and the tail-as-a-sequence — the shape that matches
`eval`'s head/tail recursion). With those, `frameβ_seq_eval` threads the
IH over the head eval (value discarded) and the tail sequence, mirroring
`eval`'s three arms. This completes the gate-free structural fragment. -/

/-- β never fires from the empty sequence. -/
theorem BetaRel.seq_nil_inv {b : Expr} (h : BetaRel (.seq []) b) : b = .seq [] := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      obtain ⟨C, _, _, _, hC, _⟩ := step
      cases C <;> simp [Ctx.plug] at hC

/-- **β under `.seq (e :: rest)` stays a `.seq`**, β-relating the head and
    the tail-as-a-sequence. The cons-style inversion matching `eval`'s
    head/tail recursion. -/
theorem BetaRel.seq_cons_inv {e : Expr} {rest : List Expr} {b : Expr}
    (h : BetaRel (.seq (e :: rest)) b) :
    ∃ e' rest', b = .seq (e' :: rest') ∧ BetaRel e e' ∧
      BetaRel (.seq rest) (.seq rest') := by
  induction h with
  | refl => exact ⟨e, rest, rfl, .refl _, .refl _⟩
  | tail _ step ih =>
      obtain ⟨e', rest', rfl, he, hrest⟩ := ih
      obtain ⟨C, x, body, v, hC, hb⟩ := step
      cases C with
      | seq pre C' post =>
          simp only [Ctx.plug, Expr.seq.injEq] at hC
          cases pre with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hC
              obtain ⟨rfl, hpost⟩ := hC
              refine ⟨C'.plug (.letE x v body), rest', ?_,
                      he.tail ⟨C', x, body, v, rfl, rfl⟩, hrest⟩
              rw [hb]; simp only [Ctx.plug, List.nil_append]; rw [hpost]
          | cons p pre' =>
              simp only [List.cons_append, List.cons.injEq] at hC
              obtain ⟨hp, hrest'⟩ := hC
              refine ⟨e', pre' ++ C'.plug (.letE x v body) :: post, ?_, he, ?_⟩
              · rw [hb]; simp only [Ctx.plug, List.cons_append]; rw [hp]
              · rw [hrest'] at hrest
                exact hrest.tail
                  ⟨.seq pre' C' post, x, body, v, by simp [Ctx.plug], by simp [Ctx.plug]⟩
      | _ => simp [Ctx.plug] at hC

/-- One evaluation step of a ≥2-element sequence: evaluate the head
    (discarding its value, keeping its state), then continue with the
    tail sequence. -/
theorem eval_seq_cons_step (n : Nat) (ptable : PolicyTable) (level : Nat)
    (e f : Expr) (rest2 : List Expr) (env : Env) (T T' : TowerState) (v : Val)
    (hv : eval n ptable level e env T = some (v, T')) :
    eval (n + 1) ptable level (.seq (e :: f :: rest2)) env T
      = eval n ptable level (.seq (f :: rest2)) env T' := by
  simp only [eval, hv]

theorem eval_seq_cons_none (n : Nat) (ptable : PolicyTable) (level : Nat)
    (e f : Expr) (rest2 : List Expr) (env : Env) (T : TowerState)
    (hv : eval n ptable level e env T = none) :
    eval (n + 1) ptable level (.seq (e :: f :: rest2)) env T = none := by
  simp only [eval, hv]

/-- The `.seq` inductive step on the faithful `FrameβEvalStmt`. -/
theorem frameβ_seq_eval (n : Nat) (ptable : PolicyTable) (level : Nat)
    (exps : List Expr) (exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmt n)
    (hβ : BetaRel (.seq exps) exp_b)
    (hwf : WFβ env_a env_b T_a T_b)
    (henv : EnvVisβ env_a env_b T_a.heap T_b.heap)
    (heval : eval (n + 1) ptable level (.seq exps) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFβ env_a env_b T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  cases exps with
  | nil =>
      have hb := hβ.seq_nil_inv; subst hb
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, ht⟩ := heval; subst hr; subst ht
      exact ⟨.nilV, T_b, by simp only [eval], fun m => by cases m <;> simp [ValVisβ_aux],
             hwf, HeapEvolutionβ.refl _ _, henv, trivial, trivial⟩
  | cons e rest =>
      cases rest with
      | nil =>
          -- singleton `.seq [e]` : evaluates `e` directly
          obtain ⟨e', rest', rfl, hβ_e, hβ_rest⟩ := hβ.seq_cons_inv
          have hr : rest' = [] := by
            have := hβ_rest.seq_nil_inv; exact Expr.seq.inj this
          subst hr
          simp only [eval] at heval
          obtain ⟨r_b, T_b', h_eval_e_b, h_vv_r, hwf_out, h_he, h_env_out, hv_ra, hv_rb⟩ :=
            ih ptable level e e' env_a env_b T_a T_b r_a T_a' hβ_e hwf henv heval
          refine ⟨r_b, T_b', ?_, h_vv_r, hwf_out, h_he, h_env_out, hv_ra, hv_rb⟩
          simp only [eval]; exact h_eval_e_b
      | cons f rest2 =>
          -- `.seq (e :: f :: rest2)` : head then tail-sequence
          obtain ⟨e', rest', rfl, hβ_e, hβ_rest⟩ := hβ.seq_cons_inv
          obtain ⟨f', rest2', hr'⟩ : ∃ f' rest2', rest' = f' :: rest2' := by
            obtain ⟨f', rest2', hb_eq, _, _⟩ := hβ_rest.seq_cons_inv
            exact ⟨f', rest2', Expr.seq.inj hb_eq⟩
          subst hr'
          cases hee : eval n ptable level e env_a T_a with
          | none =>
              rw [eval_seq_cons_none n ptable level e f rest2 env_a T_a hee] at heval
              simp at heval
          | some pr =>
              obtain ⟨v_a, T_e_a⟩ := pr
              rw [eval_seq_cons_step n ptable level e f rest2 env_a T_a T_e_a v_a hee] at heval
              obtain ⟨v_b, T_e_b, h_eval_e_b, _h_vv_v, hwf_e, h_he_e, h_env_e, _, _⟩ :=
                ih ptable level e e' env_a env_b T_a T_b v_a T_e_a hβ_e hwf henv hee
              obtain ⟨r_b, T_b', h_eval_rest_b, h_vv_r, hwf_out, h_he_rest,
                      h_env_out, hv_ra, hv_rb⟩ :=
                ih ptable level (.seq (f :: rest2)) (.seq (f' :: rest2'))
                  env_a env_b T_e_a T_e_b r_a T_a' hβ_rest hwf_e h_env_e heval
              refine ⟨r_b, T_b', ?_, h_vv_r, hwf_out, h_he_e.trans h_he_rest,
                      h_env_out, hv_ra, hv_rb⟩
              rw [eval_seq_cons_step n ptable level e' f' rest2' env_b T_b T_e_b v_b h_eval_e_b]
              exact h_eval_rest_b

/-! ### 6f. The `evalList` clause — argument-list threading, gate-free

`evalList` is the argument-list traversal `.app` / `.primApp` run before
applying. It is the last gate-free structural clause, and the bridge into
the elimination side: `app_inv` (§4d) supplies the `BetaRelList` on the
arguments, and this clause carries it to `ListValVisβ`-related value lists.

Unlike the single-expression cases, `evalList` recurses on *two* clauses —
`eval n` on the head, `evalList n` on the tail — so as a standalone lemma
it takes **both** induction hypotheses the `frame_tower` mutual induction
supplies at its own `evalList` node (`Frame.lean:2244`): the eval clause
`FrameβEvalStmt n` and the evalList clause `FrameβEvalListStmt n`. The proof
is a faithful β-port: `BetaRelList` heads/tails the shared list, and the
`ListValVis` / `ValVis` / `HeapEvolution` machinery becomes the β-relations.
No gate premise — like the other structural cases, `evalList` applies
nothing. -/

/-- Pointwise `ValVisβ` on value lists — the result side matching
    `BetaRelList`. Mirror of `Bisim.ListValVis` (`ValVis ↦ ValVisβ`); the
    `ListValVisβ` the full mutual statement's `evalList` clause produces. -/
def ListValVisβ : List Val → List Val → Heap → Heap → Prop
  | [],      [],      _,   _   => True
  | x :: xs, y :: ys, h_a, h_b => ValVisβ x y h_a h_b ∧ ListValVisβ xs ys h_a h_b
  | _,       _,       _,   _   => False

/-- `ListValVisβ` preserved under heap extension (pointwise `ValVisβ_extends`).
    Mirror of `Bisim.ListValVis_extends`. -/
theorem ListValVisβ_extends : ∀ {xs ys : List Val} {h_a h_b ext_a ext_b : Heap},
    HeapValid h_a → HeapValid h_b →
    ListValValid xs h_a → ListValValid ys h_b →
    ListValVisβ xs ys h_a h_b →
    ListValVisβ xs ys (h_a ++ ext_a) (h_b ++ ext_b)
  | [],      [],      _, _, _, _, _, _, _, _, _ => trivial
  | [],      _ :: _,  _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  [],      _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, _, _, hh_a, hh_b, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨ValVisβ_extends _ _ _ _ _ _ hh_a hh_b hv_a.1 hv_b.1 h_head,
       ListValVisβ_extends hh_a hh_b hv_a.2 hv_b.2 h_tail⟩

/-- The `evalList` clause, β-analog of `FrameStmtT`'s second conjunct
    (`Frame.lean:912`): `ListValVis ↦ ListValVisβ`, the shared `exps`
    replaced by a `BetaRelList` pair, full output invariant set kept,
    gate premises absent. -/
def FrameβEvalListStmt (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exps_a exps_b : List Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (rs_a : List Val) (T_a' : TowerState),
    BetaRelList exps_a exps_b →
    WFβ env_a env_b T_a T_b →
    EnvVisβ env_a env_b T_a.heap T_b.heap →
    evalList n ptable level exps_a env_a T_a = some (rs_a, T_a') →
    ∃ rs_b T_b',
      evalList n ptable level exps_b env_b T_b = some (rs_b, T_b') ∧
      ListValVisβ rs_a rs_b T_a'.heap T_b'.heap ∧
      WFβ env_a env_b T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      EnvVisβ env_a env_b T_a'.heap T_b'.heap ∧
      ListValValid rs_a T_a'.heap ∧ ListValValid rs_b T_b'.heap

/-- **The `evalList` inductive step.** From the eval clause and the evalList
    clause at fuel `n`, the evalList clause at fuel `n+1` — exactly the
    `frame_tower` mutual induction's `evalList` node, faithfully β-ported.
    The head is threaded by the eval IH, the tail by the evalList IH; the
    head's `ValVisβ` / `ValValid` are lifted across the tail's
    `HeapEvolutionβ` (`valVisβ_preserve` / `length_mono`). -/
theorem frameβ_evalList_eval (n : Nat)
    (ih_eval : FrameβEvalStmt n) (ih_list : FrameβEvalListStmt n) :
    FrameβEvalListStmt (n + 1) := by
  intro ptable level exps_a exps_b env_a env_b T_a T_b rs_a T_a'
        hβ hwf henv heval
  cases hβ with
  | nil =>
      simp only [evalList, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
      exact ⟨[], T_b, by simp [evalList], trivial, hwf,
             HeapEvolutionβ.refl _ _, henv, trivial, trivial⟩
  | cons hβ_e hβ_rest =>
      rename_i e e' rest rest'
      simp only [evalList] at heval
      cases he : eval n ptable level e env_a T_a with
      | none => rw [he] at heval; simp at heval
      | some pr =>
          obtain ⟨v_a, T_a_inner⟩ := pr
          rw [he] at heval
          simp only at heval
          cases hrest : evalList n ptable level rest env_a T_a_inner with
          | none => rw [hrest] at heval; simp at heval
          | some pr2 =>
              obtain ⟨vs_a, T_a_inner2⟩ := pr2
              rw [hrest] at heval
              simp only [Option.some.injEq, Prod.mk.injEq] at heval
              obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
              -- IH on head `e`
              obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, hwf_inner,
                      h_he_inner, h_env_inner, hv_va, hv_vb⟩ :=
                ih_eval ptable level e e' env_a env_b T_a T_b v_a T_a_inner
                  hβ_e hwf henv he
              -- IH on tail `rest`
              obtain ⟨vs_b, T_b_inner2, h_eval_rest_b, h_lvv, hwf_inner2,
                      h_he_inner2, h_env_inner2, hv_vsa, hv_vsb⟩ :=
                ih_list ptable level rest rest' env_a env_b T_a_inner T_b_inner
                  vs_a T_a_inner2 hβ_rest hwf_inner h_env_inner hrest
              -- lift the head's value relation/validity across the tail's evolution
              have h_vv_v' : ValVisβ v_a v_b T_a_inner2.heap T_b_inner2.heap :=
                h_he_inner2.valVisβ_preserve v_a v_b hv_va hv_vb h_vv_v
              have hv_va' : ValValid v_a T_a_inner2.heap :=
                ValValid.length_mono v_a hv_va h_he_inner2.len_a
              have hv_vb' : ValValid v_b T_b_inner2.heap :=
                ValValid.length_mono v_b hv_vb h_he_inner2.len_b
              have h_he_chain : HeapEvolutionβ T_a T_b T_a_inner2 T_b_inner2 :=
                h_he_inner.trans h_he_inner2
              refine ⟨v_b :: vs_b, T_b_inner2, ?_, ⟨h_vv_v', h_lvv⟩,
                      hwf_inner2, h_he_chain, h_env_inner2,
                      ⟨hv_va', hv_vsa⟩, ⟨hv_vb', hv_vsb⟩⟩
              simp [evalList, h_eval_e_b, h_eval_rest_b]

/-! ### 6g. The closure-apply allocation chain — gate-free

`applyDirect`'s closure case binds the arguments by folding `allocStep`
over `args.zip ps`, *then* evaluates the body. The fold is the last piece
of allocation plumbing before the (gated) body eval: it must carry
`EnvVisβ` from the captured environments to the cons-extended call
environments, across heaps whose contents — and lengths — diverge.

`frame_tower` uses `allocStep_chain_aligned` (`Bisim.lean:2761`), which
proves the two result envs **Lean-equal** (same captured `cenv`, equal
heap lengths). β breaks both. The faithful relational analog is
`Bisim.alloc_chain_bisim` (`Bisim.lean:2824`), which already relaxes the
result to `EnvVis`-relatedness; this is its verbatim β-port (`EnvVis ↦
EnvVisβ`, `ValVis ↦ ValVisβ`, `ListValVis ↦ ListValVisβ`, and the §4 /
§6f extension lemmas in place of the `_weak` ones). Every `HeapValid` /
`EnvValid` step is body-agnostic and identical. This is the multi-argument
generalization of `EnvVisβ_alloc_cons` (§4b), and the last gate-free step
the closure-apply needs. -/
theorem EnvVisβ_allocStep_chain
    (xs_a : List Val) :
    ∀ (xs_b : List Val) (ps : List String) (cenv_a cenv_b : Env) (h_a h_b : Heap),
    xs_a.length = ps.length → xs_b.length = ps.length →
    ListValVisβ xs_a xs_b h_a h_b →
    ListValValid xs_a h_a → ListValValid xs_b h_b →
    HeapValid h_a → HeapValid h_b →
    EnvValid cenv_a h_a → EnvValid cenv_b h_b →
    EnvVisβ cenv_a cenv_b h_a h_b →
    let result_a := xs_a.zip ps |>.foldl allocStep (h_a, cenv_a)
    let result_b := xs_b.zip ps |>.foldl allocStep (h_b, cenv_b)
    HeapValid result_a.1 ∧ HeapValid result_b.1 ∧
    EnvValid result_a.2 result_a.1 ∧ EnvValid result_b.2 result_b.1 ∧
    EnvVisβ result_a.2 result_b.2 result_a.1 result_b.1 ∧
    (∃ ext, result_a.1 = h_a ++ ext) ∧
    (∃ ext, result_b.1 = h_b ++ ext) := by
  induction xs_a with
  | nil =>
      intro xs_b ps cenv_a cenv_b h_a h_b hlen_a hlen_b h_lvv hv_xs_a hv_xs_b
            hh_a hh_b hev_a hev_b h_env
      simp only [List.length_nil] at hlen_a
      have hps_nil : ps = [] := List.length_eq_zero_iff.mp hlen_a.symm
      subst hps_nil
      simp only [List.length_nil] at hlen_b
      have hxs_b_nil : xs_b = [] := List.length_eq_zero_iff.mp hlen_b
      subst hxs_b_nil
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show HeapValid (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
        simp [List.foldl]; exact hh_a
      · show HeapValid (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact hh_b
      · show EnvValid (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).2
                     (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
        simp [List.foldl]; exact hev_a
      · show EnvValid (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).2
                     (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact hev_b
      · show EnvVisβ (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).2
                     (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).2
                     (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
                     (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact h_env
      · show ∃ ext, (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
          = h_a ++ ext
        simp [List.foldl]
      · show ∃ ext, (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
          = h_b ++ ext
        simp [List.foldl]
  | cons a_a rest_a ih =>
      intro xs_b ps cenv_a cenv_b h_a h_b hlen_a hlen_b h_lvv hv_xs_a hv_xs_b
            hh_a hh_b hev_a hev_b h_env
      cases ps with
      | nil =>
          exfalso
          simp only [List.length_cons, List.length_nil] at hlen_a
          omega
      | cons p rest_p =>
          cases xs_b with
          | nil =>
              exfalso
              simp only [List.length_nil, List.length_cons] at hlen_b
              omega
          | cons a_b rest_b =>
              simp only [List.length_cons] at hlen_a hlen_b
              have hlen_a' : rest_a.length = rest_p.length := by omega
              have hlen_b' : rest_b.length = rest_p.length := by omega
              obtain ⟨h_vv_a, h_lvv_rest⟩ := h_lvv
              obtain ⟨hv_a_a, hv_rest_a⟩ := hv_xs_a
              obtain ⟨hv_a_b, hv_rest_b⟩ := hv_xs_b
              show
                let result_a := rest_a.zip rest_p |>.foldl allocStep
                  (h_a ++ [a_a], .cons p h_a.length cenv_a)
                let result_b := rest_b.zip rest_p |>.foldl allocStep
                  (h_b ++ [a_b], .cons p h_b.length cenv_b)
                HeapValid result_a.1 ∧ HeapValid result_b.1 ∧
                EnvValid result_a.2 result_a.1 ∧ EnvValid result_b.2 result_b.1 ∧
                EnvVisβ result_a.2 result_b.2 result_a.1 result_b.1 ∧
                (∃ ext, result_a.1 = h_a ++ ext) ∧
                (∃ ext, result_b.1 = h_b ++ ext)
              have hh_a' : HeapValid (h_a ++ [a_a]) := by
                intro i v hp
                by_cases h_lt : i < h_a.length
                · have hp_old : h_a[i]? = some v := by
                    rw [← getElem?_prefix h_a [a_a] i h_lt]; exact hp
                  exact ValValid.heap_extends v (hh_a i v hp_old) ⟨[a_a], rfl⟩
                · have h_eq : i = h_a.length := by
                    have h_le : i < (h_a ++ [a_a]).length := by
                      rw [List.getElem?_eq_some_iff] at hp
                      obtain ⟨h, _⟩ := hp; exact h
                    simp [List.length_append] at h_le; omega
                  subst h_eq
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hp
                  simp at hp
                  subst hp
                  exact ValValid.heap_extends a_a hv_a_a ⟨[a_a], rfl⟩
              have hh_b' : HeapValid (h_b ++ [a_b]) := by
                intro i v hp
                by_cases h_lt : i < h_b.length
                · have hp_old : h_b[i]? = some v := by
                    rw [← getElem?_prefix h_b [a_b] i h_lt]; exact hp
                  exact ValValid.heap_extends v (hh_b i v hp_old) ⟨[a_b], rfl⟩
                · have h_eq : i = h_b.length := by
                    have h_le : i < (h_b ++ [a_b]).length := by
                      rw [List.getElem?_eq_some_iff] at hp
                      obtain ⟨h, _⟩ := hp; exact h
                    simp [List.length_append] at h_le; omega
                  subst h_eq
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hp
                  simp at hp
                  subst hp
                  exact ValValid.heap_extends a_b hv_a_b ⟨[a_b], rfl⟩
              have hev_a' : EnvValid (.cons p h_a.length cenv_a) (h_a ++ [a_a]) := by
                intro name i hl
                simp only [List.length_append, List.length_singleton]
                simp only [Env.lookup] at hl
                by_cases h_eq : p = name
                · subst h_eq
                  simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                  omega
                · have h_neq : (p == name) = false := by
                    rw [beq_eq_false_iff_ne]; exact h_eq
                  simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                  have := hev_a name i hl
                  omega
              have hev_b' : EnvValid (.cons p h_b.length cenv_b) (h_b ++ [a_b]) := by
                intro name i hl
                simp only [List.length_append, List.length_singleton]
                simp only [Env.lookup] at hl
                by_cases h_eq : p = name
                · subst h_eq
                  simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                  omega
                · have h_neq : (p == name) = false := by
                    rw [beq_eq_false_iff_ne]; exact h_eq
                  simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                  have := hev_b name i hl
                  omega
              have hl_a : (h_a ++ [a_a])[h_a.length]? = some a_a := by
                rw [List.getElem?_append_right (Nat.le_refl _)]; simp
              have hl_b : (h_b ++ [a_b])[h_b.length]? = some a_b := by
                rw [List.getElem?_append_right (Nat.le_refl _)]; simp
              have h_vv_a' : ValVisβ a_a a_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                ValVisβ_extends a_a a_b h_a h_b [a_a] [a_b] hh_a hh_b hv_a_a hv_a_b h_vv_a
              have h_env_lifted : EnvVisβ cenv_a cenv_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                EnvVisβ_extends cenv_a cenv_b h_a h_b [a_a] [a_b]
                  hh_a hh_b hev_a hev_b h_env
              have h_env' : EnvVisβ (.cons p h_a.length cenv_a) (.cons p h_b.length cenv_b)
                  (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                EnvVisβ_cons p h_a.length h_b.length cenv_a cenv_b
                  (h_a ++ [a_a]) (h_b ++ [a_b]) a_a a_b hl_a hl_b h_vv_a' h_env_lifted
              have h_lvv_rest' : ListValVisβ rest_a rest_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                ListValVisβ_extends hh_a hh_b hv_rest_a hv_rest_b h_lvv_rest
              have hv_rest_a' : ListValValid rest_a (h_a ++ [a_a]) :=
                ListValValid.heap_extends hv_rest_a ⟨[a_a], rfl⟩
              have hv_rest_b' : ListValValid rest_b (h_b ++ [a_b]) :=
                ListValValid.heap_extends hv_rest_b ⟨[a_b], rfl⟩
              obtain ⟨hh_ra, hh_rb, hev_ra, hev_rb, h_env_r, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
                ih rest_b rest_p (.cons p h_a.length cenv_a) (.cons p h_b.length cenv_b)
                  (h_a ++ [a_a]) (h_b ++ [a_b])
                  hlen_a' hlen_b' h_lvv_rest' hv_rest_a' hv_rest_b'
                  hh_a' hh_b' hev_a' hev_b' h_env'
              refine ⟨hh_ra, hh_rb, hev_ra, hev_rb, h_env_r, ?_, ?_⟩
              · exact ⟨[a_a] ++ ext_a, by rw [hex_a, List.append_assoc]⟩
              · exact ⟨[a_b] ++ ext_b, by rw [hex_b, List.append_assoc]⟩

end LeanBlack
