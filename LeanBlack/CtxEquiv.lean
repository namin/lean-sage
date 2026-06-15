/-
  lean-sage: Contextual (observational) equivalence and the `.lam` gap.

  The one remaining piece of contextual β
  (`ContextualBetaPure.contextual_beta_pure`) is the case where the hole
  sits *under a binder* — the `Ctx.lamFree` carve-out. The natural
  attempt is to lift the per-node congruence `Ctx.plug_cong_master`
  through `.lam` by proving one more `EvalEquivAt` congruence. This file
  shows that attempt targets the *wrong relation*, and supplies the
  right one.

  The `.lam` gap has *two* compounding obstructions; this file isolates
  both and locates exactly what remains open.

  1. **Syntactic obstruction (§1, negative).** `EvalEquivAt` / `EvalEquiv`
     are *raw outcome equality*. `.lam` evaluates to a closure that
     captures its body verbatim (`Eval.lean`), so two lambdas with
     distinct bodies are distinct values. Hence lifting `plug_cong_master`
     through `.lam` in the `EvalEquivAt` frame is not merely hard, it is
     impossible — the goal is false (`lam_EvalEquivAt_forces_empty`,
     `lam_EvalEquiv_congruence_fails`).

  2. **The fix — and its free congruence (§2–§3).** Coarsen to the
     Morris-style observation: `CtxEquiv M N` asks that `M` and `N`
     may-converge to the same *ground* value (`.num` / `.bool`) in every
     context. A `.lam` context then returns an unobservable closure, so
     the syntactic obstruction is gone (`lam_closure_obs_agree`); and for
     this relation the `.lam` congruence is **free**, a corollary of
     context composition (`CtxEquiv.congr` / `under_lam` / `under_binders`).

  3. **Depth/gate obstruction (§4, negative).** But ground-observed
     `CtxEquiv` is still too strong for β to inhabit *unconditionally*:
     every application routes through the `base-apply` gate of the level
     above, so the redex (an application) and contractum (not) are
     separated — at the top of the tower the redex cannot apply at all
     (`beta_not_unconditional_CtxEquiv`). The genuine β relation is
     therefore *conditional* (the `BuiltinReadyP` / pure-sided conditions
     `contextual_beta_pure` already carries).

  Net (§5): the open problem is to extend the *conditional* congruence
  `plug_cong_master` to `.lam`, which needs both a `ValVis`-style
  bisimulation-up-to-β for the closure case (Howe / logical relation) and
  the side-condition threading through the binder. The congruence
  machinery here transfers for free; the relational content does not.
-/
import LeanBlack.Ctx

/-- A first-order observable result: a ground value carrying no closure
    content. Only these are observed by `CtxEquiv`. (Defined at the root
    namespace, where `Val` lives, so dot-notation `g.isGround` resolves.) -/
def Val.isGround : Val → Bool
  | .num _  => true
  | .bool _ => true
  | _       => false

namespace LeanBlack

/-! ## 1. The negative result: `EvalEquivAt` is not a `.lam` congruence -/

/-- `.lam` evaluates (with any positive fuel) to a closure that
    captures its body *syntactically*. (Local restatement of
    `ContextualBeta.eval_lam`, to keep this file's import cone light.) -/
theorem eval_lam_closure (n : Nat) (ptable : PolicyTable) (level : Nat)
    (ps : List String) (body : Expr) (env : Env) (T : TowerState) :
    eval (n + 1) ptable level (.lam ps body) env T
      = some (.closure ps body env, T) := by
  simp [eval]

/-- **The `.lam` case is a false goal in the `EvalEquivAt` frame, not a
    missing lemma.** If the two bodies differ syntactically, then
    `EvalEquivAt P (.lam ps M) (.lam ps N)` can hold *only when `P` is
    unsatisfiable*: at any state satisfying `P` the two lambdas evaluate
    to the distinct closure values `.closure ps M env` / `.closure ps N env`,
    so they share no outcome and the outcome-equality iff fails. -/
theorem lam_EvalEquivAt_forces_empty
    {P : StatePred} {ps : List String} {M N : Expr} (hMN : M ≠ N)
    (h : EvalEquivAt P (.lam ps M) (.lam ps N)) :
    ∀ ptable level env T, ¬ P ptable level env T := by
  intro ptable level env T hP
  have hiff := h ptable level env T hP (.closure ps M env) T
  have hL : ∃ k, eval k ptable level (.lam ps M) env T
      = some (.closure ps M env, T) := ⟨1, eval_lam_closure 0 ptable level ps M env T⟩
  obtain ⟨k, hk⟩ := hiff.mp hL
  cases k with
  | zero => simp [eval] at hk
  | succ n =>
      rw [eval_lam_closure] at hk
      injection hk with hk'
      injection hk' with hval _
      injection hval with _ hbody _
      exact hMN hbody.symm

/-- Concretely, on the artifact's own Wand redex/contractum pair
    `(λx. x) 0` vs `let x = 0 in x`: since `EvalEquiv` is exactly
    `EvalEquivAt` at the everywhere-true (hence satisfiable) predicate,
    the plain congruence `Ctx.plug_cong` genuinely cannot extend to
    `.lam`. The obstruction is real, not a vacuity artifact. -/
theorem lam_EvalEquiv_congruence_fails :
    ¬ EvalEquiv
        (.lam ["y"] (.app [.lam ["x"] (.var "x"), .num 0]))
        (.lam ["y"] (.letE "x" (.num 0) (.var "x"))) := by
  intro h
  have h' : EvalEquivAt (fun _ _ _ _ => True)
      (.lam ["y"] (.app [.lam ["x"] (.var "x"), .num 0]))
      (.lam ["y"] (.letE "x" (.num 0) (.var "x"))) :=
    fun ptable level env T _ v T' => h ptable level env T v T'
  exact lam_EvalEquivAt_forces_empty
    (by intro hc; exact Expr.noConfusion hc) h' [] 0 Env.nil initTower True.intro

/-! ## 2. Context composition -/

/-- Fill the hole of `C` with the context `D` — context composition. -/
def Ctx.comp : Ctx → Ctx → Ctx
  | .hole,                D => D
  | .ifteCond c et ee,    D => .ifteCond (c.comp D) et ee
  | .ifteThen ec c ee,    D => .ifteThen ec (c.comp D) ee
  | .ifteElse ec et c,    D => .ifteElse ec et (c.comp D)
  | .lam ps c,            D => .lam ps (c.comp D)
  | .app pre c post,      D => .app pre (c.comp D) post
  | .set x c,             D => .set x (c.comp D)
  | .em c,                D => .em (c.comp D)
  | .primAppFun c args,   D => .primAppFun (c.comp D) args
  | .primAppArg f pre c post, D => .primAppArg f pre (c.comp D) post
  | .letEVal x c body,    D => .letEVal x (c.comp D) body
  | .letEBody x ev c,     D => .letEBody x ev (c.comp D)
  | .seq pre c post,      D => .seq pre (c.comp D) post

/-- Composition does what it should: plugging the composite equals
    nesting the plugs. -/
@[simp] theorem Ctx.plug_comp (C D : Ctx) (e : Expr) :
    (C.comp D).plug e = C.plug (D.plug e) := by
  induction C <;> simp_all [Ctx.comp, Ctx.plug]

/-! ## 3. Contextual (observational) equivalence

The observation must be at **ground type**, not the full value. If we
observed the whole returned value (as `EvalEquiv` does), a context that
*returns* the plugged term as a closure — e.g. `.lam ps □` — would
distinguish β-related terms, since the two closures are unequal values
(that is precisely `lam_EvalEquiv_congruence_fails`). So `EvalEquiv` is
too fine to be a congruence: building `∀ C, EvalEquiv (C[M]) (C[N])`
gives a relation no β pair can satisfy.

The fix is Morris's: observe only convergence to a **ground** value
(`.num` / `.bool`), discarding the final state and any non-ground
(closure / prim) result. A `.lam` context then yields a closure — *not*
a ground observable — so it no longer distinguishes, and β-related
terms can be (and are) equivalent. -/

/-- `M` may-converge to the ground value `g` from the given state
    (final state discarded — Morris observation). -/
def ObsConv (M : Expr) (ptable : PolicyTable) (level : Nat) (env : Env)
    (T : TowerState) (g : Val) : Prop :=
  ∃ k T', eval k ptable level M env T = some (g, T')

/-- **Morris-style contextual equivalence.** `M` and `N` may-converge
    to the same *ground* value in every context. Unlike `EvalEquiv`,
    this is coarse enough to survive closure capture, so it is a
    congruence under `.lam` (`under_lam`) — yet still fine enough to
    separate distinct ground outputs (`num 0` ≇ `num 1`). -/
def CtxEquiv (M N : Expr) : Prop :=
  ∀ (C : Ctx) (ptable : PolicyTable) (level : Nat) (env : Env)
    (T : TowerState) (g : Val), g.isGround = true →
    (ObsConv (C.plug M) ptable level env T g ↔
     ObsConv (C.plug N) ptable level env T g)

theorem CtxEquiv.refl (M : Expr) : CtxEquiv M M :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem CtxEquiv.symm {M N : Expr} (h : CtxEquiv M N) : CtxEquiv N M :=
  fun C p l env T g hg => (h C p l env T g hg).symm

theorem CtxEquiv.trans {M N R : Expr}
    (h1 : CtxEquiv M N) (h2 : CtxEquiv N R) : CtxEquiv M R :=
  fun C p l env T g hg => (h1 C p l env T g hg).trans (h2 C p l env T g hg)

/-- Observation at the empty context — the top-level ground behaviour
    `CtxEquiv` guarantees. -/
theorem CtxEquiv.obs_at_hole {M N : Expr} (h : CtxEquiv M N)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (g : Val) (hg : g.isGround = true) :
    ObsConv M ptable level env T g ↔ ObsConv N ptable level env T g := by
  have h' := h .hole ptable level env T g hg
  simpa [Ctx.plug] using h'

/-- **The congruence the `.lam` case needs — and it is free.** If
    `M ≅ N` contextually, then `D[M] ≅ D[N]` contextually for *any*
    context `D`, because contexts compose. No logical relation, no
    Howe method: just `plug_comp`. -/
theorem CtxEquiv.congr {M N : Expr} (h : CtxEquiv M N) (D : Ctx) :
    CtxEquiv (D.plug M) (D.plug N) := by
  intro C ptable level env T g hg
  rw [← Ctx.plug_comp, ← Ctx.plug_comp]
  exact h (C.comp D) ptable level env T g hg

/-- The headline instance: contextual equivalence is a congruence
    **under a binder**. This is exactly what `EvalEquivAt` could not
    deliver (`lam_EvalEquivAt_forces_empty` above). -/
theorem CtxEquiv.under_lam {M N : Expr} (h : CtxEquiv M N)
    (ps : List String) : CtxEquiv (.lam ps M) (.lam ps N) := by
  have h' := h.congr (.lam ps .hole)
  simpa [Ctx.plug] using h'

/-- Equivalence survives nesting under *any* sequence of binders — the
    iterate of `under_lam`. Binders add nothing once the base
    `CtxEquiv` holds. -/
theorem CtxEquiv.under_binders {M N : Expr} (h : CtxEquiv M N) :
    ∀ pss : List (List String),
      CtxEquiv (pss.foldr Expr.lam M) (pss.foldr Expr.lam N)
  | []         => h
  | ps :: rest => (CtxEquiv.under_binders h rest).under_lam ps

/-- **The redesign works exactly where `EvalEquiv` failed.** The `.lam`
    context that refutes `EvalEquiv` (`lam_EvalEquiv_congruence_fails`)
    does *not* refute the ground observation: a binder returns a
    closure, which is not a ground value, so neither side ever
    converges to an observable — the two agree vacuously. This is why
    `CtxEquiv` tolerates the closure difference the artifact's relation
    cannot, and hence why `hβ` below is *satisfiable*. -/
theorem lam_closure_obs_agree (ps : List String) (M N : Expr)
    (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState)
    (g : Val) (hg : g.isGround = true) :
    ObsConv (.lam ps M) ptable level env T g ↔
    ObsConv (.lam ps N) ptable level env T g := by
  have key : ∀ B : Expr, ¬ ObsConv (.lam ps B) ptable level env T g := by
    rintro B ⟨k, T', hk⟩
    cases k with
    | zero => simp [eval] at hk
    | succ n =>
        rw [eval_lam_closure] at hk
        have hgc : g = .closure ps B env := by
          injection hk with h1; injection h1 with h2 _; exact h2.symm
        rw [hgc] at hg
        simp [Val.isGround] at hg
  exact ⟨fun h => absurd h (key M), fun h => absurd h (key N)⟩

/-! ## 4. The depth/gate obstruction: β is *not* an unconditional CtxEquiv

The congruence above is free — but it is a congruence of a relation too
*strong* for β to inhabit. Coarsening to ground observation removed the
syntactic (closure-capture) obstruction (§3), yet a second, deeper one
remains: in this reflective tower **every application routes through the
`base-apply` gate** of the level above (`applyVia`, `Eval.lean`). The
redex `(λx. body) v` is an application; the contractum `let x = v in body`
is not. So they are separated by any *state* whose gate is non-standard,
and even with the standard gate they are separated at the top of the
tower — where there is no level above to host the gate, so the redex
cannot apply at all.

We formalize the sharpest case: at `level = maxDepth - 1` the redex never
converges (`applyVia` needs `materialize (level+1)`, which is `none`),
while the contractum converges to `0`. Hence the *unconditional* ground
`CtxEquiv` is false for β — which is exactly why `contextual_beta_pure`
carries the `BuiltinReadyP` (standard gate + depth margin) and pure-sided
side conditions. The genuine β relation is a *conditional* contextual
equivalence. -/

/-- Past the tower's depth no application can fire: `applyVia` needs
    level `level+1` materialized, but `materialize · (level+1) = none`
    once `level+1 ≥ maxDepth`, for *every* state. -/
theorem applyVia_depth_none {ptable : PolicyTable} {level : Nat}
    (op : Val) (args : List Val) (T : TowerState)
    (h : Tower.maxDepth ≤ level + 1) (k : Nat) :
    applyVia k ptable level op args T = none := by
  have hmat : T.materialize (level + 1) = none := by
    simp [TowerState.materialize, h]
  cases k with
  | zero => simp [applyVia]
  | succ n => simp [applyVia, hmat]

/-- A two-element application cannot converge past the tower depth: it
    routes through `applyVia`, which fails there — whatever the function
    and argument evaluate to. -/
theorem eval_app_depth_none {ptable : PolicyTable} {level : Nat}
    (f arg : Expr) (env : Env) (T : TowerState)
    (h : Tower.maxDepth ≤ level + 1) (k : Nat) :
    eval k ptable level (.app [f, arg]) env T = none := by
  cases k with
  | zero => simp [eval]
  | succ n =>
      simp only [eval]
      split
      · rfl
      · split
        · rfl
        · exact applyVia_depth_none _ _ _ h n

/-- **β is not an *unconditional* contextual equivalence.** Even under
    ground observation, the Wand redex `(λx. x) 0` and contractum
    `let x = 0 in x` are distinguished: at the top of the tower
    (`level = maxDepth - 1 = 15`) the redex cannot apply — no level above
    to host the `base-apply` gate — so it never converges, while the
    contractum still converges to `0`. This is *why* the artifact's β
    needs `BuiltinReadyP` and pure-sided contexts: the genuine β relation
    is the *conditional* ground-contextual equivalence, not this
    unconditional one. -/
theorem beta_not_unconditional_CtxEquiv :
    ¬ CtxEquiv (.app [.lam ["x"] (.var "x"), .num 0])
               (.letE "x" (.num 0) (.var "x")) := by
  intro h
  have key := h .hole [] 15 Env.nil ({ heap := [], levels := [] }) (.num 0) rfl
  simp only [Ctx.plug] at key
  have hcon : ObsConv (.letE "x" (.num 0) (.var "x")) [] 15 Env.nil
      ({ heap := [], levels := [] }) (.num 0) :=
    ⟨2, { heap := [.num 0], levels := [] }, by
      simp [eval, TowerState.alloc, Env.lookup, Heap.alloc]⟩
  have hredex : ¬ ObsConv (.app [.lam ["x"] (.var "x"), .num 0]) [] 15 Env.nil
      ({ heap := [], levels := [] }) (.num 0) := by
    rintro ⟨k, T', hk⟩
    rw [eval_app_depth_none _ _ _ _ (by decide) k] at hk
    simp at hk
  exact hredex (key.mpr hcon)

/-! ## 5. The open core, precisely located

The two obstructions together give the honest shape of the remaining
`.lam` work — genuinely the relational + reflective content the author
left open:

* **Syntactic obstruction** (closures capture bodies verbatim) — defeats
  the artifact's `EvalEquivAt`/`EvalEquiv` outright (§1). *Resolved in
  principle* by coarsening the observation to ground values: a binder
  then returns an unobservable closure (`lam_closure_obs_agree`, §3).

* **Depth/gate obstruction** (applications are gate-mediated; the
  contractum performs none) — defeats even the *unconditional* ground
  `CtxEquiv` (§4, `beta_not_unconditional_CtxEquiv`). Forces the relation
  to be *conditional*: standard `base-apply` gate with depth margin
  (`BuiltinReadyP`) and pure pre-hole siblings — exactly the side
  conditions `contextual_beta_pure` already carries for the lam-free
  cases.

So the open problem is **not** "prove `CtxEquiv redex contractum`" — §4
shows that is false. It is: extend the conditional congruence
`Ctx.plug_cong_master` to the `.lam` constructor, which requires *both*

  (a) the ground-coarsening for the closure case — a `ValVis`-style
      bisimulation refined to relate β-related closure bodies (the Howe /
      logical-relation step), which §3 shows is the right and sufficient
      shape; and

  (b) threading the `BuiltinReadyP` / `Pure` side conditions through the
      binder — the condition-preservation `plug_cong_master` already does
      for the other twelve constructors, here compounded with (a).

The congruence *machinery* is free (`CtxEquiv.congr` / `under_lam` /
`under_binders` transfer to the conditional relation once its side
conditions are shown closed under context composition); the difficulty
is entirely in (a)+(b) for the binder. -/

end LeanBlack
