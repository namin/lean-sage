/-
  lean-sage: the syntax-observation / β dividing line.

  An *additive, independent* facility. It does **not** touch `Val`, `Expr`,
  `eval`, or any existing theorem: it reuses the real evaluator verbatim
  and adds one syntax-sensitive observer on top of it.

  ## Motivation and honest scope

  lean-sage's gate certifies `CE_weak_strong` — a **value-level,
  directional "no-clobbering"** property, quantified over `callAsBaseApply`
  and carried by an `ApprovedModification`'s kernel-checked proof. That is
  an *operational* conservative extension. It is **not** the *equational*
  statement that a contextual equivalence `M ≃ N` is preserved.

  The reason lean-sage's β results hold is that the gated modification
  surface — `base-apply` — receives already-evaluated argument *values*
  (`applyVia … (op : Val) (args : List Val)`), never operand *syntax*. A
  genuine fexpr (operative) is the opposite: it receives operands
  **unevaluated**, one semantic layer earlier.

  This file models the *smallest slice* of that earlier layer: a single
  operative `syntax-tag`, recognized **only at the root of a program**,
  that returns a **ground** value determined by its operand's head
  constructor.

  ## What this shows — the evaluator index is load-bearing

  The observation context `(syntax-tag [-])` is an *ordinary* lean-sage
  context `syntaxTagCtx : Ctx` (a hole in application-argument position). It
  is lam-free, reflective-depth 0, and pure-sided (its only pre-hole sibling
  is the variable `syntax-tag`, which is `Pure`). So it satisfies the
  hypotheses of `wand_beta_ctx_pure_at_start`:

  * `base_equates_in_syntaxTagCtx` — under the **base evaluator** this exact
    context equates the β pair `((λx.x) 0)` and `let x = 0 in x` (obtained
    by instantiating `wand_beta_ctx_pure_at_start`, not merely asserted).

  * `operative_separates` — under `evalF` the **same syntactic context**
    maps the pair to two distinct **ground** values (`.num 0` vs `.num 1`).

  Bundled as `syntaxTagCtx_equated_by_eval_but_separated_by_evalF`. So the
  load-bearing thing is **not** an "operative-free" restriction on `Ctx`
  (the context is *in* `Ctx`), but the **evaluator index**:
  `wand_beta_ctx_pure_at_start` is a theorem about `eval`, not about
  arbitrary semantic extensions of `eval`. A previously *stuck* context
  (`syntax-tag` is unbound in the base) acquires syntax-inspecting power
  under `evalF` and refines contextual equivalence — without enlarging the
  context syntax at all.

  * `evalF_agrees_off_operative_root` — off the root operative form, `evalF`
    is the base evaluator. Whole-program agreement off one root pattern —
    **not** `CE_weak_strong` (no `base-apply` replacement, no
    `ApprovedModification`); the hypothesis is "not an operative at the
    root", not "operative-free".

  * `observe_witnesses_base_undefined` — in the base language the observer
    form is meaningless (`syntax-tag` unbound), so the extension only gives
    meaning to previously-stuck programs.

  ## What this is NOT

  * **Not Wand's theorem.** Wand 1998 proves the full collapse (contextual
    equivalence = α-congruence). This is one characteristic *counterexample*
    in lean-sage's syntax under a semantic extension, not the triviality
    theorem.
  * **Not a fexpr evaluator.** `asOperative` fires only when the *whole
    program* is `(syntax-tag operand)`. A genuine model needs a
    `base-combine` hook *before* operand evaluation, operatives at arbitrary
    depth, the caller environment, and applicative-vs-operative closures.
    That is the next step; see the branch notes.
  * **Not `CE_weak_strong`.** See `evalF_agrees_off_operative_root`.
-/

import LeanBlack.ProofBased
import LeanBlack.ContextualBetaPure

namespace LeanBlack

/-! ## The operative: syntactic discrimination of an operand -/

/-- The operative's behaviour: a **ground** value (`.num`) determined by the
    operand's *head constructor*, read off its **syntax** without evaluating
    it. Ground so the distinction is observable under lean-sage's
    Morris-style ground observation (`CtxEquiv` observes only `.num`/`.bool`).
    This is the reflective power Wand shows collapses the equational theory:
    telling `((λx.x) 0)` (an `.app`, tag `0`) from `let x = 0 in x` (a
    `.letE`, tag `1`) before either is run. -/
def synHeadTag : Expr → Val
  | .app _       => .num 0
  | .letE _ _ _  => .num 1
  | _            => .num 2

/-- Recognise the operative form `(syntax-tag operand)` **at the root**,
    returning the *unevaluated* operand. -/
def asOperative : Expr → Option Expr
  | .app [.var "syntax-tag", operand] => some operand
  | _                                 => none

/-- The base evaluator extended with the one root operative. Non-operative
    whole programs are handed to the real `evalProgram` unchanged; only the
    root operative form is intercepted, consuming its operand as **syntax**. -/
def evalF (fuel : Nat) (ptable : PolicyTable) (e : Expr)
    (defaultPolicy : BlackPolicy := acceptAllPolicy) : Option Val :=
  match asOperative e with
  | some operand => some (synHeadTag operand)
  | none         => evalProgram fuel ptable e defaultPolicy

/-! ## The witnesses: the Wand β pair and the observer context -/

/-- The β-redex `((λx. x) 0)`. -/
def betaRedex : Expr := .app [.lam ["x"] (.var "x"), .num 0]

/-- The β-contractum `let x = 0 in x`. Same pair as
    `wand_beta_ctx_pure_at_start`. -/
def betaContractum : Expr := .letE "x" (.num 0) (.var "x")

/-- The observation context `C[-] = (syntax-tag [-])`, as an *ordinary*
    lean-sage `Ctx`: a hole in application-argument position. It is lam-free,
    depth 0, and pure-sided — so it satisfies `wand_beta_ctx_pure_at_start`. -/
def syntaxTagCtx : Ctx := .app [.var "syntax-tag"] .hole []

/-- Fill the observer context. Definitionally `.app [.var "syntax-tag", e]`,
    so `asOperative (observe e) = some e`. -/
def observe (e : Expr) : Expr := syntaxTagCtx.plug e

/-! ## The separation -/

/-- **Agreement off the operative root.** When the whole program is not the
    operative form, the extended evaluator is the base evaluator. This is
    whole-program agreement off one root pattern — **not** lean-sage's
    `CE_weak_strong` gate, and the hypothesis is "not an operative at the
    root", not "operative-free". -/
theorem evalF_agrees_off_operative_root (fuel : Nat) (ptable : PolicyTable)
    (e : Expr) (dp : BlackPolicy) (h : asOperative e = none) :
    evalF fuel ptable e dp = evalProgram fuel ptable e dp := by
  simp [evalF, h]

/-- The observer form is *meaningless* in the base language for our
    witnesses: `syntax-tag` is unbound, so the base evaluator rejects it.
    Hence the extension only gives meaning to a previously-stuck program.

    (The fully general `∀ o fuel ptable dp, evalProgram fuel ptable
    (observe o) dp = none`, whence whole-program success preservation, needs
    a lemma that the start tower's level-0 env never binds `"syntax-tag"`;
    left as a follow-up — see the branch notes.) -/
theorem observe_witnesses_base_undefined :
    evalProgram 100 [acceptAllPolicy] (observe betaRedex) = none
    ∧ evalProgram 100 [acceptAllPolicy] (observe betaContractum) = none := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **Same base result** (a quick concrete check; the real contextual
    statement is `base_equates_in_syntaxTagCtx`). -/
theorem same_base_result :
    evalProgram 100 [acceptAllPolicy] betaRedex
      = evalProgram 100 [acceptAllPolicy] betaContractum := by
  decide +kernel

/-- **The base evaluator equates the pair in this exact context.** The
    observer context `syntaxTagCtx` is a lam-free, pure-sided `Ctx` at
    depth 0, so `wand_beta_ctx_pure_at_start` applies verbatim: under the
    base evaluator, `(syntax-tag ((λx.x) 0))` and `(syntax-tag (let x = 0 in
    x))` converge to the same ground outcomes. Machine-checked, not
    asserted. -/
theorem base_equates_in_syntaxTagCtx
    (ptable : PolicyTable) (p : BlackPolicy) (env : Env)
    (v : Val) (T_final : TowerState) :
    (∃ k, eval k ptable 0 (observe betaRedex) env
            ((buildTower (syntaxTagCtx.emDepth + 2)).setPolicyAt 0 p)
            = some (v, T_final))
    ↔
    (∃ k, eval k ptable 0 (observe betaContractum) env
            ((buildTower (syntaxTagCtx.emDepth + 2)).setPolicyAt 0 p)
            = some (v, T_final)) :=
  wand_beta_ctx_pure_at_start syntaxTagCtx (by rfl)
    (by
      refine ⟨?_, trivial⟩
      intro e he
      rcases List.mem_singleton.mp he with rfl
      rfl)
    (by decide) ptable p env v T_final

/-- **The operative context separates the pair — at ground type.** Under
    `evalF` the *same syntactic context* distinguishes the β pair:
    `(syntax-tag ((λx.x) 0)) ⇓ 0` while
    `(syntax-tag (let x = 0 in x)) ⇓ 1`. -/
theorem operative_separates :
    evalF 100 [acceptAllPolicy] (observe betaRedex)
      ≠ evalF 100 [acceptAllPolicy] (observe betaContractum) := by
  decide +kernel

/-- **The dividing line, as one theorem: the evaluator index is
    load-bearing.** The *same* `Ctx` equates the β pair under the base
    evaluator (`base_equates_in_syntaxTagCtx`), yet separates it — at ground
    type — under `evalF`. `wand_beta_ctx_pure_at_start` is a theorem about
    `eval`; a semantic extension can refine contextual equivalence by giving
    new observational power to a previously-stuck context, without enlarging
    the context syntax. A Wand-style counterexample, not the full triviality
    theorem, and not a statement about `CE_weak_strong`. -/
theorem syntaxTagCtx_equated_by_eval_but_separated_by_evalF :
    (∀ (ptable : PolicyTable) (p : BlackPolicy) (env : Env)
        (v : Val) (T_final : TowerState),
      (∃ k, eval k ptable 0 (observe betaRedex) env
              ((buildTower (syntaxTagCtx.emDepth + 2)).setPolicyAt 0 p)
              = some (v, T_final))
      ↔
      (∃ k, eval k ptable 0 (observe betaContractum) env
              ((buildTower (syntaxTagCtx.emDepth + 2)).setPolicyAt 0 p)
              = some (v, T_final)))
    ∧ evalF 100 [acceptAllPolicy] (observe betaRedex)
        ≠ evalF 100 [acceptAllPolicy] (observe betaContractum) :=
  ⟨base_equates_in_syntaxTagCtx, operative_separates⟩

end LeanBlack
