/-
  lean-sage: a top-level syntax-sensitive observation extension.

  An *additive, independent* facility. It does **not** touch `Val`, `Expr`,
  `eval`, or any existing theorem: it reuses the real evaluator verbatim
  and adds one syntax-sensitive observer on top of it.

  ## Motivation and honest scope

  lean-sage's gate certifies `CE_weak_strong` — a **value-level,
  directional "no-clobbering"** property: every application the old
  `base-apply` handled successfully is still handled compatibly by the new
  one, quantified over `callAsBaseApply` and carried by an
  `ApprovedModification`'s kernel-checked proof. That is an *operational*
  conservative extension. It is **not** the *equational* statement that a
  contextual equivalence `M ≃ N` is preserved: preserving every old
  execution does not stop a language extension from adding a **new context**
  that distinguishes previously-equivalent terms.

  The reason lean-sage's β results hold is that the gated modification
  surface — `base-apply` — receives already-evaluated argument *values*
  (`applyVia … (op : Val) (args : List Val)`), never operand *syntax*. A
  genuine fexpr (operative) is the opposite: it receives operands
  **unevaluated**, one semantic layer earlier, so it is not expressible as a
  `base-apply` modification at all.

  This file models the *smallest slice* of that earlier layer: a single
  operative `syntax-tag`, recognized **only at the root of a program**,
  that returns a **ground** value determined by its operand's head
  constructor. It is deliberately not a fexpr evaluator — see "What this is
  not" below.

  ## What this shows

  * `evalF_agrees_off_operative_root` — when the *whole program* is not the
    operative form, `evalF` delegates to the base evaluator (definitional).
    This is whole-program agreement off one root pattern. **It is not
    lean-sage's `CE_weak_strong` gate** (no `base-apply` replacement, no
    `ApprovedModification`).

  * `observe_base_undefined` — the operative form is meaningless in the base
    language (`syntax-tag` is unbound), so adding it only gives meaning to a
    previously-undefined program.

  * `same_base_result` — the β-redex `((λx.x) 0)` and the β-contractum
    `let x = 0 in x` produce the same base result. The *genuine* contextual
    equation for this pair is `wand_beta_ctx_pure_at_start`
    (`ContextualBetaPure.lean`): they are contextually equivalent for every
    context in the lam-free, pure-sided (and operative-free) class `Ctx`.

  * `operative_separates` — the operative context maps this pair to two
    distinct **ground** values (`.num`), so it separates a pair that
    `wand_beta_ctx_pure_at_start` equates.

  Bundled as `same_base_result_but_operative_separates`. The point: the
  operative is a context **outside** the class `Ctx` for which contextual β
  is proved. The pure/operative-free restriction on `Ctx` is therefore not
  incidental — syntactic-reflection contexts are exactly what it excludes,
  and admitting them (as a real fexpr would) breaks the equational theory.

  ## What this is NOT

  * **Not Wand's theorem.** Wand 1998 proves the full collapse (contextual
    equivalence = α-congruence). This is one characteristic *counterexample*
    in lean-sage's syntax, not the triviality theorem.
  * **Not a fexpr evaluator.** `asOperative` fires only when the *entire
    program* is `(syntax-tag operand)`; an operative nested inside a larger
    program is delegated to `evalProgram`, which does not know `syntax-tag`.
    So `asOperative e = none` means "not an operative at the root", not
    "operative-free". A genuine model would put a `base-combine` hook
    *before* operand evaluation, recognize operatives at arbitrary depth,
    carry the caller environment, and distinguish applicative from operative
    closures. That is the next step; see the branch notes.
  * **Not `CE_weak_strong`.** See `evalF_agrees_off_operative_root` above.

  One root observer is enough to *refute* a contextual equivalence — cf.
  `beta_not_ObsEq` in lean-refl-beta, which refutes with an equally shallow
  context — which is all this file claims.
-/

import LeanBlack.ProofBased
import LeanBlack.ContextualBetaPure

namespace LeanBlack

/-! ## The operative: syntactic discrimination of an operand -/

/-- The operative's behaviour: a **ground** value (`.num`) determined by the
    operand's *head constructor*, read off its **syntax** without evaluating
    it. Ground so that the distinction is observable under lean-sage's
    Morris-style ground observation (`CtxEquiv` observes only `.num`/`.bool`;
    a `.sym` tag would not refute it). This is exactly the reflective power
    Wand shows collapses the equational theory: telling `((λx.x) 0)` (an
    `.app`, tag `0`) from `let x = 0 in x` (a `.letE`, tag `1`) before
    either is run. -/
def synHeadTag : Expr → Val
  | .app _       => .num 0
  | .letE _ _ _  => .num 1
  | _            => .num 2

/-- Recognise the operative form `(syntax-tag operand)` **at the root**,
    returning the *unevaluated* operand. In the base language the head
    `syntax-tag` is an unbound variable, so this form has no prior meaning
    (see `observe_base_undefined`). -/
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

/-! ## The witnesses: the Wand β pair and the operative observer -/

/-- The β-redex `((λx. x) 0)`. -/
def betaRedex : Expr := .app [.lam ["x"] (.var "x"), .num 0]

/-- The β-contractum `let x = 0 in x`. Same pair as
    `wand_beta_ctx_pure_at_start`. -/
def betaContractum : Expr := .letE "x" (.num 0) (.var "x")

/-- The operative observation context `C[-] = (syntax-tag [-])` — a context
    *outside* the operative-free class `Ctx` of `contextual_beta_pure`. -/
def observe (o : Expr) : Expr := .app [.var "syntax-tag", o]

/-! ## The separation -/

/-- **Agreement off the operative root.** When the whole program is not the
    operative form, the extended evaluator is the base evaluator. This is
    whole-program agreement off one root pattern — **not** lean-sage's
    `CE_weak_strong` gate (which replaces a `base-apply` value under an
    `ApprovedModification`), and the hypothesis is "not an operative at the
    root", not "operative-free". -/
theorem evalF_agrees_off_operative_root (fuel : Nat) (ptable : PolicyTable)
    (e : Expr) (dp : BlackPolicy) (h : asOperative e = none) :
    evalF fuel ptable e dp = evalProgram fuel ptable e dp := by
  simp [evalF, h]

/-- The operative form is *meaningless* in the base language for our
    witnesses: `syntax-tag` is unbound, so the base evaluator rejects it.
    Hence adding the operative only gives meaning to a previously-undefined
    program (additivity, witnessed on the pair used below).

    The fully general statement — `∀ o fuel ptable dp,
    evalProgram fuel ptable (observe o) dp = none`, whence whole-program
    success preservation `evalProgram e = some v → evalF e = some v` — needs
    a lemma that the start tower's level-0 env never binds `"syntax-tag"`
    (independent of the policy). Left as a follow-up; see the branch notes. -/
theorem observe_witnesses_base_undefined :
    evalProgram 100 [acceptAllPolicy] (observe betaRedex) = none
    ∧ evalProgram 100 [acceptAllPolicy] (observe betaContractum) = none := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **Same base result.** The β-redex and β-contractum produce the same
    value under the base evaluator. Their genuine *contextual* equivalence
    (over the operative-free class `Ctx`) is `wand_beta_ctx_pure_at_start`. -/
theorem same_base_result :
    evalProgram 100 [acceptAllPolicy] betaRedex
      = evalProgram 100 [acceptAllPolicy] betaContractum := by
  decide +kernel

/-- **The operative context separates the pair — at ground type.** The
    single operative context distinguishes the β-equal pair:
    `(syntax-tag ((λx.x) 0)) ⇓ 0` while `(syntax-tag (let x = 0 in x)) ⇓ 1`.
    So a context *outside* `Ctx` refutes the contextual equivalence that
    `wand_beta_ctx_pure_at_start` establishes for contexts *inside* it. -/
theorem operative_separates :
    evalF 100 [acceptAllPolicy] (observe betaRedex)
      ≠ evalF 100 [acceptAllPolicy] (observe betaContractum) := by
  decide +kernel

/-- **The dividing line, as one theorem.** The β pair has the same base
    result, yet a syntactic-reflection observer separates it at ground type.
    A Wand-style β counterexample in lean-sage's syntax: it shows the
    operative-free restriction on `Ctx` is load-bearing — not the full
    triviality theorem, and not a statement about `CE_weak_strong`. -/
theorem same_base_result_but_operative_separates :
    evalProgram 100 [acceptAllPolicy] betaRedex
        = evalProgram 100 [acceptAllPolicy] betaContractum
    ∧ evalF 100 [acceptAllPolicy] (observe betaRedex)
        ≠ evalF 100 [acceptAllPolicy] (observe betaContractum) :=
  ⟨same_base_result, operative_separates⟩

end LeanBlack
