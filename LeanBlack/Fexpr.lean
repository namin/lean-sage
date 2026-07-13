/-
  lean-sage: Fexpr experiment — the CE / β dividing line, made a theorem.

  This file is an *additive, independent* facility. It does **not** touch
  `Val`, `Expr`, `eval`, or any existing theorem: it reuses the real
  evaluator verbatim and adds *one operative special form* on top of it.
  The point is to turn a scoping caveat into a machine-checked separation.

  ## What the rest of lean-sage proves, and what it does not

  lean-sage's gate certifies `CE_weak_strong`: a **value-level, directional
  "no-clobbering"** property — every application the old `base-apply`
  handled successfully is still handled compatibly by the new one. That is
  an *operational* conservative extension. It is emphatically **not** the
  *equational* statement `M ≃_old N → M ≃_new N`: preserving every old
  execution does not stop a language extension from introducing a **new
  context** that distinguishes previously-equivalent terms.

  The reason lean-sage's β results (`contextual_beta_pure`,
  `wand_defeated_existential_gated_beta`) hold is *not* that CE implies
  them. It is that the gated modification surface — `base-apply` — receives
  already-evaluated argument *values* (`applyVia … (op : Val) (args : List
  Val)`), never operand *syntax*. A genuine fexpr (operative) is defined by
  the opposite: it receives its operand **unevaluated**. So a fexpr is not
  expressible as a `base-apply` modification at all; it lives one semantic
  layer earlier.

  ## What this file shows

  Model that earlier layer minimally: `evalF` is the ordinary evaluator
  extended with a single operative, `syntax-tag`, which receives its
  operand as *syntax* and returns a value determined by the operand's head
  constructor (Wand's decisive premise: syntactic discrimination of
  operands). Then:

  * `evalF_conservative` — on every operative-free program `evalF` agrees
    with the base evaluator (indeed the operative form was previously
    *meaningless*, `base_operative_undefined`). So the extension passes a
    behavioral / operational CE gate.

  * `betaPair_obsEquiv` — the Wand pair `((λx.x) 0)` and `0` are
    observationally equivalent under the *base* evaluator (β at top level).

  * `operative_distinguishes` — yet the single operative context
    `(syntax-tag [-])` maps them to different values under `evalF`, so the
    β contextual equivalence **fails** once the operative exists. The
    extension does *not* pass an equational CE gate.

  Bundled as `beta_survives_but_operative_breaks_it`. This is Wand 1998
  ("The Theory of Fexprs is Trivial") localized inside lean-sage's own
  calculus: not a collapse the gate "defeats", but the negative theorem
  explaining why an equational gate must reject unrestricted syntactic
  reflection.

  ## Scope of this experiment

  `evalF` intercepts the operative at the observation site (a top-level
  context). One distinguishing context is all a *refutation* of a
  contextual equivalence needs — cf. `beta_not_ObsEq` in lean-refl-beta,
  which refutes with an equally shallow context. A full structural overlay
  (the operative firing at any depth) and the corresponding *restricted*
  operative that may control evaluation order yet not discriminate syntax
  — the β-*safe* fexpr — are the natural next steps; see the branch notes.
-/

import LeanBlack.ProofBased

namespace LeanBlack

/-! ## The operative: syntactic discrimination of an operand -/

/-- The operative's behaviour: a value determined by the operand's *head
    constructor*, read off its **syntax** without evaluating it. This is
    exactly the reflective power Wand shows collapses the equational
    theory — the ability to tell `((λx.x) 0)` (an `.app`) from `0` (a
    `.num`) before either is run. -/
def synHeadTag : Expr → Val
  | .num _           => .sym "lit"
  | .bool _          => .sym "lit"
  | .quote _         => .sym "lit"
  | .var _           => .sym "var"
  | .ifte _ _ _      => .sym "ifte"
  | .lam _ _         => .sym "lam"
  | .app _           => .sym "app"
  | .set _ _         => .sym "set"
  | .em _            => .sym "em"
  | .primApp _ _     => .sym "primApp"
  | .letE _ _ _      => .sym "letE"
  | .seq _           => .sym "seq"
  | .installPolicy _ => .sym "installPolicy"

/-- Recognise the operative form `(syntax-tag operand)`, returning the
    *unevaluated* operand. In the base language the head `syntax-tag` is an
    unbound variable, so this form has no prior meaning (see
    `base_operative_undefined`) — adding the operative is additive. -/
def asOperative : Expr → Option Expr
  | .app [.var "syntax-tag", operand] => some operand
  | _                                 => none

/-- The base evaluator extended with the one operative. Ordinary programs
    are handed to the real `evalProgram` unchanged; only the operative form
    is intercepted, and it consumes its operand as **syntax**. -/
def evalF (fuel : Nat) (ptable : PolicyTable) (e : Expr)
    (defaultPolicy : BlackPolicy := acceptAllPolicy) : Option Val :=
  match asOperative e with
  | some operand => some (synHeadTag operand)
  | none         => evalProgram fuel ptable e defaultPolicy

/-! ## The witnesses: the Wand β pair and the operative context -/

/-- The β-redex `((λx. x) 0)`. -/
def betaRedex : Expr := .app [.lam ["x"] (.var "x"), .num 0]

/-- Its value `0` — the β-contractum's outcome. Same pair as
    `wand_defeated_existential`. -/
def betaValue : Expr := .num 0

/-- The operative observation context `C[-] = (syntax-tag [-])`. -/
def observe (o : Expr) : Expr := .app [.var "syntax-tag", o]

/-! ## The separation -/

/-- **Behavioral / operational CE.** On any operative-free program the
    extended evaluator is exactly the base evaluator: the operative changes
    nothing about old behaviour. This is the gate lean-sage's certificates
    speak to. -/
theorem evalF_conservative (fuel : Nat) (ptable : PolicyTable) (e : Expr)
    (dp : BlackPolicy) (h : asOperative e = none) :
    evalF fuel ptable e dp = evalProgram fuel ptable e dp := by
  simp [evalF, h]

/-- The operative form is *meaningless* in the base language: `syntax-tag`
    is unbound, so the base evaluator diverges/rejects. Adding the
    operative therefore only gives meaning to previously-undefined
    programs — the strongest form of operational conservativity. -/
theorem base_operative_undefined :
    evalProgram 100 [acceptAllPolicy] (observe betaValue) = none := by
  decide +kernel

/-- **β at top level, base evaluator.** The Wand pair converges to the same
    value under the ordinary evaluator — the equivalence the operative is
    about to break. -/
theorem betaPair_obsEquiv : ObsEquivConverges betaRedex betaValue := by
  refine ⟨100, .num 0, ?_, ?_⟩ <;> decide +kernel

/-- **Equational CE fails.** The single operative context distinguishes the
    β-equal pair: `(syntax-tag ((λx.x) 0)) ⇓ app` while
    `(syntax-tag 0) ⇓ lit`. So `M ≃_old N` does **not** survive the
    extension — one new context suffices to refute the contextual
    equivalence. -/
theorem operative_distinguishes :
    evalF 100 [acceptAllPolicy] (observe betaRedex)
      ≠ evalF 100 [acceptAllPolicy] (observe betaValue) := by
  decide +kernel

/-- **The dividing line, as one theorem.** The β pair is observationally
    equivalent under the base evaluator, yet the operative context
    distinguishes it: behavioral conservative extension does not imply
    preservation of the equational theory. Wand's collapse, localized in
    lean-sage's calculus. -/
theorem beta_survives_but_operative_breaks_it :
    ObsEquivConverges betaRedex betaValue
    ∧ evalF 100 [acceptAllPolicy] (observe betaRedex)
        ≠ evalF 100 [acceptAllPolicy] (observe betaValue) :=
  ⟨betaPair_obsEquiv, operative_distinguishes⟩

end LeanBlack
