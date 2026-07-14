# DECOUPLING — conservative extension is not equational preservation

**Thesis.** The property lean-sage's gate certifies — *conservative
extension* — and the property equational reasoning needs — *preservation of
a contextual/equational theory* — are **independent**. A gate that
guarantees the first guarantees nothing about the second. This is not a
limitation of the current proofs; it is a fact about what the two
properties *are*, and lean-sage's own theorem structure already exhibits
it.

For what each headline result does and does not claim, see
[`SCOPE.md`](SCOPE.md) and [`CLAIMS.md`](CLAIMS.md). This note isolates one
cross-cutting conclusion.

## The two axes

**Conservative extension (`CE_weak_strong`).** A property of a *change to
the evaluator*: replacing the `base-apply` value preserves every
previously-successful application's result, up to CakeML-style value
bisimulation. It quantifies over `callAsBaseApply (op : Val) (args : List
Val)` — over already-evaluated *values* — and is carried by an
`ApprovedModification`'s kernel-checked proof
(`approvedPolicy_soundForCE_weak_strong`, `LeanBlack/ProofBased.lean`;
worked instance `multnExact_soundForCE_first_install_tower`,
`LeanBlack/Policies.lean`; propagated through reflective depth by
`eval_tower_safe`, `LeanBlack/Soundness.lean`).

**Contextual equivalence (`CtxEquiv`).** A relation between *terms*,
relative to a *fixed observing semantics*: `M ≈ N` iff `M` and `N`
may-converge to the same ground value (`.num`/`.bool`) in every context
(`LeanBlack/CtxEquiv.lean`). It is a statement about the evaluator, not
about any particular closed run.

These answer different questions. CE asks: *after I change the machine, do
old programs still produce their old outputs?* Equational reasoning asks:
*can I substitute `N` for `M` anywhere without any observer noticing?* The
first is preserved by construction of the gate; the second is a property of
the semantics the gate is allowed to change.

## Why they are independent — from lean-sage's own theorems

The decoupling does not need the fexpr experiment. It is visible in the
shape of the existing β development.

**If CE implied equational preservation, `contextual_beta_pure` would be a
corollary of the CE theorems.** It is not. It is a separate, hard
development that CE never mentions, and it carries side conditions CE never
imposes:

- `contextual_beta_pure` / `wand_beta_ctx_pure_at_start`
  (`LeanBlack/ContextualBetaPure.lean`) — β *is* a contextual equivalence,
  but only for **lam-free, pure-sided contexts under a depth budget**
  (`BuiltinReadyP`). None of those conditions appears in `CE_weak_strong`.

- The forward half alone (`obsConv_refine_forward`,
  `LeanBlack/LamBetaReflect.lean`) needs the gate *plus* purity — again,
  conditions foreign to CE.

And the equation genuinely **fails** without those conditions — three
machine-checked impossibilities pin why:

- `beta_not_unconditional_CtxEquiv` (`LeanBlack/CtxEquiv.lean`) — at the top
  of the tower the redex's gate-mediated apply cannot fire, so it diverges
  where the contractum converges. β is *not* an unconditional contextual
  equivalence.
- `lam_EvalEquiv_congruence_fails` — outcome-equality congruence is false
  under `.lam` (closures freeze bodies).
- `reverseSimβ_false` — the gate alone, without a depth margin, is
  insufficient for the reverse direction.

So the equational fact is conditional, hard, and independently proved, and
it is false in exactly the regimes CE says nothing about. **That gap — a
separate conditional theorem flanked by impossibility results, sitting next
to an unconditional CE guarantee — is the decoupling, already mechanized.**

## The sharper reason: contextual equivalence is evaluator-indexed

`CtxEquiv` / `wand_beta_ctx_pure_at_start` are theorems about **`eval`**.
They are not statements about arbitrary semantic extensions of `eval`.
Since a reflective system's whole premise is that it *changes its own
evaluator*, an equation that held is a claim about a semantics that may no
longer be the operative one. Preserving every old closed-program result
(CE) does not preserve the observing semantics that made two terms
equivalent — because the equivalence was never a fact about the preserved
behavior; it was a fact about the (mutable) semantics.

Concretely: a context that is *stuck* under the base evaluator has no
distinguishing power, so it cannot witness an inequivalence — but a semantic
extension can give that same syntactic context new observational power, and
then it does. See the appendix.

## The consequence

> The gate certifies that old **behavior** survives — not that old
> **reasoning** survives.

For a self-improving / reflective system this is the load-bearing caveat:
it can keep every promise about outputs (CE across the whole tower,
`eval_tower_safe`) and still invalidate the equational theory its own code
was written against. **Equational-theory preservation is a distinct
obligation from conservative extension, and it needs a distinct gate** — an
equational/contextual checker, not a CE checker. Wand 1998 bounds what such
a gate can admit: with unrestricted syntactic reflection, the only
surviving congruence is α-equivalence.

For the LICS-ask framing this refines two of the open needs:

- *"Equational theories that survive gated reflection"* — this is not a
  corollary of the CE gate; it is a separate obligation, and lean-sage's
  β development is a first (conditional) instance of discharging it.
- *"A negative theory of incompatible substrate–gate pairings"* — a CE gate
  is provably silent about equational theories; a semantic substrate that
  admits syntactic reflection is incompatible with a gate meant to preserve
  a nontrivial equational theory (Wand).

## What this does NOT claim

- Not that CE and equational preservation are in *conflict* — only that
  they are *independent*. A modification can satisfy both.
- Not that any specific admitted lean-sage modification (e.g. multn)
  provably breaks a contextual equivalence — lean-sage proves no such
  thing. The claim is about the *guarantees*: the CE gate provides no
  equational theorem, and β-preservation had to be earned separately and
  conditionally.
- Not that equational reasoning under reflection is hopeless — it is
  conditionally recoverable (`contextual_beta_pure`), just not for free.

## Appendix — a sharpening witness (`LeanBlack/Fexpr.lean`)

An additive, evaluator-only illustration of the evaluator-index point. The
observation context `(syntax-tag [-])` is an *ordinary* lean-sage context
`syntaxTagCtx : Ctx` (a hole in application-argument position), lam-free,
depth 0, pure-sided.

- `base_equates_in_syntaxTagCtx` — under the base evaluator this exact
  context equates the β pair `((λx.x) 0)` and `let x = 0 in x` (by
  instantiating `wand_beta_ctx_pure_at_start`; machine-checked, not
  asserted).
- `operative_separates` — under `evalF` (the base evaluator plus one
  syntax-reading operative) the **same syntactic context** maps the pair to
  distinct ground values (`.num 0` vs `.num 1`).
- `syntaxTagCtx_equated_by_eval_but_separated_by_evalF` — the two together:
  the evaluator index is load-bearing. A previously-stuck context acquires
  observational power under a semantic extension and refines `≈`, without
  enlarging the context syntax at all.

Honest scope (see the file header): this is a *root-only* observer, **not**
a fexpr evaluator, **not** a statement about `CE_weak_strong` (the operative
is not a `base-apply` modification, so `evalF_agrees_off_operative_root` is
whole-program agreement off one root pattern, not the CE gate), and **not**
Wand's full triviality theorem — one characteristic counterexample.
Kernel-clean, axiom-pinned in `LeanBlack/AxiomAudit.lean`; run
`lake exe fexprSmoke`.

The witness sharpens the conclusion, but the conclusion stands on the
existing β theorems alone: **conservative extension is not equational
preservation.**
