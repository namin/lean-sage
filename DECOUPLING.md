# DECOUPLING — lean-sage's operational CE is not an equational-preservation theorem

**Thesis.** lean-sage's gate certifies an *operational simulation* property
for changes to `base-apply`: every application that succeeded through the
old apply rule can be reproduced through the new one with a *related*
result. **Equational preservation is a different, relational obligation**:
laws valid under one semantic configuration must remain valid under a later
configuration, in all relevant contexts. lean-sage proves operational CE,
and proves selected β laws *separately and conditionally*; it currently
proves **no general theorem transporting those laws across a CE-admitted
transition**. So equational preservation is not supplied by the present CE
certificate — it must be earned by an additional relational gate condition
or a lifting theorem.

This note is deliberately narrow about what is and isn't shown. For the
headline results and their qualifiers see [`SCOPE.md`](SCOPE.md) and
[`CLAIMS.md`](CLAIMS.md).

> The title says *operational CE* on purpose. In logic, "conservative
> extension" often means preservation of *all* old-language theorems,
> equations included. lean-sage's `CE_weak_strong` is a specific operational
> predicate; this note is about that predicate, not the logician's notion.

## The two obligations

**Operational CE (`CE_weak_strong`).** A property of a *change to the apply
rule*. It quantifies over one `callAsBaseApply old op operands` execution
and requires a successful execution through `new` whose result is
**bisimulation-related** (`ValVis_weak`), not necessarily identical
(`approvedPolicy_soundForCE_weak_strong`, `LeanBlack/ProofBased.lean`;
worked instance `multnExact_soundForCE_first_install_tower`,
`LeanBlack/Policies.lean`). Propagated across reflective depth,
`eval_tower_safe` (`LeanBlack/Soundness.lean`) gives `TowerCE` /
`SafeEvolution`: it relates the apply rules stored at corresponding tower
levels — it is **not** a whole-program, cross-version observational
equivalence `eval_S(P) ≈ eval_{S'}(P)`.

**Equational validity.** A relation between *terms*, relative to an
*observing configuration*. Write `M ≈_{P,S} N` for "`M` and `N` are
contextually indistinguishable under semantics `S` at configurations
satisfying predicate `P`". lean-sage's β law is of this shape:
`contextual_beta_pure` / `wand_beta_ctx_pure_at_start`
(`LeanBlack/ContextualBetaPure.lean`) establish a **conditional,
contextually-quantified exact-outcome equivalence** for the redex/contractum
pair — under `BuiltinReadyP`, lam-free contexts, pure pre-hole siblings, and
a pure operand. It is *not* the unconditional `CtxEquiv` relation of
`LeanBlack/CtxEquiv.lean`; indeed `beta_not_unconditional_CtxEquiv` proves
the pair is **not** in unconditional `CtxEquiv` (at the top of the tower the
redex's gate-mediated apply is stuck while the contractum converges).

These are different questions. CE asks: *after replacing a level's apply
rule, can every previously-successful application be simulated through the
new rule with a related result?* Equational validity asks: *can I substitute
`N` for `M` in every context without any observer noticing — under this
configuration and semantics?*

## What lean-sage does and does not connect

The missing link is a **transport** theorem:

> `CE(S, S')  ∧  (M ≈_{P,S} N)  ⟹  (M ≈_{P',S'} N)`

(with the relationship between `P` and `P'` itself to be stated). lean-sage
does not prove it. Two cautions about what that absence does and does not
mean:

- **Absence is not refutation.** lean-sage having no transport theorem does
  not prove transport is *false*. Establishing genuine independence would
  need both a `CE ∧ ¬EqPres` witness and an `EqPres ∧ ¬CE` witness inside
  the *same* admission mechanism; this note claims neither. (The appendix
  is explicitly *not* a CE witness — see below.)

- **A separate β proof is not evidence against transport.**
  `contextual_beta_pure` answers `Beta(S)` — "does β hold in the current
  semantics?" — not `TransportBeta(S, S')`. Even a system that *did* have a
  CE-to-transport theorem would still need an independent proof that β held
  initially. So the mere existence of a hard, separate β development says
  nothing about whether transport holds.

What the β development *does* show is the **shape** the equational side is
forced into. The three impossibilities explain why the current development
cannot simply drop its observation, depth, and context restrictions:
unconditional `CtxEquiv` (`beta_not_unconditional_CtxEquiv`), exact-outcome
congruence under `.lam` (`lam_EvalEquiv_congruence_fails`), and the
*unbudgeted* reverse simulation (`reverseSimβ_false`) are respectively
false. Purity is an additional *sufficient* condition used by the positive
development, not (here) a proved-necessary one. These results constrain the
shape of an equational theorem; they do **not** establish CE-to-equational
nonimplication.

Conversely, `obsConv_refine_forward` (`LeanBlack/LamBetaReflect.lean`) is
positive evidence that the transport layer is *buildable*: gate readiness +
purity + a cross-side β relation together establish the forward half of a
ground-observational refinement under a binder. That is the template for
what a transport theorem would need — operational invariants plus a
relational lifting — not a proof that CE gives it for free.

## The sharper reason: equivalence is configuration-indexed

Internally, an admitted reflection does **not** replace the Lean function
`eval` — `eval` is fixed. What changes is a *tower configuration*
`(ptable, level, env, T)`, especially the value stored in a `base-apply`
cell. An equation is therefore not a relation between syntax trees; it is
relative to an observing configuration — policy table, level, environment,
tower state, and observation discipline — and lean-sage's reflective
transitions change exactly that configuration. An equation that held is a
claim about a configuration that may no longer be the operative one.
Operational CE relates the apply rules across the transition; it does not,
by itself, carry a relational law stated over the old configuration to the
new one.

## The conclusion to keep

> **The gate certifies simulation of the old application behavior — not
> transport of the relational laws used to reason about programs.**

Stated as one sentence: operational CE is a *simulation* obligation;
equational preservation across change is a *transport* obligation. lean-sage
proves the simulation property and selected equational-*validity* results
for particular configurations (`contextual_beta_pure`), but it does not yet
prove a general CE-to-equational transport theorem. The research problem
this frames is the useful one:

> **What local admission conditions, interface restrictions, and relational
> lifting principles suffice to make selected equational laws durable across
> reflective transitions?**

`obsConv_refine_forward` is a first data point that the answer is not
"nothing"; a full `TransportBeta` under CE-admitted transitions is open (a
weak-relation analog of the `eval_tower_safe` induction; cf. `SCOPE.md`,
"Reflective depth: what is NOT claimed").

For the LICS-ask framing this sharpens two open needs:

- *"Equational theories that survive gated reflection"* — not a corollary of
  the CE gate; a distinct transport obligation, of which the conditional β
  law is a first (non-transported) instance.
- *"A negative theory of incompatible substrate–gate pairings"* — precisely:
  a gate that **admits unrestricted syntax-discriminating reflection**
  cannot simultaneously preserve the full nontrivial contextual theory
  characterized in Wand's model (Wand 1998, contextual equivalence collapses
  to α-congruence). Note this is a fact about the **admission policy**, not
  the substrate: a substrate expressive enough to represent syntax-inspecting
  reflection whose gate *rejects* every such modification is not
  incompatible with equational preservation.

## What this does NOT claim

- Not that operational CE and equational preservation are *logically
  independent* — only that they are *different obligations*, and no theorem
  in lean-sage transports the latter from the former.
- Not that any admitted lean-sage modification (e.g. multn) provably breaks
  an equational law — lean-sage proves no such thing.
- Not that equational reasoning under reflection is hopeless — it is
  conditionally recoverable (`contextual_beta_pure`), and the transport
  layer looks buildable (`obsConv_refine_forward`), just not free.

## Appendix — illustration of semantic-index dependence (not a CE counterexample)

`LeanBlack/SyntaxObserver.lean` illustrates the *configuration/semantics-
index* point with an external, evaluator-level extension. The observation
context `(syntax-tag [-])` is an ordinary lean-sage context
`syntaxTagCtx : Ctx` (lam-free, depth 0, pure-sided).

- `base_equates_in_syntaxTagCtx` — under the base evaluator this exact
  context equates the β pair in the may-convergence sense (identical
  `∃k, eval … = some (v, T')` behaviour for every exact `(v, T')`), by
  instantiating `wand_beta_ctx_pure_at_start`; machine-checked. (In the
  canonical stuck environment neither side converges.)
- `syntaxObserver_separates` — under a *different* function `evalF` (the
  base evaluator plus one syntax-reading operative) the same syntactic
  context yields distinct observable ground values (`.num 0` vs `.num 1`).

**This is not a `CE_weak_strong` counterexample.** `evalF` is not a
`base-apply` modification and is not related to `eval` by
`CE_weak_strong`; `evalF_agrees_off_operative_root` is whole-program
agreement off one root pattern, not the CE gate. It is a *root-only*
observer, not a fexpr evaluator, and not Wand's triviality theorem — one
characteristic witness that an equation is relative to the observing
semantics, which changing the semantics can invalidate. Kernel-clean,
pinned in `LeanBlack/AxiomAudit.lean`; run `lake exe syntaxObserverSmoke`.

The appendix sharpens the intuition; the conclusion rests on the main text:
operational CE is a simulation obligation and equational preservation across
change is a transport obligation. lean-sage supplies the simulation gate and
proves selected equational-validity laws for particular configurations
(`contextual_beta_pure`), but no general theorem transporting those laws
across a CE-admitted transition — that transport layer is the open problem.
