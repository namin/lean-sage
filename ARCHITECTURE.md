# ARCHITECTURE — the layers, and which complexity is necessary

lean-sage grew by accretion, and some of its structure shows growth
rings. This document is the corrective lens: the layer map, the
dualities that are *theorem-forced* (they cannot be unified, and we
can say why), and the remaining accidental complexity (flagged, with
its consolidation plan). Companion documents: [`SCOPE.md`](SCOPE.md)
(per-result qualifiers), [`CLAIMS.md`](CLAIMS.md) (claim-by-claim
classification), [`DESIGN.md`](DESIGN.md) / 
[`DESIGN_PROOF.md`](DESIGN_PROOF.md) (decision rationale).

## The layer map

```
 8  audit          Public, AxiomAudit            the claim surface; CI-pinned axioms
 7  equational     EvalFuelMono, Ctx, PureExt,   contextual β: redex ≡ contractum
    theory         CtxPure, ContextualBeta,        in every non-λ position
                   ContextualBetaPure
 6  composition    Compose, HeapAgree, GovChain  chains of admissions; gate swaps
 5  admission      ProofBased (+ approvals in    proof-bearing gates: the record's
                   HeapAgree, IdentityDelegate,    constructor demands the certificate
                   GovChain)
 4  tower          Soundness                     eval_tower_safe, SafeEvolution,
    theorems                                       the necessity counterexample
 3  policies       Policies                      CE relations; structural policies
 2  bisimulation   Bisim, Frame                  CakeML-style value bisim; cross-side
    engine                                         framing (the technical core, ~9.5k LOC)
 1  substrate      Black, Tower, Eval            syntax, values, global heap, levels,
                                                   the four mutually-recursive evaluators
```

Lower layers never import higher ones. The smoke layer
(`Smoke.lean`, `Demos.lean`, `ProofBasedSmoke.lean`) sits beside the
library and instantiates it on concrete runtime data.

## Necessary dualities (theorem-forced)

These look like duplication; they are not. Each pair coexists for a
reason that is itself proved or proven-about.

**1. Strict `CE` vs. weak `CE_weak_strong`.**
The whole-program tower theorem (`eval_tower_safe`) threads the
strict relation (`ValVis` results, `SafeEvolution` tables). The
proof-bearing gate can only ever be *weak*-sound: the multn worked
example concludes `ValVis_weak` because the installed closure's
captured environment refers into the post-admission heap — strict
soundness for it is impossible, not merely unproved. So the strict
relation owns the whole-trace theorem and the weak relation owns the
proof-bearing admission layer, and they meet nowhere. Unifying them
*is* the open problem (a weak-relation analog of the
`all_tower_safe` induction), recorded in `SCOPE.md`.

**2. Full-prefix vs. selective certificates.**
A full-prefix certificate (`CE_weak_strong`, `HeapPrefix`-bound) is
the natural per-admission form, but two successive real admissions
rewrite the same `base-apply` cell, so two full-prefix certificates
can never fire at a common test state (`fullPrefix_certs_conflict`).
Chains therefore *must* be carried by the selective form
(`CE_weak_strong_at`, pinning only the cells a proof reads). The
hierarchy is one-directional and proved: **the selective certificate
is the primitive**; the full-prefix form is its corollary
(`CE_weak_strong_of_at`). There is one multn proof
(`multnApproval_at_proof`) and one identity-delegate proof
(`identityDelegate_CE_at`); the `ApprovedModification`-facing forms
are derived.

**3. Structural policies vs. proof-bearing approvals.**
A structural policy (`multnExactPolicy`) amortizes one soundness
theorem over every admission of a foreseen shape; a proof-bearing
approval pays per modification and needs no foresight. This is a
design point of the paper (`DESIGN_PROOF.md`), not duplication:
`structural_policy_yields_approval` proves the structural path is an
amortization layer over the proof-bearing one.

**4. `CE_weak` beside `CE_weak_strong`.**
`CE_weak` is the premise-minimal statement the structural multn
theorem concludes in; `CE_weak_strong` adds the Deep/Shift test-state
premises the proof-bearing discipline needs. The coercion is one
line (`CE_weak_to_strong`); the weaker-premised form is what the
underlying soundness theorems naturally produce.

## Accidental complexity (flagged, with plan)

**Context-language tiers.** `Ctx`, `SimpleCtx`, `EasyCtx`,
`WideCtx` (`Ctx.lean`) and `PureCtx` (`CtxPure.lean`) are growth
rings of the contextual-β effort: each tier covers the positions
whose congruence was provable with the preservation hypotheses
available at the time. They differ only in (a) which positions are
included and (b) what is demanded of pre-hole siblings. The
consolidation target is one context language and one master
congruence parameterized by a sibling class `S : Expr → Prop` and a
predicate family: `S := fun _ => False` recovers the easy tier
(contexts with no pre-hole siblings), `S := fun _ => True` the wide
tier, `S := Pure` the pure tier, and the trivial predicate family
recovers the unconditional (`SimpleCtx`) track. Until that refactor
lands, treat `PureCtx.plug_cong_family` as the most general master
and the others as historical scaffolding kept for their weaker
hypotheses.

**Two `matches` disciplines.** `ApprovedModification.matches`
(content-prefix) and `ApprovedModificationAt.matches` (per-cell)
could collapse into the selective form with `indices := range`;
kept separate for now because the full-prefix form is what the
existing scenes and `approvedPolicy_soundForCE_weak_strong` consume.
Candidate follow-up to the context consolidation.

## Where the open problems live

| Open problem | Blocking layer | Recorded in |
|---|---|---|
| Whole-trace theorem for proof-bearing gates | 4 (needs a weak `all_tower_safe`) | `SCOPE.md` |
| Contextual β under `.lam` | 7 (needs Howe-style up-to-bisim, L4) | `SCOPE.md` |
| Derived (not assumed) gate-swap soundness | 6 | `SCOPE.md` |
