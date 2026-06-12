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

**Context-language tiers — RESOLVED.** There is now exactly one
context language (`Ctx`, `Ctx.lean`) and one master congruence
(`Ctx.plug_cong_master`, `CtxPure.lean`), parameterized by a sibling
class `S : Expr → Prop` and a predicate family indexed by remaining
`em`-depth. The historical tiers are instantiations: the trivial
family with `S := True` gives the unconditional strict track
(`Ctx.plug_cong`); `S := fun _ => False` gives the easy tier
(`Ctx.plug_cong_at_easy` — contexts with no pre-hole siblings, no
hypotheses at all); `S := (Pure · = true)` with the `BuiltinReadyP`
family gives contextual β (`contextual_beta_pure`). The former
`SimpleCtx`/`EasyCtx`/`WideCtx`/`PureCtx` types, their four master
lemmas, and the thirteen strict per-constructor congruence lemmas
(~1,400 lines) are deleted. Side conditions on a context are
`lamFree` (the one open position), `emDepth` (the family index), and
`sidesOK S`; the `em`-descent hypothesis is demanded only of
contexts that actually `em`-nest.

**Two `matches` disciplines — RESOLVED (by theorem).** The
full-prefix admission discipline is *provably* the
`indices := List.range` instance of the selective one, at every
layer (`GovChain.lean`): relation
(`HeapPrefix_iff_agree_range`), certificate
(`CE_weak_strong_iff_at_range`), matcher
(`ApprovedModification.toAt_matches` — Boolean equality, so the two
gates agree decision-for-decision), and gate
(`approvedPolicy_eq_at` : `approvedPolicy ams =
approvedPolicyAt (ams.map toAt)`, pointwise as functions). The two
structures are kept for their distinct *statement* roles
(single-admission vs. chain link), but they are one discipline, and
the kernel has checked that.

With both items resolved, the remaining complexity in this repo is
the theorem-forced kind catalogued above.

## Where the open problems live

| Open problem | Blocking layer | Recorded in |
|---|---|---|
| Whole-trace theorem for proof-bearing gates | 4 (needs a weak `all_tower_safe`) | `SCOPE.md` |
| Contextual β under `.lam` | 7 (needs Howe-style up-to-bisim, L4) | `SCOPE.md` |
| Derived (not assumed) gate-swap soundness | 6 | `SCOPE.md` |
