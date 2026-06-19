# SCOPE — what lean-sage claims, and what it does not

This document spells out the precise scope of the artifact's headline
results — a single place to check what is mechanized, what is
operational-only, and what is deliberately not claimed. For the
headline theorem list and entry points, see [`README.md`](README.md).
For architectural rationale, see [`DESIGN.md`](DESIGN.md) and
[`DESIGN_PROOF.md`](DESIGN_PROOF.md).

## What is proved

lean-sage mechanizes proof-carrying reflective modification of a
Black-style reflective tower. Seven theorems form the public surface
(all in [`LeanBlack/Public.lean`](LeanBlack/Public.lean)):

| Theorem | Where | What it gives |
|---|---|---|
| `eval_tower_safe` | `LeanBlack/Soundness.lean` | Substrate stays CE-coherent under any reflective program. |
| `multnExact_soundForCE_first_install_tower` | `LeanBlack/Policies.lean` | Worked example: multn at first install on `bbApply` is a conservative extension. |
| `safeEvolution_necessary` | `LeanBlack/Soundness.lean` | Necessity: without the gate, CE fails (concrete counterexample). |
| `LeanBlack.wand_defeated_existential_gated_beta` | `LeanBlack/ProofBased.lean` | β-equivalence survives gated reflection (convergent / top-level). |
| `LeanBlack.approvedPolicy_soundForCE_weak_strong` | `LeanBlack/ProofBased.lean` | Proof-based admission soundness: every approval is CE. |
| `LeanBlack.CE_weak_strong_trans` | `LeanBlack/Compose.lean` | Composition: chained admissions yield CE substrates. |
| `contextual_beta_pure` | `LeanBlack/ContextualBetaPure.lean` | Contextual β: redex ≡ contractum in every `Expr` position except under `.lam` (see scope below). |

In support of the composition theorem (`CE_weak_strong_trans`),
[`LeanBlack/GovChain.lean`](LeanBlack/GovChain.lean) adds the
selective admission layer and chain composition — see "Reflective
depth" below for what it does and does not establish.

All theorems are kernel-checked with no `sorry` or `admit`, on the
standard axioms only (`propext` / `Classical.choice` / `Quot.sound`),
CI-enforced by [`LeanBlack/AxiomAudit.lean`](LeanBlack/AxiomAudit.lean).
Toolchain: `leanprover/lean4:v4.29.1`. For the claim-by-claim
classification (kernel theorem / instantiated on concrete data /
runtime demo / not mechanized), see [`CLAIMS.md`](CLAIMS.md).

## Why the headline relation is `CE_weak` / `CE_weak_strong`, not strict `CE`

The conservative-extension predicate lean-sage uses is `CE_weak` (and
its proof-bearing extension `CE_weak_strong`), not a strict relation
requiring Lean-equal captured environments on closures.

The reason is the closure case of the multn proof. multn is a closure
whose captured `orig` env binding refers, by index, into a heap that
has been extended by the `.set` itself. The post-admission heap and
the pre-admission heap therefore differ at the `base-apply` cell, so
any predicate that demands strict equality of captured environments
cannot be discharged for the multn admission.

CakeML-style value bisimulation (Kumar 2016 §3) solves this: closures
are related pointwise through their captured environments under a
depth-indexed bisim relation `ValVis_aux` / `ValVis_weak`. `CE_weak`
asks for bisim-related, not Lean-equal, captured envs. This is the
relation the soundness theorems conclude in, and the relation the
`Compose.lean` transitivity argument operates on.

A strict-CE variant would force lean-sage to either (a) materialize
the post-admission heap inside the proof obligation (which makes the
predicate non-compositional) or (b) abandon multn as the worked
example. Neither is desirable.

## What is proved about β-equivalence

`wand_defeated_existential_gated_beta` is the **convergent** form: it
states that there exist `M ≠ N` (specifically, `((λx. x) 0)` and `0`)
that evaluate to the same value at the top level under any list of
proof-bearing approvals. This is the value-level existential defeat
of Wand 1998 that the predecessor lean-green already had, lifted to
the proof-based admission setting.

**The contextual lift is now proved for every `Expr` position except
under `.lam`.** `contextual_beta_pure`
([`LeanBlack/ContextualBetaPure.lean`](LeanBlack/ContextualBetaPure.lean)):
for any lam-free context `C : Ctx` (all thirteen hole-bearing
positions of the `Expr` tree except `.lam`'s body — including `.set`
value positions, `.letE` bodies, and `.em`-nesting to any depth
within the tower bound), any binder `x`, any body, and any *pure*
operand `v_expr`:

    C[(λx. body) v_expr]  ≡  C[let x = v_expr in body]

(same convergent outcomes), at every state satisfying
`BuiltinReadyP (emDepth C)`. The program-level corollary
`contextual_beta_at_start` instantiates this at the canonical
pre-materialized start tower `buildTower (emDepth C + 2)` under any
level-0 policy, any policy table, and any env — closing the
lazy-materialization gap (`initTower` materializes only level 0, so
the hole's level+1 condition fails at the bare start state).
`wand_beta_ctx_pure_at_start` is the Wand-pair instance.

The precise scope qualifiers:

- **Pure operand and pure pre-hole siblings.** `v_expr` and the
  context's sub-expressions evaluated *before* the hole must be
  `Pure` (no `.set` / `.installPolicy`); post-hole siblings and
  context nodes themselves (e.g. a surrounding `.set`) are
  unconstrained. This is what guarantees the L1 conditions survive
  to the hole: pure evaluation only *extends* the state
  (`LeanBlack/PureExt.lean`).
- **`BuiltinReadyP d` precondition.** Depth margin
  `level + d + 1 < maxDepth`, levels materialized past
  `level + d + 1`, builtin `base-apply` cells in the window
  `[level, level + d]`, and a pure heap. The start-tower corollary
  discharges all of it by construction.
- **`.lam` exclusion.** Contexts placing the hole under a binder
  are not covered: closures embed bodies syntactically, so
  outcome-equality congruence fails; the `.lam` case needs a
  `ValVis`-style relation refined to permit β-related closure
  bodies (Howe-style), threaded through `eval` by the L4
  parallel-bisim induction. This is the one remaining piece of the
  full contextual statement.

The supporting machinery:
[`LeanBlack/EvalFuelMono.lean`](LeanBlack/EvalFuelMono.lean) (fuel
monotonicity), [`LeanBlack/Ctx.lean`](LeanBlack/Ctx.lean) (the one
context language, observational equivalence, per-constructor
congruences),
[`LeanBlack/PureExt.lean`](LeanBlack/PureExt.lean) (`StateExtends`
under pure evaluation, the preservation engine),
[`LeanBlack/CtxPure.lean`](LeanBlack/CtxPure.lean) (the one master
congruence `Ctx.plug_cong_master`, parameterized by sibling class
and predicate family; the strict and easy tiers are its
instantiations `Ctx.plug_cong` / `Ctx.plug_cong_at_easy`), and
[`LeanBlack/ContextualBeta.lean`](LeanBlack/ContextualBeta.lean) /
[`LeanBlack/HeapAgree.lean`](LeanBlack/HeapAgree.lean) (the β
base-case witness and the post-admission CE bridges).

## Reflective depth: what is claimed

lean-sage mechanizes **multi-level reflective modification of
`base-apply`**. `(em (em (set! base-apply ...)))` modifies level
*N* + 1's apply rule from level *N*, and `eval_tower_safe` propagates
the per-modification gate through arbitrary reflective depth. This is
exercised by `Smoke` Scene 3, `Demos` Scenes 6 and 11, and
`ProofBasedSmoke` Scenes 7 and 9.

lean-sage also includes **operational per-level policy
installation** via `(installPolicy n)`, exercised by `Smoke` Scene 4
and `Demos` Scene 11.

On the proof-based side,
[`LeanBlack/GovChain.lean`](LeanBlack/GovChain.lean) strengthens the
*composition* story so it applies to real admission sequences:

- **Selective admission** (`ApprovedModificationAt` /
  `approvedPolicyAt`): the certificate pins only the cells it reads
  (`CE_weak_strong_at`). This matters because full-prefix
  certificates from successive admissions can never fire at a
  common test state — each admission rewrites the `base-apply`
  cell — so without selectivity, `CE_weak_strong_trans` cannot be
  applied to an actual chain of two or more installs.
- **Chain composition** (`chain_CE`): n links at per-link
  snapshots compose, at any test state agreeing with each link's
  cells.
- **Runtime inversions**: every committed `.set` factors as one
  admission step (`eval_set_inverts` / `eval_set_commit_govStep`);
  every committed `installPolicy` selects a table entry
  (`eval_installPolicy_inverts`).
- A packaged corollary (`GovReach` / `govReach_CE`) quantifies over
  interleavings of admissions and gate replacements.

## Reflective depth: what is NOT claimed

The "gate is itself modifiable through the gate one level up" axis
remains backed **operationally** (multi-level `set!` +
`installPolicy`, with `eval_tower_safe` covering strictly-sound
tables), **not** by a strong proof-based theorem. Precisely:

- `govReach_CE`'s `regate` rule *assumes* each replacement gate is
  sound; the assumption is discharged by construction only for
  kernel-built `approvedPolicyAt` gates
  (`approvedPolicyAt_SoundForCEAt` — no such gate exists without
  kernel-checked certificates). The theorem does not derive gate
  soundness from a gated check one level up.
- The chain's firing condition at a test state (`CertsFire`) is a
  per-instance obligation, discharged for the concrete links here
  by the fresh-cells discipline, not in general.
- There is no whole-program-trace theorem for proof-bearing tables.
  The obstruction is principled: proof-bearing gates are sound for
  `CE_weak_strong` (weak bisimilar results, content-prefix-bound
  certificates) and cannot be sound for the strict `CE` that the
  `eval_tower_safe` induction threads — the multn worked example
  itself is the counterexample. A weak-relation analog of the full
  `all_tower_safe` induction is the real target and remains future
  work.

## Composition: how the chain actually composes

The structural multn soundness theorem
`multnExact_soundForCE_first_install_tower` covers
`oldVal = .builtinBaseApply` — the first-install case.
`ProofBasedSmoke` Scene 10 exercises the two-install chain
`bbApply → multn → identity-delegate-on-multn` end-to-end at
runtime.

For the *composed* guarantee on that chain, `CE_weak_strong_trans`
(in `LeanBlack/Compose.lean`) alone does not suffice: it composes
two certificates at a common reference heap, and the two
full-prefix approvals' snapshots provably conflict at the
`base-apply` cell (`fullPrefix_certs_conflict`,
`ProofBasedSmoke.lean`) — no test state extends both. The composed
guarantee is delivered by the selective layer
(`LeanBlack/GovChain.lean`): the selective re-renders of the same
two approvals pin only the cells their proofs read, the chain's
firing condition holds at the post-chain heap and any extension
(`chainCertsFire_post_chain`), and `chain_CE` then gives the
composed conservative extension `bbApply → identity-delegate`.
`ProofBasedSmoke` Scene 11 runs the contrast. (Scene-level concrete
side conditions use `native_decide`, per that file's house style;
the `GovChain.lean` machinery is axiom-clean.)

Stronger non-trivial wrappers (`multn → logging-multn`, etc.) would
need their own `CE_weak_strong_at` proofs but slot into the same
chain machinery.

## Summary table — paper claim ↔ artifact backing

| Paper-level claim | Artifact backing |
|---|---|
| Substrate is always a conservative extension of the base under reflective modification. | `eval_tower_safe` (`CE_weak`, with multi-level reflection through `(em ...)`-chains). |
| Modifications carry kernel-checked CE evidence. | `ApprovedModification.proof : CE_weak_strong …`; `approvedPolicy_soundForCE_weak_strong`. |
| The gate is load-bearing — without it, CE fails. | `safeEvolution_necessary` + `ProofBasedSmoke` Scene 4. |
| β-equivalence survives gated reflection. | `wand_defeated_existential_gated_beta` (convergent / top-level) + `contextual_beta_pure` (every `Expr` position except under `.lam`; pure operand and pure pre-hole siblings — see above). |
| Modifications compose. | `CE_weak_strong_trans` + `identityDelegateApproval` + `ProofBasedSmoke` Scene 10. |
| Reflective depth: per-level modification, governed. | Multi-level `set! base-apply` proved sound via `eval_tower_safe`; `installPolicy` operational. Proof-based admission chains compose across kernel-built gate swaps at the admission-event level (`GovChain.lean`); a strong proof-based gate-modifies-gate theorem (whole-program-trace, derived gate soundness) remains future work — see above. |
