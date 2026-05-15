# SCOPE — what lean-sage claims, and what it does not

This document spells out the precise scope of the artifact's headline
results — a single place to check what is mechanized, what is
operational-only, and what is deliberately not claimed. For the
headline theorem list and entry points, see [`README.md`](README.md).
For architectural rationale, see [`DESIGN.md`](DESIGN.md) and
[`DESIGN_PROOF.md`](DESIGN_PROOF.md).

## What is proved

lean-sage mechanizes proof-carrying reflective modification of a
Black-style reflective tower. Six theorems form the public surface
(all in [`LeanBlack/Public.lean`](LeanBlack/Public.lean)):

| Theorem | Where | What it gives |
|---|---|---|
| `eval_tower_safe` | `LeanBlack/Soundness.lean` | Substrate stays CE-coherent under any reflective program. |
| `multnExact_soundForCE_first_install_tower` | `LeanBlack/Policies.lean` | Worked example: multn at first install on `bbApply` is a conservative extension. |
| `safeEvolution_necessary` | `LeanBlack/Soundness.lean` | Necessity: without the gate, CE fails (concrete counterexample). |
| `LeanBlack.wand_defeated_existential_gated_beta` | `LeanBlack/ProofBased.lean` | β-equivalence survives gated reflection (convergent / top-level). |
| `LeanBlack.approvedPolicy_soundForCE_weak_strong` | `LeanBlack/ProofBased.lean` | Proof-based admission soundness: every approval is CE. |
| `LeanBlack.CE_weak_strong_trans` | `LeanBlack/Compose.lean` | Composition: chained admissions yield CE substrates. |

All theorems are kernel-checked with no `sorry`, `admit`, or `axiom`.
Toolchain: `leanprover/lean4:v4.20.0`.

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

It is **not** the full contextual statement
`∀ C, evalProgram (C[M]) = evalProgram (C[N])`.

The contextual lift is partial / in-progress. The pieces live in
[`LeanBlack/EvalFuelMono.lean`](LeanBlack/EvalFuelMono.lean),
[`LeanBlack/Ctx.lean`](LeanBlack/Ctx.lean),
[`LeanBlack/ContextualBeta.lean`](LeanBlack/ContextualBeta.lean), and
[`LeanBlack/HeapAgree.lean`](LeanBlack/HeapAgree.lean). The clean
half (`EasyCtx`, `WideCtx`, `SimpleCtx`) covers every `Expr`-tree
position except `.lam`. `contextual_beta_easy` in `Ctx.lean` is the
contextually-quantified β statement for the easy-context
sub-language. What remains is threading the L4 parallel-bisim
invariant through `eval` to lift to arbitrary contexts.

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

## Reflective depth: what is NOT claimed

The public theorem surface does not currently expose a recursive
proof-based theorem for installing new gate policies through higher
gates. In other words: although `(installPolicy n)` operationally
exists and is reachable through `(em ...)`-chains, there is no
public lemma quantifying over an arbitrary chain of higher-gate
proof-based admissions of new policies. The headline theorems
quantify over a fixed `verifiedTable`, and the
"policy at level *N* is itself reflectively modifiable" axis from the
reasonable-reflection abstract is captured operationally by
multi-level `set!`-on-`base-apply` plus `installPolicy`, not by a
recursive proof-based policy-installation theorem.

This is a deliberate scoping decision, not an oversight: the recursive
proof-based policy-installation theorem would compose
`approvedPolicy_soundForCE_weak_strong` across a quantified chain of
higher gates, which is future work.

## Composition: first install + identity-delegate, not arbitrary chain

The structural multn soundness theorem
`multnExact_soundForCE_first_install_tower` covers
`oldVal = .builtinBaseApply` — the first-install case. Composition
across admissions is supplied separately by `CE_weak_strong_trans`
(in `LeanBlack/Compose.lean`) together with a concrete second link
`identityDelegateApproval` (in `LeanBlack/IdentityDelegate.lean`).
`ProofBasedSmoke` Scene 10 exercises the full chain
`bbApply → multn → identity-delegate-on-multn` end-to-end.

Stronger non-trivial wrappers (`multn → logging-multn`, etc.) would
need their own `CE_weak_strong` proofs but slot into the same chain
machinery.

## Summary table — paper claim ↔ artifact backing

| Paper-level claim | Artifact backing |
|---|---|
| Substrate is always a conservative extension of the base under reflective modification. | `eval_tower_safe` (`CE_weak`, with multi-level reflection through `(em ...)`-chains). |
| Modifications carry kernel-checked CE evidence. | `ApprovedModification.proof : CE_weak_strong …`; `approvedPolicy_soundForCE_weak_strong`. |
| The gate is load-bearing — without it, CE fails. | `safeEvolution_necessary` + `ProofBasedSmoke` Scene 4. |
| β-equivalence survives gated reflection. | `wand_defeated_existential_gated_beta` (convergent / top-level). Contextual β is partial — see above. |
| Modifications compose. | `CE_weak_strong_trans` + `identityDelegateApproval` + `ProofBasedSmoke` Scene 10. |
| Reflective depth: per-level modification, governed. | Multi-level `set! base-apply` proved sound via `eval_tower_safe`; `installPolicy` operational; no public recursive proof-based policy-installation theorem. |
