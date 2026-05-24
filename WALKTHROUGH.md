# WALKTHROUGH — a guided scan of the source

This is a **reading map**, not a tutorial. The aim is a feel for the
artifact in ~15 minutes: follow the links, glance at each landmark, move
on. Every link jumps to a specific definition by line number.

- Want to *build* an approval yourself? → [`TUTORIAL.md`](TUTORIAL.md).
- Want the *claim ↔ theorem* table? → [`README.md`](README.md).
- Want to know what is / isn't claimed? → [`SCOPE.md`](SCOPE.md).

Line numbers are current as of this commit; if they drift, the symbol
names in `code font` are the stable anchors (grep for them).

---

## The one idea, in 30 seconds

A modification to the interpreter's `base-apply` rule is admitted only if
it carries a kernel-checked proof of conservative extension. That proof
*is* the admission certificate:

→ [`ApprovedModification`](LeanBlack/ProofBased.lean#L242) — a struct with
a `proof : CE_weak_strong …` field. **No value of this type exists unless
the Lean kernel type-checks the proof.** The constructor is the gate.

→ [`approvedPolicy`](LeanBlack/ProofBased.lean#L268) — turns a list of
approvals into an ordinary `BlackPolicy`. The runtime treats it like any
other policy; the difference is only in *construction*.

Everything else is what makes that honest.

---

## Tier 1 — the gate and the proof it rests on

Read these five top-to-bottom; they are the spine.

| Stop | Where | What you're looking at |
|------|-------|------------------------|
| 1 | [`CE_weak_strong`](LeanBlack/ProofBased.lean#L192) | The evidence predicate. "Every baseline success is preserved" — plus the Deep/Shift premises the multn proof actually needs (§4 of TUTORIAL explains why). |
| 2 | [`ApprovedModification`](LeanBlack/ProofBased.lean#L242) | The certificate. The `proof` field is the load-bearing kernel admission point. |
| 3 | [`approvedPolicy`](LeanBlack/ProofBased.lean#L268) | The runtime gate, built from a list of certificates. Same type as `acceptAllPolicy` / `multnExactPolicy`. |
| 4 | [`approvedPolicy_soundForCE_weak_strong`](LeanBlack/ProofBased.lean#L328) | The headline soundness: every admission under the gate has a `CE_weak_strong` witness. |
| 5 | [`CE_weak_strong_trans`](LeanBlack/Compose.lean#L138) | Composition — chained admissions stay CE-extending. The *global* guarantee across a sequence of admissions. |

## Tier 2 — the worked example: admit one, refuse one

| Stop | Where | What you're looking at |
|------|-------|------------------------|
| 6 | [`multnApproval`](LeanBlack/ProofBased.lean#L1837) | The headline admission. A `CE_weak_strong` proof for the multn closure, built by invoking [`multnExact_soundForCE_first_install_tower`](LeanBlack/Policies.lean#L561). Section preamble at [L1684](LeanBlack/ProofBased.lean#L1684). |
| 7 | [`wand_defeated_existential_gated_beta`](LeanBlack/ProofBased.lean#L1671) | Wand 1998, defeated (convergent form): `((λx. x) 0)` and `0` converge to the same value under *any* list of gated approvals. |
| 8 | [`safeEvolution_necessary`](LeanBlack/Soundness.lean#L1939) | The converse — *without* the gate (`acceptAll`), a malicious constant-zero mod breaks `(+ 1 2)`. The gate is load-bearing. |
| 9 | [`eval_tower_safe`](LeanBlack/Soundness.lean#L1781) | Safety through reflection: evaluating *any* expression — including `(em …)` and `(set! base-apply …)` at any depth — preserves the CE invariant. |

## Tier 3 — see it actually run

Runnable scenes (`lake exe proofBasedSmoke`). These are where the gate
fires against real tower evaluation.

| Scene | Where | What it shows |
|-------|-------|---------------|
| 3 | [Scene 3](ProofBasedSmoke.lean#L177) | `multnApproval` constructs and the gate admits/refuses on a hand-crafted ctx. |
| 4 | [Scene 4](ProofBasedSmoke.lean#L236) | **The disaster demo** — a doubling wrapper is *refused*: no CE proof exists, so no approval can be built. |
| 8 | [Scene 8](ProofBasedSmoke.lean#L557) | End-to-end: gate installed, `(set! base-apply multn)` admitted, `(2 3 4) ⇒ 24` at level 1. |
| 9 | [Scene 9](ProofBasedSmoke.lean#L639) | Same, one level deeper — `(em (2 3 4)) ⇒ 24` dispatched through level 2's now-`multn` base-apply. |
| 10 | [Scene 10](ProofBasedSmoke.lean#L683) | The composed chain `bbApply → multn → identity-delegate` — both admit, a wrong-shape mod at step 2 is refused. |

---

## The substrate underneath (for context)

You don't need these to grasp the gate, but they answer "a gate over
*what*?"

- [`Val`](LeanBlack/Black.lean#L16) / [`Expr`](LeanBlack/Black.lean#L27) /
  [`Env`](LeanBlack/Black.lean#L43) / [`Heap`](LeanBlack/Black.lean#L49) —
  the Black-faithful core: heap, closures, `set!`.
- [`BlackPolicy`](LeanBlack/Black.lean#L233) — `MutationCtx → Val → Val →
  Bool`. *This* is the interface `approvedPolicy` implements.
- [`TowerState`](LeanBlack/Tower.lean#L56) /
  [`buildTower`](LeanBlack/Tower.lean#L107) — the tower of levels and its
  on-demand materialization.
- [`eval`](LeanBlack/Eval.lean#L49) /
  [`applyDirect`](LeanBlack/Eval.lean#L193) /
  [`evalProgram`](LeanBlack/Eval.lean#L220) — the tower-indexed evaluator.
  `applyDirect` is where `base-apply` is consulted.

## The CE engine (deep machinery — skip on a first pass)

The CakeML-style value bisimulation that makes the CE proofs go through.
Large files; the named entry points:

- [`ValVis_aux`](LeanBlack/Bisim.lean#L55) /
  [`ValVis_weak`](LeanBlack/Bisim.lean#L170) — the bisimulation relating
  closures pointwise through captured environments.
- [`ValVis_aux_weak_trans`](LeanBlack/Compose.lean#L27) — depth-indexed
  transitivity; what `CE_weak_strong_trans` (stop 5) rests on.
- [`LeanBlack/Frame.lean`](LeanBlack/Frame.lean) — cross-side framing, the
  technical engine. Start at
  [`PolicyTableRespectsBisimT`](LeanBlack/Frame.lean#L72).

---

## Where to enter, by intent

| If you want to… | Open |
|-----------------|------|
| See the whole public surface on one screen | [`LeanBlack/Public.lean`](LeanBlack/Public.lean) |
| Read the gate in isolation | [`LeanBlack/ProofBased.lean`](LeanBlack/ProofBased.lean) (sectioned for top-to-bottom reading; see TUTORIAL §13) |
| Watch it run | `lake exe proofBasedSmoke` → [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) |
| Build your own approval | [`TUTORIAL.md`](TUTORIAL.md) §5–§7 |

## Rough sizes (so nothing surprises you)

```
small / read in full   Public.lean (55)  IdentityDelegate.lean (233)
                       Compose.lean (179)  Black.lean (449)
medium                 ProofBased.lean (1898)  Soundness.lean (1995)
large / skim only      Bisim.lean (4505)  Frame.lean (4944)
in progress (contextual-β, not public)
                       Ctx.lean  ContextualBeta.lean  HeapAgree.lean  EvalFuelMono.lean
```
