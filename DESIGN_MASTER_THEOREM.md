# The guarded-extension master theorem

`LeanBlack/GuardedExt.lean` · `LeanBlack/GuardedExtApproval.lean` · `DemoGuarded.lean`

## What changed

Before this layer, lean-sage's gate admitted exactly one reflective
modification with a kernel certificate: the multn wrapper, through the
bespoke theorem `multnExact_soundForCE_first_install_tower`
(`Policies.lean`). Admitting any *other* modification meant writing
another theorem of that size. The proposal surface was, in practice,
closed.

This layer generalizes the multn certificate from one wrapper to a
*family*, proved sound once. A new modification in the family costs a
`GuardSpec` — two small lemmas — instead of a new headline theorem.
The proposal surface is now open, and the per-proposal proof is small
enough to ask a proposer (human or LLM) to produce live.

## The family

A **guarded extension wrapper** replaces `base-apply` with

```scheme
(λ (op args). (if (<g> op) <behavior> (orig op args)))
```

where `g` is a recognizer primitive (`num?`, `bool?`, `null?`, …) and
`<behavior>` is an **arbitrary** expression. Constructed by
`guardedExtBody g t`; admitted by the decidable policy
`guardedExtPolicy g`, which checks the exact shape and that the
captured env binds `orig` to the current base-apply and `g` to the
recognizer primitive (mirroring `multnExactPolicy`).

## The split: proved once vs. per proposal

**Proved once** (`guardedExt_soundForCE_first_install_tower`): any
admitted wrapper in the family whose guard carries a `GuardSpec`
conservatively extends the builtin base-apply (`CE_weak` conclusion,
first install). The proof generalizes the multn proof's structure:

- *Guard-true case*: vacuous. `spec.misses` says the baseline is
  undefined wherever the guard fires, and CE only constrains calls the
  old semantics answered. This is why `<behavior>` is unconstrained —
  the new behavior lives entirely on territory the baseline never
  claimed.
- *Guard-false case*: the wrapper body traces to the delegating
  `orig` call (`guardedExt_closure_body_unfolds`, generalizing
  `multn_closure_body_unfolds`), and the heap-extension framing lemma
  `applyDirect_heap_extend_weak` (`Frame.lean`) reproduces the old
  result. This lemma was already wrapper-independent; nothing new was
  needed under it.

**Per proposal** (`GuardSpec g`): two lemmas about the guard —

```
total  : ∀ op, ∃ b, applyPrim g [op] = some (.bool b)
misses : ∀ op, applyPrim g [op] = some (.bool true) →
         ∀ fuel ptable level operands T,
           applyDirect fuel ptable level op operands T = none
```

plus two trivial binder disequalities. `guardSpec_numq`,
`guardSpec_boolq`, `guardSpec_nullq` are each ~20 lines of case
analysis. That is the entire marginal cost of opening a new region of
undefined territory to modification.

## The boundary is provable, not just unprovable

`misses` is the load-bearing obligation, and it draws a line *inside*
the family:

- `no_guardSpec_primq`: no `GuardSpec "prim?"` exists. A
  `prim?`-guarded wrapper would intercept every primitive application
  — `(+ 1 2)` would flow into `<behavior>` — and the baseline is
  defined there. Kernel theorem, witnessed by `(+ 1 2) ⇒ 3`.
- `no_guardSpec_closureq`: likewise for `closure?`, which would
  hijack ordinary function application.

So a refusal of these proposals is not "the proposer failed to find a
proof"; it is "the kernel holds a proof that no certificate exists."
This is the family-level analog of lean-gate's `malicious_not_CE`.

## Subsumption

`multn_admits_guardedExt` + `guardSpec_numq`: everything
`multnExactPolicy` admits, `guardedExtPolicy "num?"` admits, and the
master theorem re-derives the multn certificate. The bespoke multn
theorem still stands (nothing was deleted); it is now an instance.

## Approval packaging

`GuardedExtApproval.lean` mirrors the multn approval layer
(`HeapAgree.lean`): `guardedExtApproval_at_proof` produces the
selective certificate pinning exactly the two heap cells the proof
reads (the closure's captured `orig` and guard bindings), and
`guardedExtApproval` widens it to the `CE_weak_strong` form that
`approvedPolicy` consumes. An `ApprovedModification` for any family
member is one function call from an admission fact and a `GuardSpec`.

## The demo (`lake exe demoGuarded`)

One master theorem, two admissions, one provable refusal:

- **Booleans as selectors** (guard `bool?`): `(true 1 2)` is stuck
  under the baseline; after the gated install, `(true 1 2) ⇒ 1`,
  `(false 1 2) ⇒ 2`, and `(+ 1 2)` is still `3`.
- **multn** (guard `num?`): `(2 3 4) ⇒ 24` — through the same
  theorem, not its own.
- **The hijacker** (guard `closure?`, behavior "return 666"): the
  gated `set!` returns `false`, and `((λx. x+1) 41) ⇒ 42` still
  works. The refusal is backed by `no_guardSpec_closureq`.

Wrappers are built from source through `guardedExtBody`; the admission
closures and heaps are derived by running `eval` on the source
(`probeOf`), as in `Demo.lean` — no hand-reconstructed environments.

## Scope, stated plainly

- **First install only.** Like the multn theorem, the master theorem
  is stated for `oldVal = .builtinBaseApply`. Chained installs
  compose via `CE_weak_strong_trans` (see
  `ProofCarryingAccumulation.lean` for the existing chained example);
  a chained *family* theorem is not proved here.
- **Extensions of undefined territory only.** The family cannot
  express behavior-preserving rewrites of *defined* territory
  (optimizations). That corner requires the open logical relation for
  evolving semantics — see `CtxEquiv.lean`'s obstructions. The line
  between the two is exactly the `misses` obligation.
- **Guards are unary recognizer prims applied to `op`.** Guards over
  operand lists, or compound guards, would need the trace lemma
  re-generalized (mechanical, not conceptual).
- **`native_decide` appears in `DemoGuarded.lean` only**, for the two
  admission facts (`boolSel_admits`, `multnM_admits`) — Bool shape
  checks on concrete probe values, matching `Demo.lean`'s existing
  practice. The kernel does not reduce `eval`'s mutual recursion, so
  kernel `decide` is unavailable for eval-derived values. Everything
  semantic — master theorem, GuardSpecs, impossibility results,
  approval layer — is kernel-only, pinned in `AxiomAudit.lean` to
  `[propext, Classical.choice, Quot.sound]`.

## Why this matters for the pattern

The gate's economics depend on checking being cheaper than producing.
Before: producing a certificate meant a bespoke ~500-line soundness
theorem per modification — the asymmetry pointed the wrong way, and
the only realized proposals were the ones the artifact's authors
proved by hand. After: the expensive proof is amortized into the
class, the per-proposal obligation is two small lemmas, and the
refusals have kernel-checked impossibility backing. A proposer can now
be wild — including an LLM emitting `(guard, behavior, GuardSpec)`
triples — while the gate stays narrow. Wiring such a proposer against
this interface is the natural next step; the interface it must hit is
exactly `GuardSpec g` plus a source-level wrapper.
