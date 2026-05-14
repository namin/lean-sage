# DESIGN_PROOF.md — proof-based admission

This document explains the rationale for the proof-based admission
layer (`CE_weak_strong` / `ApprovedModification` / `approvedPolicy`)
on top of the substrate (whose architecture is in
[`DESIGN.md`](DESIGN.md)). Proof-based admission is purely additive
on top of the structural-policy world (the `multnExactPolicy`
family); both admission paths coexist in the same `PolicyTable`.

For the current state of what's mechanized and the headline theorem
list, see [`README.md`](README.md). For a hands-on walkthrough, see
[`TUTORIAL.md`](TUTORIAL.md).

## Why proof-based admission?

The structural-policy admission discipline (`multnExactPolicy` and
friends) makes a `BlackPolicy` a Boolean function `MutationCtx → Val
→ Val → Bool`, and each policy in the verified table is paired with a
separate soundness theorem (`multnExact_soundForCE_first_install_tower`)
proving that *admissions by that policy* are CE_weak-conservative. To
admit a modification the proposer must find a pre-existing policy with
a soundness theorem whose structural shape matches.

This is "semantic at the meta level, structural at runtime." It
delivers operational soundness per admission, but it does not deliver
**deep reflection without syntactic restriction**: every admissible
shape has to be foreseen and codified by a structural policy author.
Ad-hoc modifications are unadmissible.

Proof-bearing admission inverts this. The proposer ships
*(modification, proof-of-CE_weak_strong)*; the kernel type-checks the
proof. Modifications need no pre-registered policy. Structural
policies stay useful as **proof templates** (amortizing per-shape
proofs across many admissions), but they are no longer the only
admission path.

This is the "proof-theoretic" tier of the keynote's assurance lattice,
realized concretely.

## The architecture in three definitions

```lean
namespace LeanBlack

/-- CE_weak_strong: the proof-bearing soundness predicate. -/
def CE_weak_strong (level : Nat) (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    HeapPrefix h_ref T.heap →
    HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
    ValValid old T.heap → ValValid new T.heap →
    -- ... validity / bisim / shift premises (full list in ProofBased.lean) ...
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length

/-- A modification admitted via proof-bearing admission. The `proof`
    field is the load-bearing certificate: Lean's type checker refuses
    construction without a valid term of the soundness type. -/
structure ApprovedModification where
  level   : Nat
  heap    : Heap
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak_strong level heap oldVal newVal

/-- A runtime policy that admits a `.set` iff it matches an approved
    modification in scope. -/
def approvedPolicy (approvals : List ApprovedModification) : BlackPolicy :=
  fun ctx oldVal newVal => approvals.any (·.matches ctx oldVal newVal)

end LeanBlack
```

The key division of labor:

- **`CE_weak_strong`** is a uniform predicate on `(level, h_ref,
  old, new)`. It does not bake in install-protocol specifics
  (`InstallFacts`/`RuntimeWF`); those become *sufficient conditions*
  provable for specific shapes, not part of the predicate. The exact
  premise list lives in `ProofBased.lean`.

- **`ApprovedModification.proof`** is in `Prop` — equality of the
  proof doesn't matter for admission, only its *existence*. Lean's
  kernel ensures no `ApprovedModification` value can be constructed
  without a valid proof.

- **`approvedPolicy`** is just a `BlackPolicy`. From the runtime's
  perspective, it's interchangeable with `acceptAllPolicy` or
  `multnExactPolicy`. The difference is *how the boolean was
  computed* — backed by a proof, even though the runtime itself
  doesn't consult the proof.

## Relationship to the structural-policy path

Both paths live in the same `PolicyTable`. A proposer chooses:

1. **Structural** (`multnExactPolicy`): use a pre-registered policy
   whose soundness has been proved once for all admissions of that
   shape. Fast path. Restricted to pre-foreseen shapes.

2. **Proof-bearing** (`approvedPolicy approvals`): supply the proof
   yourself. Per-modification cost; no shape restriction.

`structural_policy_yields_approval` (in `ProofBased.lean`) is the
bridge: any modification admitted by a CE-weak-sound structural
policy can be lifted into an `ApprovedModification`. So the structural
path is a proof-amortization layer on top of the proof-bearing
discipline, not an alternative to it.

## Composition across admissions

`approvedPolicy_soundForCE_weak_strong` (in `ProofBased.lean`) is
per-admission. The *global* guarantee the LICS abstract names — "the
substrate is always a conservative extension of the base, across
composed admissions" — needs `CE_weak_strong_trans` (in
`Compose.lean`): chained CE-extending admissions compose into a
CE-extending substrate.

The chain is concretely realized in `IdentityDelegate.lean` +
`ProofBasedSmoke.lean` Scene 10: `bbApply → multn →
identity-delegate-on-multn`, both `.set` operations admitted by a
single `approvedPolicy` with two approvals.

This is where the proof-based admission discipline delivers what
structural-only admission can't: a chain of arbitrary CE-extending
modifications, each with its own proof, gated uniformly.

## Disaster demo

A modification that does *not* preserve CE_weak_strong (e.g. a
doubling wrapper, where `(+ 1 2)` becomes `6` instead of `3`)
cannot be constructed as an `ApprovedModification` — the
`CE_weak_strong` proof field has no inhabitant. The build refuses,
not at runtime, but at proof-construction time.

`ProofBasedSmoke.lean` Scene 4 demonstrates this: the doubling
wrapper is refused at admission (the `approvedPolicy` returns
`false`); under the un-governed `acceptAll` path, the same wrapper
breaks `(+ 1 2)`. The disaster is real and the gate is genuinely
load-bearing — see also `safeEvolution_necessary` in `Soundness.lean`
for the meta-level counterexample.

## Wand defeat (W1)

The "Wand 1998" thread says: in an ungated reflective system,
β-equivalence collapses to α-equivalence (everything is
distinguishable). The proof-based discipline defeats this for the
gated case.

`wand_defeated_existential_gated_beta` in `ProofBased.lean` proves
the convergent form: `((λx.x) 0)` and `0` evaluate to the same value
under `[approvedPolicy approvals]` for any list of approvals.
β-equivalence survives gated reflection.

The bridge is `AllPureIndep`: `eval` is policy-table-independent for
`Pure` expressions (no `.set`, no `.installPolicy`). β-redexes are
`Pure`; therefore the choice of policy table doesn't affect their
evaluation; therefore the β-redex and its contractum converge to the
same value under any policy table.

W2 (βη ⊆ ≃_obs) and W3 (lattice monotonicity comparing different
proof-based admission paths) are out of scope. The contextual lift
of W1 — `∀ context C, evalProgram (C[M]) = evalProgram (C[N])` for
β-equivalent `M`, `N` — is in progress: `EasyCtx` /
`WideCtx` cover most positions; `.lam` is deferred for closure-
syntactic refinement reasons. See `Ctx.lean` /
`ContextualBeta.lean` / `HeapAgree.lean` / `EvalFuelMono.lean`.

## What proof-based admission does NOT claim

- **Full contextual W1 (βη / contexts with `.lam`).** In progress;
  not in the public API yet.

- **W2 (βη ⊆ ≃_obs).** Out of scope. The βη induction is open.

- **W3 (lattice monotonicity).** Comparing different proof-based
  admission paths is its own problem; not addressed.

- **LLM proposer.** Future work. The architecture supports it (the
  LLM ships the proof along with the modification), but the current
  implementation is purely manual.

- **General multi-install for the *structural* path.** The
  `multnExact_soundForCE_first_install_tower` headline covers
  `oldVal = .builtinBaseApply`. The proof-based path handles
  composition via `CE_weak_strong_trans`; the structural variant
  would need either a tightened `multnExactPolicy` num-branch or new
  num-case trace lemmas.
