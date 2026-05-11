# DESIGN_PROOF.md — proof-based admission

The design for proof-based admission: extend lean-sage's admission gate
to accept *per-modification soundness proofs* alongside the proposed
mutation, so that admission is "kernel type-checks this proof" rather
than "the mutation matches a structural shape with a meta-theorem
attached."

This document scopes the architectural change, names the load-bearing
pieces, and flags the open work. Proof-based admission is purely
additive on top of the structural-policy world (the `multnExactPolicy`
family); both admission paths coexist in the same `PolicyTable`.

## Status (as of 2026-05-10)

Most of the design has shipped. See [`TUTORIAL.md`](TUTORIAL.md) for
a hands-on walkthrough.

| Item | Status |
|---|---|
| `ApprovedModification` structure | shipped |
| `approvedPolicy` runtime policy | shipped |
| `CE_weak_strong` (the proof-based predicate) | shipped |
| `approvedPolicy_soundForCE_weak_strong` (headline soundness) | proved |
| Identity demos (vacuous + closure) | shipped |
| **Multn approval (worked example)** | **proved sorry-free** |
| W1 (existential equational defeat) | **proved** (baseline-policy form) |
| Parameterized W1 (under `[approvedPolicy approvals]`) | deferred — needs `NoSet` policy-independence lemma |
| Scene A (end-to-end with multn) | partial — `multnApproval` constructs + matches verified in `ProofBasedSmoke.lean` Scene 3 |
| Scene B (custom non-multn) | deferred |
| Scene C (compile-time refusal) | deferred |
| W2 / W3 | out of scope; future work |

All deferred items have file/line pointers and effort estimates in
`LeanBlack/ProofBased.lean`'s docstrings and the *Open work* section
below.

## Design (original — most of which has shipped)

## Why

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
*(modification, proof-of-CE_weak)*; the kernel type-checks the proof.
Modifications need no pre-registered policy. Structural policies stay
useful as **proof templates** (amortizing per-shape proofs across many
admissions), but they are no longer the only admission path.

This is the "proof-theoretic" tier of the keynote's assurance lattice,
realized concretely.

## What proof-based admission claims

1. **CE_weak as a standalone Lean predicate.** Extract the
   conservative-extension-under-bisimulation property from its current
   per-policy formulation in `Policies.lean` into a uniform predicate
   `CE_weak_holds : MutationCtx → Val → Val → Prop` (working name)
   statable for any candidate modification.
2. **A proof-bearing admission record.** `ApprovedModification`
   (working name) bundles a target, a new value, and a Lean term of
   type `CE_weak_holds ctx oldVal newVal`. Construction requires the
   proof; the kernel type-checks it.
3. **A runtime policy that admits exactly approved modifications.**
   `approvedPolicy` (working name) admits a `.set` iff it matches an
   `ApprovedModification` in scope. Composes with the existing
   `BlackPolicy` interface — no change to `Black.lean`'s `.set` rule.
4. **A pathway for hand-written modifications.** Two or three example
   modifications shipped with their hand-written CE_weak proofs:
   - `multn` (proof reuses the existing
     `multnExact_soundForCE_first_install_tower`);
   - one or two further modifications not matching any structural
     policy in the table, with their own bespoke proofs.
5. **The disaster demo, sharpened.** A modification *without* a valid
   proof (e.g. replacing `base-apply` with `fun _ _ => 0`) cannot be
   constructed as an `ApprovedModification` — the soundness field
   either has the wrong type or requires `sorry`. The build refuses.
6. **W1 (existential equational-theory defeat) as a target theorem.**
   The proof-based hypothesis makes W1 directly tractable: "under
   any modification admitted via the proof-based path, no context
   distinguishes a β-redex from its contractum" — because the proof
   *is* the hypothesis the W1 argument needs. The case-by-case lift
   from operational to universal that's hard with structural-only
   admission falls out here.

## Architecture

```
lean-sage/
├── LeanBlack/
│   ├── Black.lean             # UNCHANGED — Val, Expr, .set rule, MutationCtx
│   ├── Tower.lean             # UNCHANGED — tower mechanics
│   ├── Eval.lean              # UNCHANGED — tower-indexed eval
│   ├── Bisim.lean             # UNCHANGED — ValVis, ValVis_weak, frame_tower
│   ├── Frame.lean             # UNCHANGED — shift_respect, framing infrastructure
│   ├── Soundness.lean         # UNCHANGED — TowerCE, SafeEvolution, eval_tower_safe
│   ├── Policies.lean          # REFACTOR — extract CE_weak_holds as standalone predicate;
│   │                          # existing multnExactPolicy + theorem become a worked example
│   │                          # of constructing a proof for the proof-bearing API
│   └── ProofBased.lean        # NEW — ApprovedModification, approvedPolicy,
│                              # installApproved API
├── Demos.lean                 # UPDATED — adds proof-bearing demo scenes
├── Smoke.lean                 # UPDATED — adds proof-bearing smoke
└── DESIGN_PROOF.md            # this file
```

## The new types

```lean
namespace LeanBlack

/-- CE_weak as a uniform predicate on (context, old value, new value).
This is the semantic property a proof-bearing admission must witness.
Spelled out so it does not bake in install-protocol specifics from
`InstallFacts`/`RuntimeWF`; those become *sufficient conditions*
provable for specific shapes, not part of the predicate. -/
def CE_weak_holds (ctx : MutationCtx) (oldVal newVal : Val) : Prop :=
  ∀ fuel ptable op operands metaEnv s r s',
    callAsBaseApply fuel ptable oldVal op operands metaEnv s = some (r, s') →
    ∃ fuel' s'' r',
      callAsBaseApply fuel' ptable newVal op operands metaEnv s = some (r', s'') ∧
      ValVis_weak r r' s'.heap s''.heap ∧
      HeapValid s''.heap ∧ s.heap.length ≤ s''.heap.length

/-- A modification admitted via proof-bearing admission. The `proof`
field is the load-bearing certificate: Lean's type checker refuses
construction without a valid term of the soundness type. -/
structure ApprovedModification where
  target  : String
  ctx     : MutationCtx
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak_holds ctx oldVal newVal

/-- A runtime policy that admits a `.set` iff it matches an approved
modification in scope. -/
def approvedPolicy (approvals : List ApprovedModification) : BlackPolicy :=
  fun ctx oldVal newVal =>
    approvals.any fun am =>
      am.target == ctx.target && /* equality checks on ctx, oldVal, newVal */ ...

end LeanBlack
```

Notes:
- `CE_weak_holds`'s exact form is the technical refactor work. It must
  be statable in a way that's both *uniform across modifications* and
  *provable* from the lemmas Bisim/Frame/Policies already establish.
- `approvedPolicy` is just a structural policy that happens to enumerate
  approvals. The `BlackPolicy` interface is unchanged; this is one new
  entry in the verified table.
- `ApprovedModification.proof` is in `Prop`; equality of the proof
  doesn't matter for admission, only its *existence*.

## What changes in `Policies.lean`

Today `Policies.lean` defines:

- `BlackPolicy.SoundForCE_weak` — a per-policy predicate (the policy
  is sound for CE_weak).
- `multnExactPolicy` — a specific structural policy.
- `multnExact_soundForCE_first_install_tower` — a theorem stating
  this specific policy is sound, *under install-protocol side
  conditions* bundled in `InstallFacts` and `RuntimeWF`.

The refactor:

1. **Lift `CE_weak_holds` to a `(ctx, oldVal, newVal)` predicate** (not
   parameterized by a policy). The current `SoundForCE_weak` predicate
   becomes "for every `.set` this policy admits, `CE_weak_holds`
   holds for the corresponding mutation."
2. **Rewrite `multnExact_soundForCE_first_install_tower`** to conclude
   `CE_weak_holds ctx .builtinBaseApply newClosure` (rather than the
   per-policy form). The hypothesis side stays unchanged; only the
   conclusion shape changes.
3. **Build the multn-shape proof in the proof-bearing form**: given a
   closure `v` matching multn-shape and the install-protocol facts
   (`InstallFacts`, `RuntimeWF`, deep-validity, shift-respect — all
   already in `Policies.lean`), construct
   `proof : CE_weak_holds ctx .builtinBaseApply v`. This is the
   reusable proof template for any multn-shape admission.

After the refactor, `multnExactPolicy` and the structural-policy table
are still around as a fast path, but each is a *function from
structural admission to `CE_weak_holds` proof*, not an opaque
soundness theorem.

## Demos

Three scenes in `Demos.lean`:

### Scene A — proof-bearing multn

Construct an `ApprovedModification` for multn by invoking the
multn-shape proof template. Install `approvedPolicy [multnApproval]`.
Run a program that does `(em (set! base-apply <multn>))`. The
runtime gate admits because the modification matches the approval,
which exists because the kernel accepted its proof.

### Scene B — proof-bearing custom modification

A modification that does *not* match `multnExactPolicy` (e.g. extends
`base-apply` to handle a new tagged value, or implements a different
gimmick). The proposer writes the soundness proof by hand. Construct
an `ApprovedModification` from it. Install and run. Admits.

### Scene C — refusal at compile time

A modification that does *not* preserve CE_weak (e.g.
`fun _ _ => 0`). The proposer cannot construct an `ApprovedModification`
without `sorry`, because the soundness type is unprovable. The build
fails on uncommenting. The disaster demo lives at the level of "this
file doesn't compile," not "this run gives the wrong answer."

## What this gets the keynote

- **The "proof-theoretic" gate tier is concrete.** The runtime check
  is structural (matches an approval); the *admission of approvals*
  goes through Lean's kernel type-checking the proof. This is exactly
  what the keynote's assurance-lattice column means by
  "proof-theoretic."
- **The disaster demo is sharper.** With structural-only admission,
  the disaster is "without `multnExactPolicy`, a bad mod gets
  through" — but the policy world is the safe one. With proof-based
  admission, the disaster is "without a valid proof, the modification
  literally won't compile." The failure mode is at the build, not at
  runtime.
- **W1 becomes provable.** The universal-quantification W1 says ∃
  non-α terms no context distinguishes under any CE_weak-sound
  admission. The proof-based hypothesis *is* the universal: every
  admission carries a CE_weak proof; therefore every admission
  preserves β-behavior; therefore no context built from admitted
  modifications distinguishes a β-redex from its contractum. This is
  the path that structural-only admission couldn't take.

## Open work, in order

1. **Refactor `CE_weak_holds` to a uniform `(ctx, old, new)`
   predicate.** Engineering, ~1–2 days.
2. **Port `multnExact_soundForCE_first_install_tower` to conclude the
   new predicate.** Light; mostly threading through the existing
   proof. ~1 day.
3. **Implement `ApprovedModification` + `approvedPolicy`.** Small,
   structural. ~half a day.
4. **Scene A.** ~half a day (mostly putting together existing pieces).
5. **Scene B.** The hard part — a bespoke modification with a
   bespoke proof. ~2–3 days depending on the modification chosen.
   Recommend something narrow: a new tag handled at apply, or a
   closure that wraps existing dispatch.
6. **Scene C.** Trivial once Scene A works; just attempt construction
   and watch it fail.
7. **W1.** State and prove. The proof should be a few pages of Lean
   once the architecture is in place; the load-bearing fact is
   "every admitted modification preserves β by hypothesis."

Total: 1–2 focused weeks. Substantially less than the LLM-cascade
path; LLM proposer can be a later v3 reusing this architecture.

## What proof-based admission does NOT claim

- **W2 (βη ⊆ ≃_obs).** The βη induction is open; W1 doesn't
  generalize to W2 for free.
- **W3 (lattice monotonicity).** Comparing different proof-based
  admission paths is its own problem; not addressed.
- **LLM proposer.** Future work; the architecture supports it (the
  LLM ships the proof along with the modification), but the current
  implementation is purely manual.
- **A cleaner statement of `CE_weak_holds`.** The proposed form above
  is a starting point; finding the right uniform formulation is part
  of the refactor work. The actual landed predicate is named
  `CE_weak_strong` and lives in `LeanBlack/ProofBased.lean`.
