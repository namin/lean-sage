import LeanBlack.Soundness
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.Compose
import LeanBlack.IdentityDelegate

/-!
# Public — entry-point exposing the headline API

`import LeanBlack.Public` brings the artifact's public surface into
scope. Use this if you're reading the artifact to verify the
abstract's claim; use the underlying modules if you're hacking on
internals.

## The six headline theorems

| Theorem (qualified name)                            | What it says                                                       |
|-----------------------------------------------------|--------------------------------------------------------------------|
| `eval_tower_safe`                                   | Safety: substrate stays CE-coherent under any reflective program.  |
| `multnExact_soundForCE_first_install_tower`         | Worked example: multn at first install conservatively extends.     |
| `safeEvolution_necessary`                           | Necessity: without the gate, CE fails (concrete counterexample).   |
| `LeanBlack.wand_defeated_existential_gated_beta`    | β-equivalence survives gated reflection (Wand defeat, convergent). |
| `LeanBlack.approvedPolicy_soundForCE_weak_strong`   | Proof-based admission soundness: every approval is CE.             |
| `LeanBlack.CE_weak_strong_trans`                    | Composition: chained admissions yield CE substrates.               |

The first three live in the root namespace (historical, `Soundness.lean`
and `Policies.lean` predate the `LeanBlack` namespace convention).
The last three live in the `LeanBlack` namespace.

After `open LeanBlack` (or just `import LeanBlack.Public; open LeanBlack`),
all six are accessible by their short names.

## Public types and constructors (all in `LeanBlack` namespace)

| Name                                | Purpose                                            |
|-------------------------------------|----------------------------------------------------|
| `CE_weak_strong`                    | Conservative-extension predicate at the apply-rule level. |
| `ApprovedModification`              | Kernel-checked CE certificate.                     |
| `approvedPolicy`                    | Runtime gate built from a list of approvals.       |
| `multnApproval`                     | Multn approval template (first install on bbApply). |
| `identityApproval`                  | Identity approval (self-replacement, any Val).     |
| `numIdentityApproval`               | Identity at a `.num n` value (vacuous template).   |
| `identityDelegateApproval`          | Identity-delegate-on-closure (chain second link).  |

## What's NOT exported

Internal lemmas (`frame_tower`, `shift_respect`, `applyDirect_heap_extend_weak`,
`materialize_shift_commutes`, value-bisim machinery, etc.) stay in
their underlying modules. The contextual-β infrastructure (`Ctx.lean`,
`ContextualBeta.lean`, `HeapAgree.lean`, `EvalFuelMono.lean`) is
work-in-progress and not yet part of the public surface.

For a walkthrough, see [`TUTORIAL.md`](../TUTORIAL.md). For full file
descriptions, see [`README.md`](../README.md).
-/
