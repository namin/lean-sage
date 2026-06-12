import LeanBlack.Soundness
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.Compose
import LeanBlack.IdentityDelegate
import LeanBlack.ContextualBetaPure
import LeanBlack.GovChain

/-!
# Public — entry-point exposing the headline API

`import LeanBlack.Public` brings the artifact's public surface into
scope. Use this if you're reading the artifact to verify the
abstract's claim; use the underlying modules if you're hacking on
internals.

## The seven headline theorems

| Theorem (qualified name)                            | What it says                                                       |
|-----------------------------------------------------|--------------------------------------------------------------------|
| `eval_tower_safe`                                   | Safety: substrate stays CE-coherent under any reflective program.  |
| `multnExact_soundForCE_first_install_tower`         | Worked example: multn at first install conservatively extends.     |
| `safeEvolution_necessary`                           | Necessity: without the gate, CE fails (concrete counterexample).   |
| `LeanBlack.wand_defeated_existential_gated_beta`    | β-equivalence survives gated reflection (Wand defeat, convergent). |
| `LeanBlack.approvedPolicy_soundForCE_weak_strong`   | Proof-based admission soundness: every approval is CE.             |
| `LeanBlack.CE_weak_strong_trans`                    | Composition: chained admissions yield CE substrates.               |
| `contextual_beta_pure`                              | Contextual β: redex ≡ contractum in *every* `Expr` position except under `.lam` (pure operand, pure pre-hole siblings, `em`-nesting to any depth in the tower bound). |

The supporting program-level forms of `contextual_beta_pure`
(`ContextualBetaPure.lean`):

- `contextual_beta_at_start` — the equivalence run at level 0 from
  the canonical pre-materialized tower `buildTower (emDepth C + 2)`,
  under any level-0 policy, policy table, and env (`initTower`
  materializes only level 0, so the hole's level+1 condition needs
  the pre-materialized start tower);
- `wand_beta_ctx_pure_at_start` — the specific Wand pair
  `((λx. x) 0)` / `(let x 0 x)`, contextually quantified.

The root-namespace theorems are historical (`Soundness.lean` and
`Policies.lean` predate the `LeanBlack` namespace convention); the
contextual-β layer follows `ContextualBeta.lean` in the root
namespace.

After `open LeanBlack` (or just `import LeanBlack.Public; open LeanBlack`),
all seven are accessible by their short names.

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

Supporting layer for #6 (`GovChain.lean`, all in the `LeanBlack`
namespace) — composition across *real* admission sequences:

- `ApprovedModificationAt` / `approvedPolicyAt` — proof-bearing
  admission in *selective* form: the certificate pins only the cells
  it reads (`CE_weak_strong_at`), so it stays consumable after later
  admissions rewrite the `base-apply` cell. Full-prefix approvals
  from successive admissions can never fire at a common test state,
  so this is what lets `CE_weak_strong_trans`-style composition
  apply to an actual chain at all;
- `chain_CE` — n-link composition of selective certificates at
  per-link snapshots;
- `GovReach` / `govReach_CE` — a packaged corollary quantifying
  over interleavings of admissions and gate replacements. Read its
  assumptions before citing it: each replacement gate's soundness
  is a hypothesis of the step (discharged by construction only for
  kernel-built `approvedPolicyAt` gates), and the chain's firing
  condition at a test state (`CertsFire`) is a per-instance
  obligation. It is an admission-event-level statement, not a
  whole-program-trace theorem — see `SCOPE.md`;
- `eval_set_inverts` / `eval_installPolicy_inverts` and their
  corollaries — mechanized inversions of the two mutation clauses,
  tying abstract steps to the runtime per step.

## Contextual-β support types (root namespace)

| Name                  | Purpose                                              |
|-----------------------|------------------------------------------------------|
| `LeanBlack.Ctx` + `Ctx.plug_cong_master` | THE context language and THE master congruence (sibling-class- and predicate-family-parameterized); tiers are instantiations. |
| `BuiltinReadyN d`     | Depth-indexed readiness (margin `d` of `em`-nesting). |
| `BuiltinReadyP d`     | `BuiltinReadyN d` bundled with heap purity.          |
| `LeanBlack.StateExtends` | Structural state evolution under pure evaluation. |

## What's NOT exported

Internal lemmas (`frame_tower`, `shift_respect`, `applyDirect_heap_extend_weak`,
`materialize_shift_commutes`, value-bisim machinery, etc.) stay in
their underlying modules. The only remaining contextual-β exclusion
is the `.lam` position (contexts under a binder), which needs an
up-to-bisim equivalence (`ValVis`-style) rather than outcome
equality; see `SCOPE.md`.

For a walkthrough, see [`TUTORIAL.md`](../TUTORIAL.md). For full file
descriptions, see [`README.md`](../README.md).
-/
