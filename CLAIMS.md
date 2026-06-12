# CLAIMS — the ledger

Every claim the artifact makes, classified by the strength of its
backing. This is the audit trail for "what exactly is proved":
[`SCOPE.md`](SCOPE.md) gives each result's precise qualifiers; this
file gives the one-screen classification.

## Legend

| Mark | Meaning |
|------|---------|
| **T** | Kernel-checked theorem over quantified statements. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), enforced in CI by [`LeanBlack/AxiomAudit.lean`](LeanBlack/AxiomAudit.lean). |
| **T•** | Kernel-checked theorem *instantiated on concrete runtime data*; closed-term side conditions discharged by `native_decide` (adds the trusted-compiler axiom, confined to the smoke layer). |
| **D** | Demonstrated by a runtime scene (`Smoke` / `Demos` / `ProofBasedSmoke`); no theorem. |
| **—** | Not mechanized. Stated as future work or out of scope. |

## The ledger

| Claim | Status | Backing | Qualifiers |
|---|---|---|---|
| Substrate stays CE-coherent under any reflective program | **T** | `eval_tower_safe` | Strictly-sound policy tables (`SafeEvolution`); `CE_weak` relation. |
| multn conservatively extends the baseline | **T** | `multnExact_soundForCE_first_install_tower`; proof-bearing forms `multnApproval`, `multnApprovalAt` | First install on `bbApply`; `CE_weak` / `CE_weak_strong`. |
| Without the gate, CE fails | **T** | `safeEvolution_necessary` | Concrete counterexample (diverging wrapper). |
| β-equivalence survives gated reflection (top level) | **T** | `wand_defeated_existential_gated_beta` | Convergent / top-level; specific witness pair. |
| β-equivalence survives gated reflection (contextual) | **T** | `contextual_beta_pure`, `contextual_beta_at_start` | Every `Expr` position **except under `.lam`**; pure operand and pure pre-hole siblings; `BuiltinReadyP` precondition (discharged at the canonical start tower). |
| Every proof-based admission carries a CE certificate | **T** | `approvedPolicy_soundForCE_weak_strong`; selective: `approvedPolicyAt_SoundForCEAt` | By construction — the record's `proof` field. |
| Two admissions compose at a common snapshot | **T** | `CE_weak_strong_trans` | Common reference heap — **never satisfied by two real installs** (next row). |
| Admissions compose on *real* chains | **T** + **T•** | `chain_CE` (**T**); instantiated on the worked chain by `chainCertsFire_post_chain` + `chainCertsAt_chainOk` (**T•**); impossibility of the full-prefix route: `fullPrefix_certs_conflict` (**T•**) | General chains need per-link *selective* certificates with cells disjoint from later installs; `ValValid` components are hypotheses of the firing theorem. |
| Gate replacement composes with admissions | **T**, with assumptions | `govReach_CE` (+ `GovReach`, `govReach_sound`) | Replacement-gate soundness is a *hypothesis* per step — discharged by construction only for kernel-built `approvedPolicyAt` gates. Admission-event level. |
| Committed runtime `.set` = one admission step | **T** | `eval_set_inverts`, `eval_set_commit_govStep` | Per-step bridge, not a trace theorem. |
| Committed runtime `installPolicy` = one gate-swap step | **T** | `eval_installPolicy_inverts`, `eval_installPolicy_regate_govStep` | Requires table-entry soundness. |
| Pure evaluation only extends the tower state | **T** | `pureEvalExt` / `eval_pure_extends` | `Pure` expressions over a `PureHeap`. |
| Multi-level reflective modification (`(em (em …))`) | **T** + **D** | `eval_tower_safe` covers `.set` at any depth; `Smoke` 3, `Demos` 6/11, `ProofBasedSmoke` 7/9 | Theorem under strictly-sound tables; scenes under proof-based gates. |
| Per-level policy installation, reflectively reached | **D** + **T** (per-step) | `Smoke` 4, `Demos` 11; `eval_installPolicy_inverts` | Whole-trace proof-based version: see gaps. |
| Selective vs. full-prefix contrast at runtime | **D** | `ProofBasedSmoke` Scene 11 | Mirrors `fullPrefix_certs_conflict` / `chainCertsFire_post_chain`. |

## The gaps (deliberate, documented)

| Missing | Why | Where stated |
|---|---|---|
| Whole-program-trace guarantee for proof-bearing gates | Proof-bearing gates are `CE_weak_strong`-sound and provably cannot be strictly `CE`-sound (multn is the counterexample), so they cannot enter the `eval_tower_safe` induction; a weak-relation analog of `all_tower_safe` is the target. | `SCOPE.md`, "Reflective depth: what is NOT claimed" |
| Contextual β under `.lam` | Closures embed bodies syntactically; needs an up-to-bisim outcome relation (Howe-style) threaded by the L4 parallel-bisim induction. | `SCOPE.md`, β section |
| Derived (not assumed) gate-swap soundness | `govReach_CE`'s `regate` assumes soundness; "checked by the gate one level up" is realized as kernel-by-construction, not derived. | `SCOPE.md` |
| LLM proposer | Architecture supports it; implementation manual. | `DESIGN_PROOF.md` |

## Axiom posture

- **Library (`LeanBlack/`)**: `propext`, `Classical.choice`, `Quot.sound`
  only — enforced by `LeanBlack/AxiomAudit.lean` (`#guard_msgs` on
  `#print axioms`; the build fails if any footprint changes). The
  `sorry` grep alone cannot detect tactic-introduced axioms; an
  earlier `native_decide` in the two Wand witnesses was found by
  exactly this audit and replaced with `decide +kernel`.
- **Smoke layer (`ProofBasedSmoke.lean`)**: concrete-data side
  conditions (admission booleans, cell lookups, heap agreements) use
  `native_decide` (trusted compiler). The theorems they feed are
  marked **T•** above.
