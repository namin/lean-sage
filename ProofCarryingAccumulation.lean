/-
  lean-sage addendum: ProofCarryingAccumulation

  This file is intentionally a *front door*, not new machinery.
  It imports the existing `ProofBasedSmoke` scenes and renames the
  load-bearing pieces into the keynote story:

    learn a behavior → certify it → commit it → preserve it later.

  Check directly with:

    lake env lean ProofCarryingAccumulation.lean

  It should not be imported by `LeanBlack.lean`: it depends on the
  smoke/demo file and is meant as a keynote-facing addendum.
-/

import ProofBasedSmoke

open LeanBlack

namespace ProofCarryingAccumulation

/-! ## 1. The commit log

`ProofBasedSmoke` already constructs two selective approvals:

* `runtimeMultnApprovalAtLevel1`:
    `bbApply → multn`, adding numeric application `(2 3 4) ↦ 24`;
* `runtimeIdentityDelegateApprovalAt`:
    `multn → identity-delegate-on-multn`, a later dispatcher that
    preserves the learned multn behavior by delegating to it.

Here we package them as a proof-carrying commit log. -/

abbrev Commit := AdmissionCert 1
abbrev CommitLog := List Commit

/-- Commit 1: learn numeric application. -/
def commit1_numericApplication : Commit :=
  runtimeMultnApprovalAtLevel1.toCert

/-- Commit 2: install a later dispatcher that preserves the learned one. -/
def commit2_delegateToLearnedDispatcher : Commit :=
  runtimeIdentityDelegateApprovalAt.toCert

/-- The keynote-sized proof-carrying log. -/
def commitLog : CommitLog :=
  [commit1_numericApplication, commit2_delegateToLearnedDispatcher]

/--
The two commits really form a certificate chain

  builtin base-apply → multn → identity-delegate-on-multn.

This is the compact theorem to put on a slide: the second proof does
not merely preserve the original baseline; it preserves the dispatcher
installed by the first proof.
-/
theorem commitLog_chainOk :
    ChainOk 1 commitLog .builtinBaseApply runtimeIdentityDelegateClosure :=
  chainCertsAt_chainOk

/-! ## 2. Runtime observations

These are executable observations for the keynote script. They are not
new proofs; they name the existing smoke-test scenes. -/

/-- Before committing multn, numeric application has no level-0 meaning. -/
def before_numericApplication : Option Val :=
  evalProgram fuel [] (.app [.num 2, .num 3, .num 4])

/-- After commit 1, `(2 3 4)` works at level 0. -/
def after_commit1_numericApplication : Option Val :=
  test_sceneA_compute

/-- Commit 1 also preserves ordinary arithmetic. -/
def after_commit1_plus : Option Val :=
  test_sceneA_preserves_plus

/-- The same gate admits the concrete first runtime mutation. -/
def gate_admits_commit1 : Bool :=
  test_chain_step1_admit

/-- The same gate admits the concrete second runtime mutation. -/
def gate_admits_commit2 : Bool :=
  test_chain_step2_admit

/-- The gate still refuses a wrong-shape/clobbering second mutation. -/
def gate_refuses_bad_commit2 : Bool :=
  test_chain_step2_refuses_doubling

/-! ## 3. A concrete two-commit run

The smoke file already proves the gate-level and chain-level facts.
For the keynote, it is useful to also have the actual two-commit
program in one place. -/

/-- The second reflective edit: capture the current `base-apply` as
`orig`, then install an identity delegate that calls `orig`. -/
def installIdentityDelegateOneUp : Expr :=
  .em <|
    .letE "orig" (.var "base-apply") <|
      .set "base-apply" identityDelegateLam

/-- A policy table whose only gate is the two-commit proof-based gate. -/
def twoCommitPolicyTable : PolicyTable :=
  [approvedPolicy chainApprovals]

/-- Run both commits, then use the final dispatcher on numeric application. -/
def after_commit2_numericApplication : Option Val :=
  evalProgram fuel twoCommitPolicyTable <|
    .seq [installApprovedAt1,
          installMultnOneUp,
          installIdentityDelegateOneUp,
          .app [.num 2, .num 3, .num 4]]

/-- Run both commits, then check old arithmetic still behaves as before. -/
def after_commit2_plus : Option Val :=
  evalProgram fuel twoCommitPolicyTable <|
    .seq [installApprovedAt1,
          installMultnOneUp,
          installIdentityDelegateOneUp,
          .app [.var "+", .num 1, .num 2]]

/-! ## 4. Why selective certificates matter

The full-prefix snapshots of the two ordinary approvals conflict:
commit 1's snapshot says cell 27 is `bbApply`; commit 2's snapshot
says the same cell is `multn`. So full-prefix composition is vacuous
on the real two-install chain.

The selective certificates pin only the cells the proof actually reads,
so those cells survive the updates to the `base-apply` cell. -/

theorem fullPrefixSnapshots_do_not_compose :
    ¬ ∃ h : Heap, HeapPrefix runtimeHeapLevel1 h ∧
                  HeapPrefix chainHeapAtStep2Admission h :=
  fullPrefix_certs_conflict

/-- The selective cells survive the mutation sequence. -/
def selective_cells_survive : Bool :=
  test_selective_cells_survive

/-- Is the full-prefix snapshot still valid after the first install?
It should be `false`: the `base-apply` cell changed. -/
def full_prefix_snapshot_still_valid : Bool :=
  test_fullprefix_snapshot_broken

/-! ## 5. Keynote-readable output

Running `lake env lean ProofCarryingAccumulation.lean` prints exactly
the story the slides need. -/

#eval s!"before commit:        (2 3 4)  => {shortRepr before_numericApplication}"
#eval s!"after commit 1:       (2 3 4)  => {shortRepr after_commit1_numericApplication}"
#eval s!"after commit 1:       (+ 1 2)  => {shortRepr after_commit1_plus}"
#eval s!"gate admits commit 1?              {gate_admits_commit1}"
#eval s!"gate admits commit 2?              {gate_admits_commit2}"
#eval s!"gate refuses bad commit 2?         {gate_refuses_bad_commit2}"
#eval s!"after commit 2:       (2 3 4)  => {shortRepr after_commit2_numericApplication}"
#eval s!"after commit 2:       (+ 1 2)  => {shortRepr after_commit2_plus}"
#eval s!"full-prefix snapshot still valid?  {full_prefix_snapshot_still_valid}"
#eval s!"selective proof cells survive?     {selective_cells_survive}"

end ProofCarryingAccumulation
