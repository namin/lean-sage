# Proof-carrying accumulation in `lean-sage`

This addendum is a keynote-facing front door for material that is already
present in `ProofBasedSmoke.lean` and `LeanBlack/GovChain.lean`.

The story is:

```text
builtin base-apply
  -- π₁ : CE builtin multn -->
multn base-apply
  -- π₂ : CE multn delegate(multn) -->
delegating base-apply
```

The first certificate adds a new behavior:

```scheme
(2 3 4)  ==>  24
```

while preserving old behavior:

```scheme
(+ 1 2)  ==>  3
```

The second certificate is the accumulation point: it is not merely
baseline-relative. It is a certificate from the currently installed
`multn` dispatcher to a later dispatcher that delegates to `multn`.
So the learned behavior has become part of the future obligation.

## Files involved

Existing source files:

- `ProofBasedSmoke.lean`
  - Scene 8: end-to-end multn install at level 1.
  - Scene 10: composed runtime admissions `bbApply → multn → identity-delegate`.
  - Scene 11: selective chain certificates.
- `LeanBlack/GovChain.lean`
  - `AdmissionCert`
  - `ChainOk`
  - `CertsFire`
  - `chain_CE`
  - `ApprovedModificationAt`
  - `approvedPolicyAt`
  - `GovReach`
  - `govReach_CE`

New front-door file:

- `ProofCarryingAccumulation.lean`
  - packages the existing examples as a two-commit proof-carrying log;
  - prints a keynote-sized run;
  - exposes the slide theorem `commitLog_chainOk`.

## Command

```bash
lake env lean ProofCarryingAccumulation.lean
```

Expected story-level output:

```text
before commit:        (2 3 4)  => <none>
after commit 1:       (2 3 4)  => num(24)
after commit 1:       (+ 1 2)  => num(3)
gate admits commit 1?              true
gate admits commit 2?              true
gate refuses bad commit 2?         false
after commit 2:       (2 3 4)  => num(24)
after commit 2:       (+ 1 2)  => num(3)
full-prefix snapshot still valid?  false
selective proof cells survive?     true
```

The last two lines are intentionally asymmetric: the full-prefix
snapshot is no longer valid because the `base-apply` cell changes;
the selective discipline survives because it pins only cells the proof
actually reads.

## Slide slogan

> The first proof adds behavior. The second proof makes that behavior
> part of the future contract.

## Honest scope

This is not a new whole-program trace theorem. It packages existing
admission-event and chain-composition machinery into the accumulation
story. The remaining open theorem is the fully general trace theorem
for arbitrary proof-bearing weak-CE reflective executions.
