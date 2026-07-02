# The LLM proposer against the guarded-extension gate

Design for the three-tier extension of lean-sage that puts all three
vertices of the pattern — proposer, gate, substrate — on the flagship:
an LLM proposing modifications to the genuinely reflective substrate,
admitted only with kernel certificates assembled through the master
theorem (`GuardedExt.lean`, see `DESIGN_MASTER_THEOREM.md`).

Status ledger at the bottom. Companion harness lessons come from
sc-mini's strict-gate episode (its `WRITEUP.md` §Reproducing): show
the model the exact Lean names, reject `sorry`, retry with the
checker's error text.

## Why this is now cheap

The master theorem split certificate cost into

- **class-level** (proved once): any guarded-extension wrapper whose
  guard carries a `GuardSpec` is a conservative extension;
- **per-proposal**: the `GuardSpec` itself — two ~20-line lemmas
  (`total`: the guard answers on every operator; `misses`: where the
  guard fires, the baseline is undefined).

Per-proposal obligations of this size are exactly what sc-mini
demonstrated an LLM can produce under a sorry-rejecting check with
error-feedback retries. Nothing the LLM emits is trusted: the wrapper
is source, the lemmas are checked by the kernel, and the admission
fact is a decidable shape check.

## Tier 1 — widen the certifiable territory (Lean; no LLM)

Add recognizer primitives for the value classes that had none:

- `sym?` (`applyPrim_symQ`) and `pair?` (`applyPrim_pairQ`) in
  `Black.lean`, appended to the `applyPrim` chain;
- bound in every level env (`primPairs` in `Tower.lean`, appended so
  existing heap indices are unchanged; `primPairs_length` 13→15,
  `freshLevelEnv_heap_length` +14→+16);
- bisimulation support in `Bisim.lean` (`applyPrim_symQ_bisim`,
  `applyPrim_pairQ_bisim`, dispatcher cases in `applyPrim_bisim` and
  `shift_applyPrim`).

**Deliberately absent: `GuardSpec "sym?"` and `GuardSpec "pair?"`.**
Both are provable (symbols and pairs are baseline-undefined as
operators), and leaving them unproved is the point — they are the
live per-proposal obligations for Tier 3. Without this tier, every
certifiable guard in the language already carried a pre-proved spec,
so a "proposer" would have nothing to prove.

## The booth is in Lean

The proposer and gate driver live *in the system's own language*:
`Booth.lean` (executable `lake exe booth`) and `LeanBlack/Bedrock.lean`
(the `aws bedrock-runtime` client, ported from lean-green — the
artifact that first ran an LLM proposer from inside Lean). No external
scripting layer: the whole loop — prompt, Bedrock call, file
generation, `lake env lean` check, sorry-scan, retry — is Lean IO.
This is deliberate for the thesis: the system that reflects also
proposes and gates its own reflection.

```
lake exe booth check <guard> <behavior> [--spec s|--spec-file f] [--test "e ~> v"]…
lake exe booth llm ["brief"]
```

## Tier 2 — the proposal booth (`booth check`; no LLM)

Pipeline per proposal:

```
input:   guard name g, behavior expression t (source),
         optional GuardSpec proof script for g
generate: Proposal_<n>.lean — a DemoGuarded-shaped instantiation:
         wrapper := .lam ["op","args"] (guardedExtBody g t)
         probe → closure/heap; admission fact; certificate via
         guardedExtApproval <spec> …; gate; beat programs
check:   lake env lean Proposal_<n>.lean   (prebuilt .oleans ⇒ seconds)
         acceptance = exit 0 AND no `sorry` in diagnostics
run:     the generated executable beats; report admitted/refused
```

Verdict reporting distinguishes the three refusal strengths:

1. **elaboration failure** — the proposal or its proof script doesn't
   check (retryable);
2. **no certificate offered** — well-formed wrapper, no GuardSpec
   supplied and none pre-proved (the doubling case);
3. **no certificate exists** — the guard is `prim?` or `closure?`:
   report the impossibility theorem by name
   (`no_guardSpec_primq` / `no_guardSpec_closureq`).

For guards with pre-proved specs (`num?`, `bool?`, `null?`) the booth
supplies the spec itself; the proposer only picks behavior. For
`sym?`/`pair?` the proposal must include the proof script.

Implementation note: the generated file mirrors `DemoGuarded.lean`
with the admission fact via `native_decide` (matching existing
practice; the kernel does not reduce `eval`'s mutual recursion — see
`DESIGN_MASTER_THEOREM.md` §Scope). The *GuardSpec lemmas* are
kernel-checked; the sorry-scan applies to the whole file.

## Tier 3 — the LLM in the booth (`booth llm`)

Claude (Bedrock, via `LeanBlack/Bedrock.lean`) drives the booth from
inside Lean:

```
prompt:   the language's Expr/Val grammar; the family shape;
          the exact primed Lean names (embedding shown, per the
          sc-mini lesson); the GuardSpec obligations verbatim;
          previously admitted/refused proposals as context
proposes: (g, t, proof script for GuardSpec g when unproved)
loop:     booth checks → on failure, feed the full Lean error back,
          retry (budget ~3, per sc-mini's landing)
```

Trust story, stated once: the LLM is outside the TCB entirely. It can
emit nonsense (elaboration failure), unproved claims (`sorry` —
rejected by scan), or true-but-useless lemmas (admitted into context,
never matching). The only path to an installed semantic change runs
through the kernel-checked master theorem. The booth's transcript is
the archive: every proposal, verdict, and certificate hash.

## What this does NOT claim

- No chained installs: the master theorem is first-install; one
  wrapper per session (stacking = the "stack theorem", future work).
- No new-guard *semantics*: proposals pick from the language's
  recognizers; they do not add primitives (that would change
  `applyPrim` and the bisimulation layer — a language change, not a
  reflective one).
- The booth's admission fact uses `native_decide` (demo-layer glue,
  as in `Demo.lean`); the semantic theorems remain kernel-only and
  axiom-audited.

## Status

- [x] Tier 1: prims + env + bisimulation support
- [x] `GuardSpec "sym?"` / `GuardSpec "pair?"` intentionally unproved
- [x] Tier 2: booth driver — **in Lean** (`Booth.lean`, `lake exe booth
      check`; records in `Proposals/`)
- [x] Tier 3: LLM proposer — **in Lean** (`lake exe booth llm`, via
      `LeanBlack/Bedrock.lean`)
- [ ] Stretch: stack theorem (disjoint-guard chained installs)

First live three-vertex run driven entirely from inside Lean
(2026-07-02, `lake exe booth llm`): asked for "make pairs applicable."
Attempt #1 refused (elaboration failure). Attempt #2 **admitted**:
behavior `.app [.primApp (.var "car") [.var "op"], .var "args"]` (a
pair applies its car), with a clean kernel-checked `GuardSpec "pair?"`
supplied by the model — see `Proposals/Proposal_3.lean` for the
admission record. The model's own
prediction for its test was wrong (informational; tests don't gate
admission), which is itself the thesis: the proposer's beliefs about
its proposal are untrusted; only the certificate is.
