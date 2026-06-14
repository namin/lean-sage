# The reverse simulation: discharging `ReverseSimβ`

This file consolidates the **one remaining obligation** in lean-sage's conditional
ground-contextual β-equivalence under `.lam`: the *reverse* cross-side simulation
`ReverseSimβ`. Everything else in the chain is proved (`sorry`-free, axioms
⊆ `{propext, Classical.choice, Quot.sound}`). All names below are checked Lean
declarations in `LeanBlack/`.

## Where the reverse sits

The headline is a **conditional** ground-contextual equivalence of the β redex and
its contractum — conditional because the *unconditional* version is provably false:

- **Obstruction A** — `lam_EvalEquivAt_forces_empty` (`CtxEquiv.lean`): the fine
  `EvalEquivAt` congruence is *false* under `.lam` (closures capture bodies
  verbatim). Forces the coarse **ground** `CtxEquiv`.
- **Obstruction B** — `beta_not_unconditional_CtxEquiv` (`CtxEquiv.lean`): even
  ground `CtxEquiv` is false unconditionally (at the tower top the redex's gated
  apply cannot fire). Forces the **standard-gate / pure** side conditions.

`CtxEquiv` (`CtxEquiv.lean`) is an `↔` of `ObsConv`, so the `.lam` congruence needs
**both** observational refinements:

```
ObsConv (C.plug M) ↔ ObsConv (C.plug N)      -- M = redex, N = contractum, M →β N
```

| direction | bridge | status |
|---|---|---|
| `ObsConv (C.plug M) → ObsConv (C.plug N)` | `obsConv_refine_forward` | **proved** (via `frameβ_eval_FL`) |
| `ObsConv (C.plug N) → ObsConv (C.plug M)` | `obsConv_refine_backward` | **modulo `ReverseSimβ`** |

`obsConv_iff_beta` bundles the two. The forward fundamental lemma is the *complete*
`frameβ_tower : ∀ n, FrameStmtβP n` (`LamBetaReflect.lean`), instantiated
diagonally. The only hole is `ReverseSimβ`.

## The obligation, precisely

```lean
def ReverseSimβ : Prop :=
  ∀ (k : Nat) (pt : PolicyTable) (lvl : Nat) (ea eb : Expr)
    (va vb : Env) (Sa Sb : TowerState) (rb : Val) (Sb' : TowerState),
    BetaRel ea eb → Pure ea = true → PolicyTableRespectsBisimT pt →
    WFCtxTβ va vb Sa Sb lvl → BReady Sb →
    eval k pt lvl eb vb Sb = some (rb, Sb') →
    ∃ (k' : Nat) (ra : Val) (Sa' : TowerState),
      eval k' pt lvl ea va Sa = some (ra, Sa') ∧ ValVisβ ra rb Sa'.heap Sb'.heap
```

The **b-side drives** (its `eval` is given), the a-side is reconstructed. Note the
two distinguishing features versus the forward `FrameβEvalStmtWP`:

1. **`∃ k'` fuel.** β-expansion *adds* the redex's head+apply steps, so the redex
   needs strictly more fuel than its contractum (`app_lam_redex_min_fuel`: redex
   `≥ 3`; `eval_letE` = body+1; `eval_beta_builtin` = body+3). A same-fuel reverse
   is **false**. (This corrects the unsatisfiable shape the deprecated
   `obsConv_refine_of_FL_rev` carried.)
2. **`Pure ea`, not `Pure eb`** — the a-side (redex) drives the purity premise,
   exactly as in the forward direction.

## What is already proved

- **Reverse root core — free.** `gate_letE_to_redex` (+ `_anyfuel`),
  `LamBetaReflect.lean`. Under the standard gate + pure operand, the contractum
  `.letE x V B` and the redex `.app [λx.B, V]` reduce to the **identical**
  body-evaluation (`eval_letE` and `eval_beta_builtin` are *both* equations to
  `eval n B (cons x …) {T' with heap := T'.heap ++ [v]}`). Hence
  `eval (n+1) letE = some (r,Tf) ⟹ eval (n+3) redex = some (r,Tf)` — same result,
  `+2` fuel. This is the source of `ReverseSimβ`'s `∃ k'`.
- **Reverse statement + leaf layer.** `FrameβEvalStmtRev` and the leaf cases
  `frameβ_num_caseRev`, `frameβ_bool_caseRev`, `frameβ_lam_caseRev`,
  `frameβ_quote_caseRev` (`LamBetaReflect.lean`). Clean mirrors of the forward leaf
  lemmas: invert `exp_b`, read off its result, reconstruct the a-side at fuel 1.
- **Consumers ready.** `obsConv_refine_backward` and `obsConv_iff_beta` already
  take `ReverseSimβ` and produce the conditional equivalence; nothing downstream
  needs to change once `ReverseSimβ` is a theorem.

## What remains (mechanical mirror of the forward tower)

A bottom-up reverse mirror of `frameβ_tower`. Each clause is the b-side-driven,
`∃k`-fuel analog of the corresponding forward step lemma.

1. **`var` leaf** (`frameβ_var_caseRev`). Needs the *two-sided* `EnvVisβ` lookup:
   from `env_b.lookup y = some idx_b` derive `env_a.lookup y = some idx_a` and
   `ValVisβ` of the heap cells (the forward `frameβ_var_caseW` does the a→b
   direction; mirror it).
2. **Reverse `evalList`** (`FrameβEvalListStmtRev` + step). Per-element reverse
   eval; combine the `∃k`s by `evalList_fuel_mono` to a common bound.
3. **Reverse `applyDirect` / `applyVia`** (`FrameβApplyDirectStmtRev`,
   `FrameβApplyViaStmtRev` + steps). The genuine reverse work:
   - closure case → reverse `eval` on the body (mutual);
   - the gate / `materialize` handling under `BReady` (full tower ⟹ `materialize`
     no-op; non-standard-gate branch vacuous — same structure as the forward
     `frameβ_applyVia_evalWP`);
   - `prim` / `builtinBaseApply` cases mirror the forward.
4. **Recursive eval cases**: `ifte`, `seq`, `letE`, `em` (structural);
   `app` structural + **root** (the root closes with `gate_letE_to_redex_anyfuel`);
   `primApp` (uses reverse `applyDirect`). Each: reverse IH on sub-terms for
   convergence, `frameβ_eval_FL` for the cross-side value/`WFCtxTβ` relation where a
   sub-value's identity is needed (e.g. the `ifte` condition), then reassemble at a
   common fuel.
5. **Assembler** `frameβ_eval_stepRev` (dispatch all 13 constructors; `set` /
   `installPolicy` vacuous under `Pure`), and the **mutual tower**
   `frameβ_tower_rev : ∀ n, FrameStmtβRev n` (mirror of `frameβ_tower`).
6. **Discharge**: `ReverseSimβ` follows from the reverse eval clause by inducting
   on the b-side fuel and combining the `∃k`s.

### Reuse / leverage

- **`frameβ_eval_FL`** supplies the forward value relations and `WFCtxTβ`
  propagation mid-proof — do *not* re-derive `ValVisβ` from scratch in the reverse
  cases; get it from the forward FL + determinism (`eval_fuel_mono`).
- The β-inversions (`BetaRel.{ifte,em,letE,app,primApp}_inv`, `app_inv`) and the
  purity/`BReady`/`ValVisβ` plumbing (`BetaRel.pure_eq`, `ValVisβ_pureVal_rev`,
  `BReady.closed`/`closedList`, `ValVisβ_lam_closures`, …) are all in place from the
  forward build.

### Fuel discipline (the one new bookkeeping)

Forward steps preserve fuel; reverse steps don't. In every recursive reverse case:
collect the sub-`∃k`s, take a common bound, lift each sub-result with
`eval_fuel_mono` / `evalList_fuel_mono`, then run the current node. The `app` root
adds the `+2` from `gate_letE_to_redex`.

## After `ReverseSimβ`

`obsConv_iff_beta` becomes an unconditional-given-side-conditions `↔`. The final
`.lam` headline is `Ctx.plug_cong_master` (`CtxPure.lean`) extended to the `.lam`
constructor: the congruence machinery (`CtxEquiv.under_lam`, `CtxEquiv.congr`) is
free once the side conditions (`BReady` / `Pure`) are shown closed under context
composition — the standard `plug_cong_master` condition-threading, here for the
binder.
