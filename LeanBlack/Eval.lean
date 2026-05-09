/-
  lean-black: Eval layer.

  `eval` / `evalList` / `applyVia` / `applyDirect` adapted from
  lean-green, threading a `TowerState` instead of a `RunState` and
  carrying a `level : Nat` parameter throughout.

  Key semantic changes from lean-green:

  - `(em body)`: materializes level (`level + 1`) if needed, evaluates
    `body` at that level with `env := T.envAt? (level + 1)`. No
    longer the stage-1 simplification "metaEnv := metaEnv".

  - `(set! x e)`: gating uses `T.policyAt? level` (the policy at the
    *current* level, governing modifications visible to level
    (`level - 1`)). The "meta-mutation" predicate compares the local
    env's idx for `x` against `T.envAt? level`'s idx — same shape as
    lean-green's `isMetaMutation env metaEnv`, parameterized by the
    tower instead of a single metaEnv.

  - `(installPolicy n)`: replaces `T.policyAt? level` with
    `ptable[n]?`. Per DESIGN.md decision 4, the level whose policy
    is replaced is the *current* level.

  - `applyVia` at level N: looks up `base-apply` in
    `T.envAt? (level + 1)` (materializing if needed), reads
    `T.heap[idx]?`. Cross-level dispatch: when that cell holds a
    closure created at level (N+1) by a previous `(set! base-apply
    ...)`, the closure runs *at level N* (it now IS level N's apply
    rule). Its captured env carries idxes that are valid because the
    heap is global.

  See `DESIGN.md` for the full architectural rationale.
-/

import LeanBlack.Black
import LeanBlack.Tower

/-- True iff `x` resolves to the same heap-cell index in both `env`
    and `T.envAt? level`. The architectural marker: mutations that
    hit a level-`level` env binding go through the policy gate. -/
def isMetaMutation (x : String) (env : Env) (T : TowerState) (level : Nat) : Bool :=
  match env.lookup x, (T.envAt? level).bind (·.lookup x) with
  | some i₁, some i₂ => i₁ == i₂
  | _, _             => false

mutual

def eval (fuel : Nat) (ptable : PolicyTable) (level : Nat) (exp : Expr)
    (env : Env) (T : TowerState) : Option (Val × TowerState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exp with
    | .num i        => some (.num i, T)
    | .bool b       => some (.bool b, T)
    | .quote v      => if closedValB v then some (v, T) else none
    | .var x        =>
        match env.lookup x with
        | some idx => match T.heap[idx]? with
                      | some v => some (v, T)
                      | none   => none
        | none     => none
    | .ifte c t e   =>
        match eval n ptable level c env T with
        | some (.bool false, T') => eval n ptable level e env T'
        | some (_,           T') => eval n ptable level t env T'
        | none                   => none
    | .lam ps body  => some (.closure ps body env, T)
    | .app exps     =>
        match exps with
        | []        => none
        | f :: args =>
            match eval n ptable level f env T with
            | none           => none
            | some (fv, T')  =>
                match evalList n ptable level args env T' with
                | none            => none
                | some (avs, T'') => applyVia n ptable level fv avs T''
    | .primApp f args =>
        match eval n ptable level f env T with
        | none          => none
        | some (fv, T') =>
            match evalList n ptable level args env T' with
            | none            => none
            | some (avs, T'') => applyDirect n ptable level fv avs T''
    | .set x e      =>
        -- Freeze the gate at the start of `.set`, *before* `e`
        -- evaluates. Otherwise an `installPolicy`-bearing RHS could
        -- downgrade the policy mid-evaluation and authorize itself
        -- under the looser policy. (Same TOCTOU concern as
        -- lean-green's GOTCHAS.md #1.)
        let gate? := T.policyAt? level
        match eval n ptable level e env T with
        | none         => none
        | some (v, T') =>
            match env.lookup x with
            | none     => none
            | some idx =>
                if isMetaMutation x env T' level then
                  match T'.heap[idx]?, gate? with
                  | some oldVal, some gate =>
                      let metaEnv := (T'.envAt? level).getD .nil
                      let ctx : MutationCtx :=
                        { target := x, heap := T'.heap, env := env,
                          metaEnv := metaEnv, index := idx, level := level }
                      if gate ctx oldVal v then
                        some (.bool true, T'.updateHeap idx v)
                      else
                        some (.bool false, T')
                  | _, _ => none
                else
                  -- Plain mutation: not gated. Returns true uniformly.
                  some (.bool true, T'.updateHeap idx v)
    | .em body      =>
        -- Shift up: materialize level+1, evaluate body there with
        -- the new level's env in scope.
        match T.materialize (level + 1) with
        | none => none
        | some T' =>
            match T'.envAt? (level + 1) with
            | none        => none
            | some upEnv  => eval n ptable (level + 1) body upEnv T'
    | .letE x e body =>
        match eval n ptable level e env T with
        | none         => none
        | some (v, T') =>
            let (T'', idx) := T'.alloc v
            eval n ptable level body (.cons x idx env) T''
    | .seq exps     =>
        match exps with
        | []         => some (.nilV, T)
        | [e]        => eval n ptable level e env T
        | e :: rest  =>
            match eval n ptable level e env T with
            | none          => none
            | some (_, T')  => eval n ptable level (.seq rest) env T'
    | .installPolicy idx =>
        match ptable[idx]? with
        | some newPolicy => some (.bool true, T.setPolicyAt level newPolicy)
        | none           => some (.bool false, T)

def evalList (fuel : Nat) (ptable : PolicyTable) (level : Nat) (exps : List Expr)
    (env : Env) (T : TowerState) : Option (List Val × TowerState) :=
  match fuel with
  | 0     => none
  | n + 1 =>
    match exps with
    | []        => some ([], T)
    | e :: rest =>
        match eval n ptable level e env T with
        | none         => none
        | some (v, T') =>
            match evalList n ptable level rest env T' with
            | none           => none
            | some (vs, T'') => some (v :: vs, T'')

/-- Application via the level-(`level + 1`) `base-apply` cell. The
    hinge of the cross-level causal-connection property: every
    application at level `level` goes through whatever value is
    bound to `base-apply` in level (`level + 1`)'s env. -/
def applyVia (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T : TowerState)
    : Option (Val × TowerState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match T.materialize (level + 1) with
    | none => none
    | some T' =>
        match T'.envAt? (level + 1) with
        | none => applyDirect n ptable level op args T'
        | some upEnv =>
            match upEnv.lookup "base-apply" with
            | none     => applyDirect n ptable level op args T'
            | some idx =>
                match T'.heap[idx]? with
                | none                       => none
                | some .builtinBaseApply     => applyDirect n ptable level op args T'
                | some baseApply             =>
                    applyDirect n ptable level baseApply
                      [op, listToVal args] T'

/-- Direct application — bypasses base-apply lookup. Used by the
    builtin dispatcher and by `prim-apply` (Black's `primitive-EM`
    analog: replacement closures use it to call captured originals
    without infinite regress). -/
def applyDirect (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T : TowerState)
    : Option (Val × TowerState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match op with
    | .closure ps body cenv =>
        if ps.length != args.length then none else
          let (h', env') := args.zip ps |>.foldl allocStep (T.heap, cenv)
          eval n ptable level body env' { T with heap := h' }
    | .prim name =>
        match applyPrim name args with
        | some v => some (v, T)
        | none   => none
    | .builtinBaseApply =>
        match args with
        | [actualOp, operandsList] =>
            match valToList operandsList with
            | some operands => applyDirect n ptable level actualOp operands T
            | none          => none
        | _ => none
    | _ => none
end

/-! ## Top-level entry -/

def evalProgram (fuel : Nat) (ptable : PolicyTable) (e : Expr)
    (defaultPolicy : BlackPolicy := acceptAllPolicy) : Option Val :=
  let T₀ := initTower
  let T := T₀.setPolicyAt 0 defaultPolicy
  match T.envAt? 0 with
  | none     => none
  | some env => (eval fuel ptable 0 e env T).map Prod.fst
