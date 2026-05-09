/-
  lean-black: Data layer.

  Val, Expr, Env (mutual), Heap, primitives, MutationCtx, BlackPolicy.

  Adapted from `lean-green/LeanBlack/Black.lean`. Trimmed to the
  runtime essentials: the structural-`beq` correctness lemmas and
  the verified policy library are deferred (they live in `Bisim.lean`
  / `Policies.lean` in lean-green; the lean-black ports come once
  the runtime layer here is solid).

  The per-level `LevelState` and the `Tower` type live in
  `Tower.lean`; `eval` / `evalList` / `applyVia` / `applyDirect`
  thread a `Tower` instead of a single `RunState` and live in
  `Eval.lean`.
-/

mutual
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | nilV    : Val
  | cons    : Val → Val → Val
  | sym     : String → Val
  | closure : List String → Expr → Env → Val
  | prim    : String → Val
  | builtinBaseApply : Val
  deriving Repr

inductive Expr where
  | num           : Int → Expr
  | bool          : Bool → Expr
  | quote         : Val → Expr
  | var           : String → Expr
  | ifte          : Expr → Expr → Expr → Expr
  | lam           : List String → Expr → Expr
  | app           : List Expr → Expr
  | set           : String → Expr → Expr
  | em            : Expr → Expr
  | primApp       : Expr → List Expr → Expr
  | letE          : String → Expr → Expr → Expr
  | seq           : List Expr → Expr
  | installPolicy : Nat → Expr
  deriving Repr

inductive Env where
  | nil  : Env
  | cons : String → Nat → Env → Env
  deriving Repr
end

abbrev Heap := List Val

def Env.lookup : Env → String → Option Nat
  | .nil, _ => none
  | .cons k idx rest, name => if k == name then some idx else rest.lookup name

def Heap.alloc (h : Heap) (v : Val) : Heap × Nat := (h ++ [v], h.length)

def Heap.update : Heap → Nat → Val → Heap
  | [],       _,     _ => []
  | _ :: t,   0,     v => v :: t
  | x :: t,   n + 1, v => x :: Heap.update t n v

def listToVal : List Val → Val
  | []      => .nilV
  | x :: xs => .cons x (listToVal xs)

def valToList : Val → Option (List Val)
  | .nilV       => some []
  | .cons x xs  =>
      match valToList xs with
      | some l => some (x :: l)
      | none   => none
  | _           => none

def mulConsList : Val → Option Int
  | .nilV               => some 1
  | .cons (.num n) rest => (mulConsList rest).map (n * ·)
  | _                   => none

/-- Heap-independent values: contain no closure references, and so
    relate trivially to themselves under any pair of heaps. Used to
    constrain `.quote` to literals. -/
def closedValB : Val → Bool
  | .num _              => true
  | .bool _             => true
  | .nilV               => true
  | .sym _              => true
  | .prim _             => true
  | .builtinBaseApply   => true
  | .cons x y           => closedValB x && closedValB y
  | .closure _ _ _      => false

/-! ## Primitives -/

def applyPrim_plus : List Val → Option Val
  | [.num a, .num b] => some (.num (a + b))
  | _                => none

def applyPrim_minus : List Val → Option Val
  | [.num a, .num b] => some (.num (a - b))
  | _                => none

def applyPrim_times : List Val → Option Val
  | [.num a, .num b] => some (.num (a * b))
  | _                => none

def applyPrim_mulList : List Val → Option Val
  | [v] => (mulConsList v).map (.num ·)
  | _   => none

def applyPrim_eq : List Val → Option Val
  | [.num a, .num b] => some (.bool (a == b))
  | _                => none

def applyPrim_numQ : List Val → Option Val
  | [.num _] => some (.bool true)
  | [_]      => some (.bool false)
  | _        => none

def applyPrim_boolQ : List Val → Option Val
  | [.bool _] => some (.bool true)
  | [_]       => some (.bool false)
  | _         => none

def applyPrim_closureQ : List Val → Option Val
  | [.closure _ _ _] => some (.bool true)
  | [_]              => some (.bool false)
  | _                => none

def applyPrim_primQ : List Val → Option Val
  | [.prim _] => some (.bool true)
  | [_]       => some (.bool false)
  | _         => none

def applyPrim_cons : List Val → Option Val
  | [a, b] => some (.cons a b)
  | _      => none

def applyPrim_car : List Val → Option Val
  | [.cons a _] => some a
  | _           => none

def applyPrim_cdr : List Val → Option Val
  | [.cons _ b] => some b
  | _           => none

def applyPrim_nullQ : List Val → Option Val
  | [.nilV] => some (.bool true)
  | [_]     => some (.bool false)
  | _       => none

def applyPrim (name : String) (args : List Val) : Option Val :=
  if name = "+" then applyPrim_plus args
  else if name = "-" then applyPrim_minus args
  else if name = "*" then applyPrim_times args
  else if name = "mul-list" then applyPrim_mulList args
  else if name = "=" then applyPrim_eq args
  else if name = "num?" then applyPrim_numQ args
  else if name = "bool?" then applyPrim_boolQ args
  else if name = "closure?" then applyPrim_closureQ args
  else if name = "prim?" then applyPrim_primQ args
  else if name = "cons" then applyPrim_cons args
  else if name = "car" then applyPrim_car args
  else if name = "cdr" then applyPrim_cdr args
  else if name = "null?" then applyPrim_nullQ args
  else none

/-! ## Mutation context and policy -/

/-- The mutation site context the policy gate sees at admission
    time. `level` is the level at which the `(set! ...)` is
    happening (mutating that level's heap, observed by level-1's
    `applyVia`). The library of concrete policies and their
    soundness theorems will live in a future `Policies.lean`. -/
structure MutationCtx where
  target  : String   -- the name being mutated
  heap    : Heap     -- the heap at the moment of the gate check
                     -- (= level `level`'s heap, post-RHS pre-update)
  env     : Env      -- the env in which the `.set` was evaluated
  metaEnv : Env      -- the env at level `level` (= "metaEnv" from
                     -- level (level-1)'s perspective)
  index   : Nat      -- the heap index `target` resolves to
  level   : Nat      -- the level at which the mutation happens

/-- A policy decides whether to admit a meta-env mutation, given the
    mutation context and the old / new values. -/
abbrev BlackPolicy := MutationCtx → Val → Val → Bool

abbrev PolicyTable := List BlackPolicy

/-- Default permissive policy. Useful for un-governed demos that
    show the cascade's failure modes. -/
def acceptAllPolicy : BlackPolicy := fun _ _ _ => true

/-- Default restrictive policy: refuses every meta-mutation. -/
def rejectAllPolicy : BlackPolicy := fun _ _ _ => false

/-! ## Initial bindings -/

def buildBindings (pairs : List (String × Val)) : Env × Heap :=
  pairs.foldl
    (fun (acc : Env × Heap) (kv : String × Val) =>
      let (env, h) := acc
      let (h', idx) := h.alloc kv.2
      (.cons kv.1 idx env, h'))
    (.nil, [])

def initBaseEnv : Env × Heap :=
  buildBindings
    [ ("+",        .prim "+")
    , ("-",        .prim "-")
    , ("*",        .prim "*")
    , ("=",        .prim "=")
    , ("num?",     .prim "num?")
    , ("bool?",    .prim "bool?")
    , ("closure?", .prim "closure?")
    , ("prim?",    .prim "prim?")
    , ("cons",     .prim "cons")
    , ("car",      .prim "car")
    , ("cdr",      .prim "cdr")
    , ("null?",    .prim "null?")
    , ("mul-list", .prim "mul-list")
    ]
