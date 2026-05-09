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

/-! ## Structural beq (for policies that compare Val cells) -/

mutual
  def Val.beq : Val → Val → Bool
    | .num a,             .num b             => a == b
    | .bool a,            .bool b             => a == b
    | .nilV,              .nilV               => true
    | .cons x₁ y₁,        .cons x₂ y₂         => Val.beq x₁ x₂ && Val.beq y₁ y₂
    | .sym a,             .sym b              => a == b
    | .closure ps₁ b₁ e₁, .closure ps₂ b₂ e₂  =>
        ps₁ == ps₂ && Expr.beq b₁ b₂ && Env.beq e₁ e₂
    | .prim a,            .prim b             => a == b
    | .builtinBaseApply,  .builtinBaseApply   => true
    | _,                  _                   => false

  def Expr.beq : Expr → Expr → Bool
    | .num a,         .num b         => a == b
    | .bool a,        .bool b         => a == b
    | .quote a,       .quote b        => Val.beq a b
    | .var a,         .var b          => a == b
    | .ifte c₁ t₁ e₁, .ifte c₂ t₂ e₂  =>
        Expr.beq c₁ c₂ && Expr.beq t₁ t₂ && Expr.beq e₁ e₂
    | .lam ps₁ b₁,    .lam ps₂ b₂    => ps₁ == ps₂ && Expr.beq b₁ b₂
    | .app es₁,       .app es₂        => exprListBeq es₁ es₂
    | .set x₁ e₁,     .set x₂ e₂      => x₁ == x₂ && Expr.beq e₁ e₂
    | .em b₁,         .em b₂          => Expr.beq b₁ b₂
    | .primApp f₁ as₁, .primApp f₂ as₂ =>
        Expr.beq f₁ f₂ && exprListBeq as₁ as₂
    | .letE x₁ e₁ b₁, .letE x₂ e₂ b₂  =>
        x₁ == x₂ && Expr.beq e₁ e₂ && Expr.beq b₁ b₂
    | .seq es₁,       .seq es₂        => exprListBeq es₁ es₂
    | .installPolicy a, .installPolicy b => a == b
    | _,              _                => false

  def exprListBeq : List Expr → List Expr → Bool
    | [],      []      => true
    | x :: xs, y :: ys => Expr.beq x y && exprListBeq xs ys
    | _,       _        => false

  def Env.beq : Env → Env → Bool
    | .nil,           .nil           => true
    | .cons k₁ i₁ r₁, .cons k₂ i₂ r₂ => k₁ == k₂ && i₁ == i₂ && Env.beq r₁ r₂
    | _,              _               => false
end

instance : BEq Val := ⟨Val.beq⟩

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

/-- Soundness of a policy w.r.t. an arbitrary `P : Val → Val → Prop`
    floor (e.g., `CE level` defined in `Policies.lean`). -/
def BlackPolicy.Sound (P : Val → Val → Prop) (p : BlackPolicy) : Prop :=
  ∀ ctx old new, p ctx old new = true → P old new

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
