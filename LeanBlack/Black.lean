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

/-! ## Structural-beq correctness lemmas (ported from lean-green)

    `val_beq_eq` lifts boolean structural equality to propositional
    equality. `val_beq_self` is reflexivity. Used by
    `multnExactPolicy_implies_InstallFacts` to extract the install-
    protocol facts from policy admission. -/

mutual

theorem val_beq_eq : ∀ (a b : Val), Val.beq a b = true → a = b
  | .num x,             .num y,            h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .bool x,            .bool y,           h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .nilV,              .nilV,             _ => rfl
  | .sym x,             .sym y,            h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .prim x,            .prim y,           h => by
      simp only [Val.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .builtinBaseApply,  .builtinBaseApply, _ => rfl
  | .cons x₁ y₁,        .cons x₂ y₂,       h => by
      simp only [Val.beq, Bool.and_eq_true] at h
      exact (val_beq_eq x₁ x₂ h.1) ▸ (val_beq_eq y₁ y₂ h.2) ▸ rfl
  | .closure ps₁ b₁ e₁, .closure ps₂ b₂ e₂, h => by
      simp only [Val.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1 ▸ (expr_beq_eq b₁ b₂ h.1.2) ▸
            (env_beq_eq e₁ e₂ h.2) ▸ rfl
  | .num _, .bool _, h | .num _, .nilV, h | .num _, .cons _ _, h
  | .num _, .sym _, h | .num _, .closure _ _ _, h | .num _, .prim _, h
  | .num _, .builtinBaseApply, h
  | .bool _, .num _, h | .bool _, .nilV, h | .bool _, .cons _ _, h
  | .bool _, .sym _, h | .bool _, .closure _ _ _, h | .bool _, .prim _, h
  | .bool _, .builtinBaseApply, h
  | .nilV, .num _, h | .nilV, .bool _, h | .nilV, .cons _ _, h
  | .nilV, .sym _, h | .nilV, .closure _ _ _, h | .nilV, .prim _, h
  | .nilV, .builtinBaseApply, h
  | .cons _ _, .num _, h | .cons _ _, .bool _, h | .cons _ _, .nilV, h
  | .cons _ _, .sym _, h | .cons _ _, .closure _ _ _, h
  | .cons _ _, .prim _, h | .cons _ _, .builtinBaseApply, h
  | .sym _, .num _, h | .sym _, .bool _, h | .sym _, .nilV, h
  | .sym _, .cons _ _, h | .sym _, .closure _ _ _, h
  | .sym _, .prim _, h | .sym _, .builtinBaseApply, h
  | .closure _ _ _, .num _, h | .closure _ _ _, .bool _, h
  | .closure _ _ _, .nilV, h | .closure _ _ _, .cons _ _, h
  | .closure _ _ _, .sym _, h | .closure _ _ _, .prim _, h
  | .closure _ _ _, .builtinBaseApply, h
  | .prim _, .num _, h | .prim _, .bool _, h | .prim _, .nilV, h
  | .prim _, .cons _ _, h | .prim _, .sym _, h
  | .prim _, .closure _ _ _, h | .prim _, .builtinBaseApply, h
  | .builtinBaseApply, .num _, h | .builtinBaseApply, .bool _, h
  | .builtinBaseApply, .nilV, h | .builtinBaseApply, .cons _ _, h
  | .builtinBaseApply, .sym _, h | .builtinBaseApply, .closure _ _ _, h
  | .builtinBaseApply, .prim _, h => by simp [Val.beq] at h

theorem expr_beq_eq : ∀ (a b : Expr), Expr.beq a b = true → a = b
  | .num x,            .num y,            h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .bool x,           .bool y,           h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .quote x,          .quote y,          h => by
      simp only [Expr.beq] at h; exact (val_beq_eq x y h) ▸ rfl
  | .var x,            .var y,            h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .ifte c₁ t₁ e₁,    .ifte c₂ t₂ e₂,    h => by
      simp only [Expr.beq, Bool.and_eq_true] at h
      exact (expr_beq_eq c₁ c₂ h.1.1) ▸ (expr_beq_eq t₁ t₂ h.1.2) ▸
            (expr_beq_eq e₁ e₂ h.2) ▸ rfl
  | .lam ps₁ b₁,       .lam ps₂ b₂,       h => by
      simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1 ▸ (expr_beq_eq b₁ b₂ h.2) ▸ rfl
  | .app es₁,          .app es₂,          h => by
      simp only [Expr.beq] at h; exact (expr_list_beq_eq es₁ es₂ h) ▸ rfl
  | .set x₁ e₁,        .set x₂ e₂,        h => by
      simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1 ▸ (expr_beq_eq e₁ e₂ h.2) ▸ rfl
  | .em b₁,            .em b₂,            h => by
      simp only [Expr.beq] at h; exact (expr_beq_eq b₁ b₂ h) ▸ rfl
  | .primApp f₁ as₁,   .primApp f₂ as₂,   h => by
      simp only [Expr.beq, Bool.and_eq_true] at h
      exact (expr_beq_eq f₁ f₂ h.1) ▸ (expr_list_beq_eq as₁ as₂ h.2) ▸ rfl
  | .letE x₁ e₁ b₁,    .letE x₂ e₂ b₂,    h => by
      simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1 ▸ (expr_beq_eq e₁ e₂ h.1.2) ▸ (expr_beq_eq b₁ b₂ h.2) ▸ rfl
  | .seq es₁,          .seq es₂,          h => by
      simp only [Expr.beq] at h; exact (expr_list_beq_eq es₁ es₂ h) ▸ rfl
  | .installPolicy x,  .installPolicy y,  h => by
      simp only [Expr.beq, beq_iff_eq] at h; exact h ▸ rfl
  | .num _, .bool _, h | .num _, .quote _, h | .num _, .var _, h
  | .num _, .ifte _ _ _, h | .num _, .lam _ _, h | .num _, .app _, h
  | .num _, .set _ _, h | .num _, .em _, h | .num _, .primApp _ _, h
  | .num _, .letE _ _ _, h | .num _, .seq _, h | .num _, .installPolicy _, h
  | .bool _, .num _, h | .bool _, .quote _, h | .bool _, .var _, h
  | .bool _, .ifte _ _ _, h | .bool _, .lam _ _, h | .bool _, .app _, h
  | .bool _, .set _ _, h | .bool _, .em _, h | .bool _, .primApp _ _, h
  | .bool _, .letE _ _ _, h | .bool _, .seq _, h | .bool _, .installPolicy _, h
  | .quote _, .num _, h | .quote _, .bool _, h | .quote _, .var _, h
  | .quote _, .ifte _ _ _, h | .quote _, .lam _ _, h | .quote _, .app _, h
  | .quote _, .set _ _, h | .quote _, .em _, h | .quote _, .primApp _ _, h
  | .quote _, .letE _ _ _, h | .quote _, .seq _, h | .quote _, .installPolicy _, h
  | .var _, .num _, h | .var _, .bool _, h | .var _, .quote _, h
  | .var _, .ifte _ _ _, h | .var _, .lam _ _, h | .var _, .app _, h
  | .var _, .set _ _, h | .var _, .em _, h | .var _, .primApp _ _, h
  | .var _, .letE _ _ _, h | .var _, .seq _, h | .var _, .installPolicy _, h
  | .ifte _ _ _, .num _, h | .ifte _ _ _, .bool _, h | .ifte _ _ _, .quote _, h
  | .ifte _ _ _, .var _, h | .ifte _ _ _, .lam _ _, h | .ifte _ _ _, .app _, h
  | .ifte _ _ _, .set _ _, h | .ifte _ _ _, .em _, h
  | .ifte _ _ _, .primApp _ _, h | .ifte _ _ _, .letE _ _ _, h
  | .ifte _ _ _, .seq _, h | .ifte _ _ _, .installPolicy _, h
  | .lam _ _, .num _, h | .lam _ _, .bool _, h | .lam _ _, .quote _, h
  | .lam _ _, .var _, h | .lam _ _, .ifte _ _ _, h | .lam _ _, .app _, h
  | .lam _ _, .set _ _, h | .lam _ _, .em _, h | .lam _ _, .primApp _ _, h
  | .lam _ _, .letE _ _ _, h | .lam _ _, .seq _, h | .lam _ _, .installPolicy _, h
  | .app _, .num _, h | .app _, .bool _, h | .app _, .quote _, h
  | .app _, .var _, h | .app _, .ifte _ _ _, h | .app _, .lam _ _, h
  | .app _, .set _ _, h | .app _, .em _, h | .app _, .primApp _ _, h
  | .app _, .letE _ _ _, h | .app _, .seq _, h | .app _, .installPolicy _, h
  | .set _ _, .num _, h | .set _ _, .bool _, h | .set _ _, .quote _, h
  | .set _ _, .var _, h | .set _ _, .ifte _ _ _, h | .set _ _, .lam _ _, h
  | .set _ _, .app _, h | .set _ _, .em _, h | .set _ _, .primApp _ _, h
  | .set _ _, .letE _ _ _, h | .set _ _, .seq _, h | .set _ _, .installPolicy _, h
  | .em _, .num _, h | .em _, .bool _, h | .em _, .quote _, h
  | .em _, .var _, h | .em _, .ifte _ _ _, h | .em _, .lam _ _, h
  | .em _, .app _, h | .em _, .set _ _, h | .em _, .primApp _ _, h
  | .em _, .letE _ _ _, h | .em _, .seq _, h | .em _, .installPolicy _, h
  | .primApp _ _, .num _, h | .primApp _ _, .bool _, h
  | .primApp _ _, .quote _, h | .primApp _ _, .var _, h
  | .primApp _ _, .ifte _ _ _, h | .primApp _ _, .lam _ _, h
  | .primApp _ _, .app _, h | .primApp _ _, .set _ _, h
  | .primApp _ _, .em _, h | .primApp _ _, .letE _ _ _, h
  | .primApp _ _, .seq _, h | .primApp _ _, .installPolicy _, h
  | .letE _ _ _, .num _, h | .letE _ _ _, .bool _, h
  | .letE _ _ _, .quote _, h | .letE _ _ _, .var _, h
  | .letE _ _ _, .ifte _ _ _, h | .letE _ _ _, .lam _ _, h
  | .letE _ _ _, .app _, h | .letE _ _ _, .set _ _, h
  | .letE _ _ _, .em _, h | .letE _ _ _, .primApp _ _, h
  | .letE _ _ _, .seq _, h | .letE _ _ _, .installPolicy _, h
  | .seq _, .num _, h | .seq _, .bool _, h | .seq _, .quote _, h
  | .seq _, .var _, h | .seq _, .ifte _ _ _, h | .seq _, .lam _ _, h
  | .seq _, .app _, h | .seq _, .set _ _, h | .seq _, .em _, h
  | .seq _, .primApp _ _, h | .seq _, .letE _ _ _, h
  | .seq _, .installPolicy _, h
  | .installPolicy _, .num _, h | .installPolicy _, .bool _, h
  | .installPolicy _, .quote _, h | .installPolicy _, .var _, h
  | .installPolicy _, .ifte _ _ _, h | .installPolicy _, .lam _ _, h
  | .installPolicy _, .app _, h | .installPolicy _, .set _ _, h
  | .installPolicy _, .em _, h | .installPolicy _, .primApp _ _, h
  | .installPolicy _, .letE _ _ _, h | .installPolicy _, .seq _, h =>
      by simp [Expr.beq] at h

theorem expr_list_beq_eq : ∀ (xs ys : List Expr), exprListBeq xs ys = true → xs = ys
  | [],      [],      _ => rfl
  | _ :: _,  [],      h => by simp [exprListBeq] at h
  | [],      _ :: _,  h => by simp [exprListBeq] at h
  | x :: xs, y :: ys, h => by
      simp only [exprListBeq, Bool.and_eq_true] at h
      exact (expr_beq_eq x y h.1) ▸ (expr_list_beq_eq xs ys h.2) ▸ rfl

theorem env_beq_eq : ∀ (a b : Env), Env.beq a b = true → a = b
  | .nil,           .nil,           _ => rfl
  | .nil,           .cons _ _ _,    h => by simp [Env.beq] at h
  | .cons _ _ _,    .nil,           h => by simp [Env.beq] at h
  | .cons k₁ i₁ r₁, .cons k₂ i₂ r₂, h => by
      simp only [Env.beq, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1 ▸ h.1.2 ▸ (env_beq_eq r₁ r₂ h.2) ▸ rfl

end

/-! ## Round-tripping cons-lists -/

theorem valToList_listToVal (xs : List Val) :
    valToList (listToVal xs) = some xs := by
  induction xs with
  | nil       => rfl
  | cons _ xs ih => simp [listToVal, valToList, ih]
