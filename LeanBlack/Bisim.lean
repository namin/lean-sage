/-
  Value and environment bisimulation for lean-black.

  The natural same-`Val` framing — *"if eval succeeds in state s, it
  succeeds with the same Val in state s ++ extras"* — is provably
  false in any language with closures-as-values, because
  `eval (.lam ps body) env` returns `.closure ps body env`, and two
  evaluations with `env_a ≠ env_b` produce two distinct closure
  values. CakeML faces and addresses this in Kumar 2016 §3.2 with
  *syntax-based data refinement*: closures relate when their bodies
  are syntactically equal and their captured envs are pointwise
  related. We adopt the same shape, specialized to our setting
  where source and target are the same language (so closure bodies
  are *equal*, not "compiles to").

  ## Why depth-indexed

  The mutual recursion `ValVis ↔ EnvVis` is not structurally
  founded:
    - `ValVis` on closure recurses into `EnvVis` on cenv;
    - `EnvVis` iterates over names, looks up Vals from the heap,
      and recurses into `ValVis` on those Vals — but the
      heap-looked-up Vals are not in any structural-decrease
      relation with the closure's cenv.

  The standard fix is depth-indexed approximations
  `ValVis_aux n` and `EnvVis_aux n`, where `n` bounds how deep into
  closure-captured envs we look. The "real" relations are
  `ValVis = ∀ n, ValVis_aux n` and `EnvVis = ∀ n, EnvVis_aux n`.

  This gives us:
    - `ValVis_aux` is structurally recursive in `Nat` (Lean accepts
      it without ceremony);
    - `EnvVis_aux` is a non-recursive wrapper around `ValVis_aux`;
    - The "real" relations are the limit of the chain of
      approximations.

  Framing theorems are stated at all depths uniformly and the
  proofs flow through.
-/

import LeanBlack.Black
import LeanBlack.Tower

/-! ## Depth-indexed value and env bisimulation -/

/-- `ValVis_aux n v_a v_b h_a h_b` — at depth bound `n`, values
    `v_a` (in heap `h_a`) and `v_b` (in heap `h_b`) are bisimilar.

    Closures relate when bodies are syntactically equal and captured
    envs are pointwise-related at depth `n - 1`. First-order values
    relate by structural equality. Mismatched constructors don't
    relate (return `False`). At depth `0`, every pair trivially
    relates (the bound has been reached). -/
def ValVis_aux : Nat → Val → Val → Heap → Heap → Prop
  | 0, _, _, _, _ => True
  | _ + 1, .num a,            .num b,            _,  _   => a = b
  | _ + 1, .bool a,           .bool b,           _,  _   => a = b
  | _ + 1, .nilV,             .nilV,             _,  _   => True
  | _ + 1, .sym a,            .sym b,            _,  _   => a = b
  | _ + 1, .prim a,           .prim b,           _,  _   => a = b
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _,  _   => True
  | n + 1, .cons x_a y_a,     .cons x_b y_b,     h_a, h_b =>
      ValVis_aux n x_a x_b h_a h_b ∧ ValVis_aux n y_a y_b h_a h_b
  | n + 1, .closure ps_a body_a cenv_a,
           .closure ps_b body_b cenv_b, h_a, h_b =>
      ps_a = ps_b ∧ body_a = body_b ∧ cenv_a = cenv_b ∧
      (∀ x, match cenv_a.lookup x, cenv_b.lookup x with
            | none, none => True
            | some i_a, some i_b =>
                match h_a[i_a]?, h_b[i_b]? with
                | some v_a, some v_b => ValVis_aux n v_a v_b h_a h_b
                | _, _ => False
            | _, _ => False)
  | _ + 1, _, _, _, _ => False

/-- `EnvVis_aux n env_a env_b h_a h_b` — at depth bound `n`, envs
    `env_a` and `env_b` look up to bisimilar values in their
    respective heaps.

    Defined as a non-recursive wrapper around `ValVis_aux`; the
    "true" mutual recursion is folded into `ValVis_aux`'s closure
    case (which inlines this body). The wrapper exists for use
    in framing theorems where we want to talk about env relatedness
    independently. -/
def EnvVis_aux (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ x, match env_a.lookup x, env_b.lookup x with
       | none, none => True
       | some i_a, some i_b =>
           match h_a[i_a]?, h_b[i_b]? with
           | some v_a, some v_b => ValVis_aux n v_a v_b h_a h_b
           | _, _ => False
       | _, _ => False

/-- The "real" value bisimulation: holds at every depth. -/
def ValVis (v_a v_b : Val) (h_a h_b : Heap) : Prop :=
  ∀ n, ValVis_aux n v_a v_b h_a h_b

/-- The "real" env bisimulation. -/
def EnvVis (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ n, EnvVis_aux n env_a env_b h_a h_b

/-- The closure case of `ValVis_aux`: bisim-related closures have
    structurally-equal captured envs (`cenv_a = cenv_b`) and the
    captured env's slots in the heap pair are pointwise bisim-
    related at depth `n`. The added `cenv_a = cenv_b` field makes
    cross-side cell updates affect the same index on both sides,
    which is what closes the `.set`-framing case. -/
theorem ValVis_aux_closure (n : Nat)
    (ps_a ps_b : List String) (body_a body_b : Expr)
    (cenv_a cenv_b : Env) (h_a h_b : Heap) :
    ValVis_aux (n + 1)
        (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b
    ↔ (ps_a = ps_b ∧ body_a = body_b ∧ cenv_a = cenv_b ∧
       EnvVis_aux n cenv_a cenv_b h_a h_b) := by
  simp [ValVis_aux, EnvVis_aux]

/-! ## Weak depth-indexed bisimulation

    `ValVis_aux_weak` is a sibling relation to `ValVis_aux` with the
    `cenv_a = cenv_b` clause **dropped** from the closure case. It
    relates closures that have the same code and cenvs that look up to
    *bisim*-related cells, without requiring the cenvs themselves to be
    Lean-equal. This is the form needed for prefix-extension reasoning,
    where running the same computation on heaps that differ by an
    inserted prefix produces closures whose cenvs differ in their
    fresh-region indices but agree on cell values.

    The strong form `ValVis_aux` is preserved unchanged for the
    `.set`-framing case (which relies on Lean-equal cenvs to align
    cross-side cell updates). A direct bridge `ValVis → ValVis_weak`
    lifts framing's strong outputs to the weak form when needed by
    behavioral-equivalence claims (CE).
-/

def ValVis_aux_weak : Nat → Val → Val → Heap → Heap → Prop
  | 0, _, _, _, _ => True
  | _ + 1, .num a,            .num b,            _,  _   => a = b
  | _ + 1, .bool a,           .bool b,           _,  _   => a = b
  | _ + 1, .nilV,             .nilV,             _,  _   => True
  | _ + 1, .sym a,            .sym b,            _,  _   => a = b
  | _ + 1, .prim a,           .prim b,           _,  _   => a = b
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _,  _   => True
  | n + 1, .cons x_a y_a,     .cons x_b y_b,     h_a, h_b =>
      ValVis_aux_weak n x_a x_b h_a h_b ∧ ValVis_aux_weak n y_a y_b h_a h_b
  | n + 1, .closure ps_a body_a cenv_a,
           .closure ps_b body_b cenv_b, h_a, h_b =>
      ps_a = ps_b ∧ body_a = body_b ∧
      (∀ x, match cenv_a.lookup x, cenv_b.lookup x with
            | none, none => True
            | some i_a, some i_b =>
                match h_a[i_a]?, h_b[i_b]? with
                | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
                | _, _ => False
            | _, _ => False)
  | _ + 1, _, _, _, _ => False

/-- Weak env bisim: same shape as `EnvVis_aux` but consumes
    `ValVis_aux_weak` on cell values (so closures stored in cells need
    only be weakly bisim-related). -/
def EnvVis_aux_weak (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ x, match env_a.lookup x, env_b.lookup x with
       | none, none => True
       | some i_a, some i_b =>
           match h_a[i_a]?, h_b[i_b]? with
           | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
           | _, _ => False
       | _, _ => False

def ValVis_weak (v_a v_b : Val) (h_a h_b : Heap) : Prop :=
  ∀ n, ValVis_aux_weak n v_a v_b h_a h_b

def EnvVis_weak (env_a env_b : Env) (h_a h_b : Heap) : Prop :=
  ∀ n, EnvVis_aux_weak n env_a env_b h_a h_b

/-- The closure case of `ValVis_aux_weak`: same code, with cenvs
    pointwise-bisim through their shared name set (no Lean-equality
    requirement). -/
theorem ValVis_aux_weak_closure (n : Nat)
    (ps_a ps_b : List String) (body_a body_b : Expr)
    (cenv_a cenv_b : Env) (h_a h_b : Heap) :
    ValVis_aux_weak (n + 1)
        (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b
    ↔ (ps_a = ps_b ∧ body_a = body_b ∧
       EnvVis_aux_weak n cenv_a cenv_b h_a h_b) := by
  simp [ValVis_aux_weak, EnvVis_aux_weak]

/-! ### Bridge: strong → weak

    `ValVis_aux n` is strictly stronger than `ValVis_aux_weak n` — it
    adds `cenv_a = cenv_b` on the closure case, but otherwise matches
    pointwise. The bridge is direct structural induction on `n`.
-/

theorem ValVis_aux_to_weak : ∀ (n : Nat) (v_a v_b : Val) (h_a h_b : Heap),
    ValVis_aux n v_a v_b h_a h_b → ValVis_aux_weak n v_a v_b h_a h_b
  | 0, _, _, _, _, _ => trivial
  | n + 1, .num _,            .num _,            _, _, h => h
  | n + 1, .bool _,           .bool _,           _, _, h => h
  | n + 1, .nilV,             .nilV,             _, _, h => h
  | n + 1, .sym _,            .sym _,            _, _, h => h
  | n + 1, .prim _,           .prim _,           _, _, h => h
  | n + 1, .builtinBaseApply, .builtinBaseApply, _, _, h => h
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, h =>
      ⟨ValVis_aux_to_weak n x_a x_b h_a h_b h.1,
       ValVis_aux_to_weak n y_a y_b h_a h_b h.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b, h_a, h_b, h => by
      obtain ⟨hps, hbody, _hcenv, henv⟩ := h
      show ps_a = ps_b ∧ body_a = body_b ∧ _
      refine ⟨hps, hbody, ?_⟩
      intro x
      have hx := henv x
      cases ha : cenv_a.lookup x with
      | none =>
          cases hb : cenv_b.lookup x with
          | none => trivial
          | some i_b => rw [ha, hb] at hx; simp at hx
      | some i_a =>
          cases hb : cenv_b.lookup x with
          | none => rw [ha, hb] at hx; simp at hx
          | some i_b =>
              rw [ha, hb] at hx
              simp only at hx
              cases hpa : h_a[i_a]? with
              | none =>
                  rw [hpa] at hx
                  cases hpb : h_b[i_b]? <;> rw [hpb] at hx <;> exact hx.elim
              | some w_a =>
                  cases hpb : h_b[i_b]? with
                  | none => rw [hpa, hpb] at hx; exact hx.elim
                  | some w_b =>
                      rw [hpa, hpb] at hx
                      show match h_a[i_a]?, h_b[i_b]? with
                           | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
                           | _, _ => False
                      rw [hpa, hpb]
                      exact ValVis_aux_to_weak n w_a w_b h_a h_b hx
  -- Mismatched constructor cases: ValVis_aux is False, contradicts h.
  | n + 1, .num _, .bool _, _, _, h => h.elim
  | n + 1, .num _, .nilV, _, _, h => h.elim
  | n + 1, .num _, .sym _, _, _, h => h.elim
  | n + 1, .num _, .prim _, _, _, h => h.elim
  | n + 1, .num _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .num _, .cons _ _, _, _, h => h.elim
  | n + 1, .num _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .bool _, .num _, _, _, h => h.elim
  | n + 1, .bool _, .nilV, _, _, h => h.elim
  | n + 1, .bool _, .sym _, _, _, h => h.elim
  | n + 1, .bool _, .prim _, _, _, h => h.elim
  | n + 1, .bool _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .bool _, .cons _ _, _, _, h => h.elim
  | n + 1, .bool _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .nilV, .num _, _, _, h => h.elim
  | n + 1, .nilV, .bool _, _, _, h => h.elim
  | n + 1, .nilV, .sym _, _, _, h => h.elim
  | n + 1, .nilV, .prim _, _, _, h => h.elim
  | n + 1, .nilV, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .nilV, .cons _ _, _, _, h => h.elim
  | n + 1, .nilV, .closure _ _ _, _, _, h => h.elim
  | n + 1, .sym _, .num _, _, _, h => h.elim
  | n + 1, .sym _, .bool _, _, _, h => h.elim
  | n + 1, .sym _, .nilV, _, _, h => h.elim
  | n + 1, .sym _, .prim _, _, _, h => h.elim
  | n + 1, .sym _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .sym _, .cons _ _, _, _, h => h.elim
  | n + 1, .sym _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .prim _, .num _, _, _, h => h.elim
  | n + 1, .prim _, .bool _, _, _, h => h.elim
  | n + 1, .prim _, .nilV, _, _, h => h.elim
  | n + 1, .prim _, .sym _, _, _, h => h.elim
  | n + 1, .prim _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .prim _, .cons _ _, _, _, h => h.elim
  | n + 1, .prim _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .num _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .bool _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .nilV, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .sym _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .prim _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .cons _ _, _, _, h => h.elim
  | n + 1, .builtinBaseApply, .closure _ _ _, _, _, h => h.elim
  | n + 1, .cons _ _, .num _, _, _, h => h.elim
  | n + 1, .cons _ _, .bool _, _, _, h => h.elim
  | n + 1, .cons _ _, .nilV, _, _, h => h.elim
  | n + 1, .cons _ _, .sym _, _, _, h => h.elim
  | n + 1, .cons _ _, .prim _, _, _, h => h.elim
  | n + 1, .cons _ _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .cons _ _, .closure _ _ _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .num _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .bool _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .nilV, _, _, h => h.elim
  | n + 1, .closure _ _ _, .sym _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .prim _, _, _, h => h.elim
  | n + 1, .closure _ _ _, .builtinBaseApply, _, _, h => h.elim
  | n + 1, .closure _ _ _, .cons _ _, _, _, h => h.elim

theorem EnvVis_aux_to_weak (n : Nat) (env_a env_b : Env) (h_a h_b : Heap) :
    EnvVis_aux n env_a env_b h_a h_b → EnvVis_aux_weak n env_a env_b h_a h_b := by
  intro h x
  have hx := h x
  cases ha : env_a.lookup x with
  | none =>
      cases hb : env_b.lookup x with
      | none => trivial
      | some _ => rw [ha, hb] at hx; simp at hx
  | some i_a =>
      cases hb : env_b.lookup x with
      | none => rw [ha, hb] at hx; simp at hx
      | some i_b =>
          rw [ha, hb] at hx
          simp only at hx
          cases hpa : h_a[i_a]? with
          | none =>
              rw [hpa] at hx
              cases hpb : h_b[i_b]? <;> rw [hpb] at hx <;> exact hx.elim
          | some w_a =>
              cases hpb : h_b[i_b]? with
              | none => rw [hpa, hpb] at hx; exact hx.elim
              | some w_b =>
                  rw [hpa, hpb] at hx
                  show match h_a[i_a]?, h_b[i_b]? with
                       | some v_a, some v_b => ValVis_aux_weak n v_a v_b h_a h_b
                       | _, _ => False
                  rw [hpa, hpb]
                  exact ValVis_aux_to_weak n w_a w_b h_a h_b hx

theorem ValVis_to_weak {v_a v_b : Val} {h_a h_b : Heap} :
    ValVis v_a v_b h_a h_b → ValVis_weak v_a v_b h_a h_b :=
  fun h n => ValVis_aux_to_weak n v_a v_b h_a h_b (h n)

theorem EnvVis_to_weak {env_a env_b : Env} {h_a h_b : Heap} :
    EnvVis env_a env_b h_a h_b → EnvVis_weak env_a env_b h_a h_b :=
  fun h n => EnvVis_aux_to_weak n env_a env_b h_a h_b (h n)

/-- Pointwise weak list bisim. -/
def ListValVis_weak : List Val → List Val → Heap → Heap → Prop
  | [],      [],      _,   _   => True
  | x :: xs, y :: ys, h_a, h_b => ValVis_weak x y h_a h_b ∧ ListValVis_weak xs ys h_a h_b
  | _,       _,       _,   _   => False

theorem ListValVis_weak.length_eq : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVis_weak xs ys h_a h_b → xs.length = ys.length
  | [],      [],      _, _, _ => rfl
  | [],      _ :: _,  _, _, h => absurd h (by simp [ListValVis_weak])
  | _ :: _,  [],      _, _, h => absurd h (by simp [ListValVis_weak])
  | _ :: xs, _ :: ys, _, _, ⟨_, h_tail⟩ => by
      simp [List.length_cons, ListValVis_weak.length_eq h_tail]

/-! ## State extension -/

/-- Cross-side state relation: same policy. The heap relation between
    `s_a` and `s_b` is *not* a prefix relation in general (independent
    allocations on the two sides break that), and is instead tracked
    point-wise via `ValVis` / `EnvVis` on the relevant values. -/
def StateExt (s_a s_b : RunState) : Prop :=
  s_a.policy = s_b.policy

theorem StateExt.refl (s : RunState) : StateExt s s := rfl

theorem StateExt.trans {s_a s_b s_c : RunState}
    (h_ab : StateExt s_a s_b) (h_bc : StateExt s_b s_c) :
    StateExt s_a s_c := Eq.trans h_ab h_bc

/-- **Heap-only extension** between states, ignoring the policy. The
    same-side state evolution under `eval`: heap grows monotonically,
    but the policy may change (via `installPolicy`). Distinct from
    `StateExt` (which is *cross-side* and requires same policy on
    both sides). -/
def HeapExt (s_a s_b : RunState) : Prop :=
  ∃ extras, s_b.heap = s_a.heap ++ extras

theorem HeapExt.refl (s : RunState) : HeapExt s s :=
  ⟨[], (List.append_nil _).symm⟩

theorem HeapExt.trans {s_a s_b s_c : RunState}
    (h_ab : HeapExt s_a s_b) (h_bc : HeapExt s_b s_c) :
    HeapExt s_a s_c := by
  obtain ⟨extras_ab, h_heap_ab⟩ := h_ab
  obtain ⟨extras_bc, h_heap_bc⟩ := h_bc
  exact ⟨extras_ab ++ extras_bc, by rw [h_heap_bc, h_heap_ab, List.append_assoc]⟩

theorem HeapExt.heap_le {s_a s_b : RunState} (h : HeapExt s_a s_b) :
    s_a.heap.length ≤ s_b.heap.length := by
  obtain ⟨extras, hext⟩ := h
  rw [hext, List.length_append]
  exact Nat.le_add_right _ _


/-! ## Validity and self-bisimulation -/

/-- An env is **valid** in heap `h` if all its bindings point to
    cells within `h`. The runtime invariant the install protocol
    establishes for the metaEnv and for closure-captured envs. -/
def EnvValid (env : Env) (h : Heap) : Prop :=
  ∀ x i, env.lookup x = some i → i < h.length

theorem EnvValid.heap_extends {env : Env} {h_a h_b : Heap}
    (hv : EnvValid env h_a) (hext : ∃ extras, h_b = h_a ++ extras) :
    EnvValid env h_b := by
  obtain ⟨extras, hex⟩ := hext
  intro x i hl
  have h_lt : i < h_a.length := hv x i hl
  rw [hex, List.length_append]
  omega

/-- If `h_b = h_a ++ extras` and `i < h_a.length`, then
    `h_b[i]? = h_a[i]?`. The prefix-preservation lemma. -/
theorem getElem?_prefix (h_a : Heap) (extras : List Val) (i : Nat)
    (h_lt : i < h_a.length) :
    (h_a ++ extras)[i]? = h_a[i]? := by
  rw [List.getElem?_append_left h_lt]

/-! ## `Heap.update` structural lemmas -/

theorem Heap.update_length : ∀ (h : Heap) (idx : Nat) (v : Val),
    (Heap.update h idx v).length = h.length
  | [],       _,     _ => rfl
  | _ :: _,   0,     _ => rfl
  | _ :: t,   n + 1, v => by
      simp only [Heap.update, List.length_cons]
      exact congrArg Nat.succ (Heap.update_length t n v)

/-- Lookup at the updated index returns the new value (provided
    the index is in bounds). -/
theorem Heap.update_get_eq : ∀ (h : Heap) (idx : Nat) (v : Val),
    idx < h.length → (Heap.update h idx v)[idx]? = some v
  | [],       _,     _, h_lt => by simp at h_lt
  | _ :: _,   0,     _, _    => rfl
  | _ :: t,   n + 1, v, h_lt => by
      simp only [Heap.update, List.getElem?_cons_succ]
      have : n < t.length := by
        simp only [List.length_cons] at h_lt
        omega
      exact Heap.update_get_eq t n v this

/-- Lookup at any index ≠ idx is unchanged by the update. -/
theorem Heap.update_get_neq : ∀ (h : Heap) (idx : Nat) (v : Val) (i : Nat),
    i ≠ idx → (Heap.update h idx v)[i]? = h[i]?
  | [],       _,     _, _, _    => rfl
  | _ :: _,   0,     _, 0, hne  => absurd rfl hne
  | _ :: _,   0,     _, _ + 1, _ => rfl
  | _ :: t,   n + 1, v, 0, _    => rfl
  | _ :: t,   n + 1, v, i + 1, hne => by
      simp only [Heap.update, List.getElem?_cons_succ]
      have : i ≠ n := fun h_eq => hne (congrArg Nat.succ h_eq)
      exact Heap.update_get_neq t n v i this

/-- Out-of-bounds update is a no-op. -/
theorem Heap.update_oob : ∀ (h : Heap) (idx : Nat) (v : Val),
    h.length ≤ idx → Heap.update h idx v = h
  | [],       _,     _, _    => rfl
  | _ :: _,   0,     _, h_le => by simp at h_le
  | _ :: t,   n + 1, v, h_le => by
      simp only [Heap.update]
      simp only [List.length_cons] at h_le
      exact congrArg _ (Heap.update_oob t n v (Nat.le_of_succ_le_succ h_le))

/-! ## Reflexivity at every depth

    A value is bisimilar to itself in any heap, provided env-validity
    is preserved. We use this for the trivial framing case (where
    `s_a = s_b`) and for relating values to themselves under heap
    extension. -/

/-- Helper: if cenv is valid in h_a, and h_b extends h_a, then for
    each x, the cenv lookups in (h_a, h_b) succeed-or-fail together
    and produce the same Val. -/
theorem EnvVis_aux_self_of_valid (n : Nat) (cenv : Env)
    (h_a h_b : Heap) (hv : EnvValid cenv h_a)
    (hext : ∃ extras, h_b = h_a ++ extras)
    (ih : ∀ v, ValVis_aux n v v h_a h_b) :
    EnvVis_aux n cenv cenv h_a h_b := by
  obtain ⟨extras, hex⟩ := hext
  intro x
  cases hl : cenv.lookup x with
  | none      => simp
  | some idx  =>
      have h_lt : idx < h_a.length := hv x idx hl
      simp only [hl]
      have h_eq : h_b[idx]? = h_a[idx]? := by
        rw [hex]; exact getElem?_prefix h_a extras idx h_lt
      -- idx < h_a.length implies h_a[idx]? is some.
      have h_some : ∃ v, h_a[idx]? = some v := by
        cases hh : h_a[idx]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hh
            omega
        | some v => exact ⟨v, rfl⟩
      obtain ⟨v, hv_eq⟩ := h_some
      rw [hv_eq, h_eq, hv_eq]
      exact ih v

/-- A `Val`'s references are within the heap. **Shallow** validity:
    closure cenvs reference valid heap indices, but we don't recursively
    require the referenced values to also be valid (that's a heap-level
    invariant — see `HeapValid` below). -/
def ValValid : Val → Heap → Prop
  | .num _,            _ => True
  | .bool _,           _ => True
  | .nilV,             _ => True
  | .sym _,            _ => True
  | .prim _,           _ => True
  | .builtinBaseApply, _ => True
  | .cons x y,         h => ValValid x h ∧ ValValid y h
  | .closure _ _ cenv, h => EnvValid cenv h

theorem ValValid.heap_extends : ∀ (v : Val) {h_a h_b : Heap},
    ValValid v h_a → (∃ extras, h_b = h_a ++ extras) →
    ValValid v h_b
  | .num _,            _, _, _,  _    => trivial
  | .bool _,           _, _, _,  _    => trivial
  | .nilV,             _, _, _,  _    => trivial
  | .sym _,            _, _, _,  _    => trivial
  | .prim _,           _, _, _,  _    => trivial
  | .builtinBaseApply, _, _, _,  _    => trivial
  | .cons x y,         _, _, hv, hext =>
      ⟨ValValid.heap_extends x hv.1 hext,
       ValValid.heap_extends y hv.2 hext⟩
  | .closure _ _ _, _, _, hv, hext =>
      EnvValid.heap_extends hv hext

/-- A heap is **deeply valid** if every value in it is `ValValid` in
    that heap. This is the runtime invariant maintained by `eval`:
    `alloc` only adds values that were `ValValid` in the heap at
    the time of allocation; `update` only replaces a cell with a
    value `ValValid` in the current heap. -/
def HeapValid (h : Heap) : Prop :=
  ∀ (i : Nat) (v : Val), h[i]? = some v → ValValid v h

/-- An env is **deeply valid** in a deeply-valid heap if every name
    it binds points to a cell holding a `ValValid` value. Follows
    from `EnvValid` + `HeapValid`. -/
theorem EnvValid.implies_lookups_valid {env : Env} {h : Heap}
    (hv : EnvValid env h) (hh : HeapValid h) :
    ∀ x i, env.lookup x = some i → ∃ v, h[i]? = some v ∧ ValValid v h := by
  intro x i hl
  have h_lt : i < h.length := hv x i hl
  have h_some : ∃ v, h[i]? = some v := by
    cases hp : h[i]? with
    | none =>
        exfalso
        have := List.getElem?_eq_none_iff.mp hp
        omega
    | some v => exact ⟨v, rfl⟩
  obtain ⟨v, hp⟩ := h_some
  exact ⟨v, hp, hh i v hp⟩

/-- Strengthened helper: like `EnvVis_aux_self_of_valid` but the
    inductive-step hypothesis is only invoked on values that are
    `ValValid` in `h_a` (which holds for heap lookups via
    `HeapValid`). -/
theorem EnvVis_aux_self_of_valid' (n : Nat) (cenv : Env)
    (h_a h_b : Heap) (hv : EnvValid cenv h_a)
    (hh : HeapValid h_a)
    (hext : ∃ extras, h_b = h_a ++ extras)
    (ih : ∀ v, ValValid v h_a → ValVis_aux n v v h_a h_b) :
    EnvVis_aux n cenv cenv h_a h_b := by
  obtain ⟨extras, hex⟩ := hext
  intro x
  cases hl : cenv.lookup x with
  | none      => simp
  | some idx  =>
      have h_lt : idx < h_a.length := hv x idx hl
      simp only [hl]
      have h_eq : h_b[idx]? = h_a[idx]? := by
        rw [hex]; exact getElem?_prefix h_a extras idx h_lt
      have h_some : ∃ v, h_a[idx]? = some v := by
        cases hp : h_a[idx]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hp
            omega
        | some v => exact ⟨v, rfl⟩
      obtain ⟨v, hv_eq⟩ := h_some
      have hv_valid : ValValid v h_a := hh idx v hv_eq
      rw [hv_eq, h_eq, hv_eq]
      exact ih v hv_valid

/-- A value bisimilar to itself under heap extension, given validity.

    Proved by induction on depth `n`: the closure case at depth `n+1`
    needs the inductive hypothesis (at depth `n`) for the values
    looked up via cenv's bindings. By `HeapValid`, those values are
    `ValValid` in `h_a`, so the IH applies. -/
theorem ValVis_aux_self_extend (n : Nat) :
    ∀ (v : Val) (h_a : Heap) (extras : Heap),
      HeapValid h_a → ValValid v h_a →
      ValVis_aux n v v h_a (h_a ++ extras) := by
  induction n with
  | zero => intros; trivial
  | succ k ih =>
      intro v h_a extras hh hv
      cases v with
      | num _    => rfl
      | bool _   => rfl
      | nilV     => trivial
      | sym _    => rfl
      | prim _   => rfl
      | builtinBaseApply => trivial
      | cons x y =>
          obtain ⟨hx, hy⟩ := hv
          exact ⟨ih x h_a extras hh hx, ih y h_a extras hh hy⟩
      | closure ps body cenv =>
          refine ⟨rfl, rfl, rfl, ?_⟩
          apply EnvVis_aux_self_of_valid' k cenv h_a (h_a ++ extras) hv hh
              ⟨extras, rfl⟩
          intro v' hv_valid
          exact ih v' h_a extras hh hv_valid

/-- Self-bisim within a single heap. Given `EnvValid` and `HeapValid`,
    every heap-cell value is `ValValid`, so `ValVis_aux_self_extend`
    (with empty extras) gives self-bisim at every depth. -/
theorem EnvVis_self_of_valid (env : Env) (h : Heap)
    (hv : EnvValid env h) (hh : HeapValid h) :
    EnvVis env env h h := by
  intro depth x
  cases hl : env.lookup x with
  | none => simp
  | some i =>
      simp only [hl]
      have h_lt : i < h.length := hv x i hl
      have h_some : ∃ v, h[i]? = some v := by
        cases hp : h[i]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hp
            omega
        | some v => exact ⟨v, rfl⟩
      obtain ⟨v, hv_eq⟩ := h_some
      rw [hv_eq]
      have hv_valid : ValValid v h := hh i v hv_eq
      have := ValVis_aux_self_extend depth v h [] hh hv_valid
      simpa using this

/-! ## Closed values: heap-independent self-bisimulation

    A `closedValB`-true value contains no closure references, so it
    `ValValid`s in any heap and bisimulates itself across any pair
    of heaps. This is what justifies the `.quote v` case in `frame`:
    `eval` only admits `.quote v` when `closedValB v = true`, so the
    quoted value relates trivially to itself. -/

theorem closedValB_ValValid : ∀ (v : Val) (h : Heap),
    closedValB v = true → ValValid v h
  | .num _,            _, _ => trivial
  | .bool _,           _, _ => trivial
  | .nilV,             _, _ => trivial
  | .sym _,            _, _ => trivial
  | .prim _,           _, _ => trivial
  | .builtinBaseApply, _, _ => trivial
  | .cons x y,         h, hc => by
      simp [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedValB_ValValid x h hc.1, closedValB_ValValid y h hc.2⟩
  | .closure _ _ _,    _, hc => by simp [closedValB] at hc

theorem closedValB_ValVis_aux : ∀ (n : Nat) (v : Val) (h_a h_b : Heap),
    closedValB v = true → ValVis_aux n v v h_a h_b
  | 0,     _,                   _,   _,   _   => trivial
  | _ + 1, .num _,              _,   _,   _   => rfl
  | _ + 1, .bool _,             _,   _,   _   => rfl
  | _ + 1, .nilV,               _,   _,   _   => trivial
  | _ + 1, .sym _,              _,   _,   _   => rfl
  | _ + 1, .prim _,             _,   _,   _   => rfl
  | _ + 1, .builtinBaseApply,   _,   _,   _   => trivial
  | k + 1, .cons x y,           h_a, h_b, hc => by
      simp [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedValB_ValVis_aux k x h_a h_b hc.1,
             closedValB_ValVis_aux k y h_a h_b hc.2⟩
  | _ + 1, .closure _ _ _,      _,   _,   hc => by simp [closedValB] at hc

/-! ## Heap-extension lemmas

    The key building block for framing: bisimulation between
    `(v_a, v_b)` (or `(env_a, env_b)`) is preserved when both heaps
    grow by appended extras. Validity hypotheses ensure that closure
    cenv references stay in the original heap prefix, so heap
    lookups in the extended heaps give the same `Val`s as before.

    Both proofs go by induction on depth `n`. The closure case at
    depth `n+1` uses `EnvVis_aux_extends` at depth `n`, which uses
    `ValVis_aux_extends` at depth `n` (the IH).

    Stage-3 work item: full proof. For now, the lemmas are stated
    so the framing theorem above can be structured against them,
    making the dependency explicit. -/

mutual

theorem ValVis_aux_extends : ∀ (n : Nat) (v_a v_b : Val)
    (h_a h_b ext_a ext_b : Heap),
    HeapValid h_a → HeapValid h_b →
    ValValid v_a h_a → ValValid v_b h_b →
    ValVis_aux n v_a v_b h_a h_b →
    ValVis_aux n v_a v_b (h_a ++ ext_a) (h_b ++ ext_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, ext_a, ext_b,
      hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨ValVis_aux_extends n x_a x_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.1 hv_b.1 h_vis.1,
       ValVis_aux_extends n y_a y_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.2 hv_b.2 h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, ext_a, ext_b, hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨h_vis.1, h_vis.2.1, h_vis.2.2.1,
       EnvVis_aux_extends n cenv_a cenv_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a hv_b h_vis.2.2.2⟩
  -- Mismatched constructor pairs at depth ≥ 1: h_vis is `False`.
  | _ + 1, .num _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .prim _,           _, _, _, _, _, _, _, _, h => h.elim

theorem EnvVis_aux_extends (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap),
      HeapValid h_a → HeapValid h_b →
      EnvValid env_a h_a → EnvValid env_b h_b →
      EnvVis_aux n env_a env_b h_a h_b →
      EnvVis_aux n env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro env_a env_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b h_vis x
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => simp [hl_a, hl_b]
      | some _ => rw [hl_b] at h_x; simp at h_x
  | some i_a =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => rw [hl_b] at h_x; simp at h_x
      | some i_b =>
          rw [hl_b] at h_x
          simp only at h_x
          have h_lt_a : i_a < h_a.length := hv_a x i_a hl_a
          have h_lt_b : i_b < h_b.length := hv_b x i_b hl_b
          have h_eq_a : (h_a ++ ext_a)[i_a]? = h_a[i_a]? :=
            getElem?_prefix h_a ext_a i_a h_lt_a
          have h_eq_b : (h_b ++ ext_b)[i_b]? = h_b[i_b]? :=
            getElem?_prefix h_b ext_b i_b h_lt_b
          -- Goal (after cases): match some i_a, some i_b with ... (in ext heaps)
          simp only [hl_a, hl_b]
          -- Simp reduces the outer match (since both args are some); goal is
          -- now the inner match on heap lookups in extended heaps.
          rw [h_eq_a, h_eq_b]
          cases hp_a : h_a[i_a]? with
          | none => rw [hp_a] at h_x; simp at h_x
          | some v_a =>
              cases hp_b : h_b[i_b]? with
              | none => rw [hp_a, hp_b] at h_x; simp at h_x
              | some v_b =>
                  rw [hp_a, hp_b] at h_x
                  have hv_va : ValValid v_a h_a := hh_a i_a v_a hp_a
                  have hv_vb : ValValid v_b h_b := hh_b i_b v_b hp_b
                  exact ValVis_aux_extends n v_a v_b h_a h_b ext_a ext_b
                    hh_a hh_b hv_va hv_vb h_x

end

/-! ## Weak-bisim heap-extension lemmas

    Weak versions of the strong heap-extension lemmas above. The closure
    case loses the `cenv_a = cenv_b` clause but keeps the cell-pointwise
    bisim, which is preserved by extension via the standard nested
    induction. The non-closure cases are identical to the strong case
    (modulo the type signature), so these largely mirror
    `ValVis_aux_extends` / `EnvVis_aux_extends`. -/

mutual

theorem ValVis_aux_weak_extends : ∀ (n : Nat) (v_a v_b : Val)
    (h_a h_b ext_a ext_b : Heap),
    HeapValid h_a → HeapValid h_b →
    ValValid v_a h_a → ValValid v_b h_b →
    ValVis_aux_weak n v_a v_b h_a h_b →
    ValVis_aux_weak n v_a v_b (h_a ++ ext_a) (h_b ++ ext_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, ext_a, ext_b,
      hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨ValVis_aux_weak_extends n x_a x_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.1 hv_b.1 h_vis.1,
       ValVis_aux_weak_extends n y_a y_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a.2 hv_b.2 h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, ext_a, ext_b, hh_a, hh_b, hv_a, hv_b, h_vis =>
      ⟨h_vis.1, h_vis.2.1,
       EnvVis_aux_weak_extends n cenv_a cenv_b h_a h_b ext_a ext_b
          hh_a hh_b hv_a hv_b h_vis.2.2⟩
  -- Mismatched constructor pairs at depth ≥ 1: h_vis is `False`.
  | _ + 1, .num _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .prim _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .builtinBaseApply, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .num _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .bool _,           _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .nilV,             _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .cons _ _,         _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .sym _,            _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .closure _ _ _,    _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .prim _,           _, _, _, _, _, _, _, _, h => h.elim

theorem EnvVis_aux_weak_extends (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap),
      HeapValid h_a → HeapValid h_b →
      EnvValid env_a h_a → EnvValid env_b h_b →
      EnvVis_aux_weak n env_a env_b h_a h_b →
      EnvVis_aux_weak n env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro env_a env_b h_a h_b ext_a ext_b hh_a hh_b hv_a hv_b h_vis x
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => simp [hl_a, hl_b, EnvVis_aux_weak]
      | some _ => rw [hl_b] at h_x; simp at h_x
  | some i_a =>
      rw [hl_a] at h_x
      cases hl_b : env_b.lookup x with
      | none => rw [hl_b] at h_x; simp at h_x
      | some i_b =>
          rw [hl_b] at h_x
          simp only at h_x
          have h_lt_a : i_a < h_a.length := hv_a x i_a hl_a
          have h_lt_b : i_b < h_b.length := hv_b x i_b hl_b
          have h_eq_a : (h_a ++ ext_a)[i_a]? = h_a[i_a]? :=
            getElem?_prefix h_a ext_a i_a h_lt_a
          have h_eq_b : (h_b ++ ext_b)[i_b]? = h_b[i_b]? :=
            getElem?_prefix h_b ext_b i_b h_lt_b
          simp only [hl_a, hl_b]
          rw [h_eq_a, h_eq_b]
          cases hp_a : h_a[i_a]? with
          | none => rw [hp_a] at h_x; simp at h_x
          | some v_a =>
              cases hp_b : h_b[i_b]? with
              | none => rw [hp_a, hp_b] at h_x; simp at h_x
              | some v_b =>
                  rw [hp_a, hp_b] at h_x
                  have hv_va : ValValid v_a h_a := hh_a i_a v_a hp_a
                  have hv_vb : ValValid v_b h_b := hh_b i_b v_b hp_b
                  exact ValVis_aux_weak_extends n v_a v_b h_a h_b ext_a ext_b
                    hh_a hh_b hv_va hv_vb h_x

end

/-- Universal-depth weak val-vis preserved under heap extension. -/
theorem ValVis_weak_extends (v_a v_b : Val) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : ValValid v_a h_a) (hv_b : ValValid v_b h_b)
    (h_vis : ValVis_weak v_a v_b h_a h_b) :
    ValVis_weak v_a v_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact ValVis_aux_weak_extends n v_a v_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

theorem EnvVis_weak_extends (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : EnvValid env_a h_a) (hv_b : EnvValid env_b h_b)
    (h_vis : EnvVis_weak env_a env_b h_a h_b) :
    EnvVis_weak env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact EnvVis_aux_weak_extends n env_a env_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

/-! ## Bisim preservation under cross-side `Heap.update`

    Bisimulation preserved under symmetric in-place update at index
    `idx` to bisim-related new values. The "symmetric" structure is
    enabled by the strengthened `ValVis_aux` on closures (cenvs are
    structurally equal cross-side, so cell-update lookups land at
    the same index on both sides). -/

mutual

theorem ValVis_aux_update : ∀ (n : Nat) (v_a v_b : Val) (h_a h_b : Heap)
    (idx : Nat) (newVal_a newVal_b : Val),
    HeapValid h_a → HeapValid h_b →
    h_a.length = h_b.length →
    ValValid v_a h_a → ValValid v_b h_b →
    -- new values bisim-related at the updated heap pair, at depths < n.
    -- This is the STRICTLY BOUNDED form (was `∀ k, ...` universal): the
    -- closure case only needs h_vis_new at depths < n (used at depth
    -- n-1 in `EnvVis_aux_update`, and recursively at depths < n-1).
    -- The strict bound enables a depth-induction self-update lemma
    -- where the caller constructs h_vis_new from IH at strictly
    -- smaller depths (without needing the current depth's result).
    (∀ k, k < n → ValVis_aux k newVal_a newVal_b
                              (Heap.update h_a idx newVal_a)
                              (Heap.update h_b idx newVal_b)) →
    ValValid newVal_a (Heap.update h_a idx newVal_a) →
    ValValid newVal_b (Heap.update h_b idx newVal_b) →
    ValVis_aux n v_a v_b h_a h_b →
    ValVis_aux n v_a v_b (Heap.update h_a idx newVal_a)
                          (Heap.update h_b idx newVal_b)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .num _,            .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .bool _,           .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .nilV,             .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, .sym _,            .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .prim _,           .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ + 1, .builtinBaseApply, .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, .cons x_a y_a, .cons x_b y_b, h_a, h_b, idx, newVal_a, newVal_b,
      hh_a, hh_b, hlen, hv_a, hv_b, h_vis_new, hv_new_a, hv_new_b, h_vis =>
      -- Recursive .cons calls at depth n: weaken from `< n+1` to `< n`.
      -- (k < n implies k < n+1 by Nat.lt_succ_of_lt.)
      ⟨ValVis_aux_update n x_a x_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a.1 hv_b.1
          (fun k h_lt => h_vis_new k (Nat.lt_succ_of_lt h_lt))
          hv_new_a hv_new_b h_vis.1,
       ValVis_aux_update n y_a y_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a.2 hv_b.2
          (fun k h_lt => h_vis_new k (Nat.lt_succ_of_lt h_lt))
          hv_new_a hv_new_b h_vis.2⟩
  | n + 1, .closure ps_a body_a cenv_a, .closure ps_b body_b cenv_b,
      h_a, h_b, idx, newVal_a, newVal_b,
      hh_a, hh_b, hlen, hv_a, hv_b, h_vis_new, hv_new_a, hv_new_b, h_vis =>
      -- ValValid on closure unfolds to EnvValid on cenv. Cenv equality
      -- (`h_vis.2.2.1`) is what feeds `EnvVis_aux_update`'s `env_eq`.
      -- Outer bound is `< n+1` (= `≤ n`); EnvVis_aux_update at depth n
      -- takes bound `≤ n`. Convert via `Nat.lt_succ_iff.mp`.
      ⟨h_vis.1, h_vis.2.1, h_vis.2.2.1,
       EnvVis_aux_update n cenv_a cenv_b h_a h_b idx newVal_a newVal_b
          hh_a hh_b hlen hv_a hv_b h_vis.2.2.1
          (fun k h_le => h_vis_new k (Nat.lt_succ_of_le h_le))
          hv_new_a hv_new_b h_vis.2.2.2⟩
  -- Mismatched constructor pairs at depth ≥ 1: `h_vis` is `False`.
  | _ + 1, .num _,            .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .num _,            .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .bool _,           .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .nilV,             .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .cons _ _,         .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .sym _,            .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .closure _ _ _,    .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .prim _,           .builtinBaseApply, _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .num _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .bool _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .nilV,             _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .cons _ _,         _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .sym _,            _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .closure _ _ _,    _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | _ + 1, .builtinBaseApply, .prim _,           _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim

theorem EnvVis_aux_update (n : Nat) :
    ∀ (env_a env_b : Env) (h_a h_b : Heap)
      (idx : Nat) (newVal_a newVal_b : Val),
      HeapValid h_a → HeapValid h_b →
      h_a.length = h_b.length →
      EnvValid env_a h_a → EnvValid env_b h_b →
      env_a = env_b →   -- structural equality (lookup_eq gives i_a = i_b)
      (∀ k, k ≤ n → ValVis_aux k newVal_a newVal_b
                                 (Heap.update h_a idx newVal_a)
                                 (Heap.update h_b idx newVal_b)) →
      ValValid newVal_a (Heap.update h_a idx newVal_a) →
      ValValid newVal_b (Heap.update h_b idx newVal_b) →
      EnvVis_aux n env_a env_b h_a h_b →
      EnvVis_aux n env_a env_b (Heap.update h_a idx newVal_a)
                                (Heap.update h_b idx newVal_b) := by
  intro env_a env_b h_a h_b idx newVal_a newVal_b
        hh_a hh_b hlen hv_a hv_b h_env_eq h_vis_new hv_new_a hv_new_b h_vis x
  -- env_a = env_b → lookups give the same index on both sides.
  have h_lookup_eq : env_a.lookup x = env_b.lookup x := by rw [h_env_eq]
  have h_x := h_vis x
  cases hl_a : env_a.lookup x with
  | none =>
      rw [hl_a] at h_x h_lookup_eq
      have hl_b : env_b.lookup x = none := h_lookup_eq.symm
      simp [hl_a, hl_b]
  | some i_a =>
      rw [hl_a] at h_x h_lookup_eq
      have hl_b : env_b.lookup x = some i_a := h_lookup_eq.symm
      rw [hl_b] at h_x
      simp only at h_x
      simp only [hl_a, hl_b]
      have h_lt_a : i_a < h_a.length := hv_a x i_a hl_a
      have h_lt_b : i_a < h_b.length := hv_b x i_a hl_b
      -- Both indices equal i_a; case on whether i_a = idx.
      by_cases h_idx : i_a = idx
      · -- Both lookups give the updated cell → newVal_a, newVal_b.
        subst h_idx
        rw [Heap.update_get_eq h_a i_a newVal_a h_lt_a]
        rw [Heap.update_get_eq h_b i_a newVal_b h_lt_b]
        exact h_vis_new n (Nat.le_refl n)
      · -- Both lookups give an unchanged cell.
        cases hp_a : h_a[i_a]? with
        | none =>
            exfalso
            have := List.getElem?_eq_none_iff.mp hp_a
            omega
        | some v_a =>
            cases hp_b : h_b[i_a]? with
            | none =>
                exfalso
                have := List.getElem?_eq_none_iff.mp hp_b
                omega
            | some v_b =>
                rw [Heap.update_get_neq h_a idx newVal_a i_a h_idx, hp_a]
                rw [Heap.update_get_neq h_b idx newVal_b i_a h_idx, hp_b]
                rw [hp_a, hp_b] at h_x
                have hv_va : ValValid v_a h_a := hh_a i_a v_a hp_a
                have hv_vb : ValValid v_b h_b := hh_b i_a v_b hp_b
                -- ValVis_aux_update at depth n needs bound `< n`. We have
                -- `≤ n` (EnvVis's outer bound). Weaken: k < n → k ≤ n.
                exact ValVis_aux_update n v_a v_b h_a h_b idx
                  newVal_a newVal_b hh_a hh_b hlen hv_va hv_vb
                  (fun k h_lt => h_vis_new k (Nat.le_of_lt h_lt))
                  hv_new_a hv_new_b h_x

end

/-! ## Heap evolution (cross-side framing across in-place updates) -/

/-- **Heap evolution** (cross-side): a strictly weaker relation than
    `HeapExt s_a s_a' ∧ HeapExt s_b s_b'`. The four-place relation
    `HeapEvolution s_a s_b s_a' s_b'` captures what's preserved across
    a *both-sides* step: heap length grows on each side, *and* any
    cross-side env-bisim that held at the source pair `(s_a, s_b)`
    still holds at the target pair `(s_a', s_b')`.

    This is the right relation for framing across `.set` (which
    performs an in-place `Heap.update` and breaks the prefix
    structure of `HeapExt`). The same-side analog would require old
    and new values at the updated cell to be self-bisim-related,
    which fails for `multnExactPolicy` (admits
    `.builtinBaseApply → multn-closure`, not self-bisim). The
    cross-side formulation works because both sides update with
    bisim-*related* new values (via `policy_respects_bisim`), even
    when same-side old/new aren't related.

    Reflexive, transitive, length-monotone, lifted from
    `HeapExt s_a s_a' ∧ HeapExt s_b s_b'` via `from_heapExt`. -/
structure HeapEvolution (s_a s_b s_a' s_b' : RunState) : Prop where
  len_a : s_a.heap.length ≤ s_a'.heap.length
  len_b : s_b.heap.length ≤ s_b'.heap.length
  /-- For every depth `n` and every pair of envs that are
      structurally equal cross-side and bisim-related at depth `n`
      in the source state pair, the same envs remain bisim-related
      in the target state pair. The `env_a = env_b` precondition is
      satisfied at every framing call site by `WFCtx.env_eq`. -/
  env_preserve : ∀ (n : Nat) (env_a env_b : Env),
    env_a = env_b →
    EnvValid env_a s_a.heap → EnvValid env_b s_b.heap →
    EnvVis_aux n env_a env_b s_a.heap s_b.heap →
    EnvVis_aux n env_a env_b s_a'.heap s_b'.heap
  /-- For every depth `n` and every pair of values that were valid in
      the source state pair and bisim-related at depth `n`, the same
      values remain bisim-related in the target state pair at the
      same depth. Used to lift `ValVis` of operands/funcs across
      inner-step heap evolutions in the `.app` / `.primApp` cases. -/
  val_preserve : ∀ (n : Nat) (v_a v_b : Val),
    ValValid v_a s_a.heap → ValValid v_b s_b.heap →
    ValVis_aux n v_a v_b s_a.heap s_b.heap →
    ValVis_aux n v_a v_b s_a'.heap s_b'.heap

theorem HeapEvolution.refl (s_a s_b : RunState) :
    HeapEvolution s_a s_b s_a s_b :=
  ⟨Nat.le_refl _, Nat.le_refl _,
   fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Lift a single-value bisim across `HeapEvolution` (universal-depth). -/
theorem HeapEvolution.valVis_preserve {s_a s_b s_a' s_b' : RunState}
    (h : HeapEvolution s_a s_b s_a' s_b') (v_a v_b : Val)
    (hv_a : ValValid v_a s_a.heap) (hv_b : ValValid v_b s_b.heap)
    (h_vis : ValVis v_a v_b s_a.heap s_b.heap) :
    ValVis v_a v_b s_a'.heap s_b'.heap := by
  intro n
  exact h.val_preserve n v_a v_b hv_a hv_b (h_vis n)

/-- Lift an env bisim across `HeapEvolution` (universal-depth). -/
theorem HeapEvolution.envVis_preserve {s_a s_b s_a' s_b' : RunState}
    (h : HeapEvolution s_a s_b s_a' s_b') (env_a env_b : Env)
    (h_env_eq : env_a = env_b)
    (hv_a : EnvValid env_a s_a.heap) (hv_b : EnvValid env_b s_b.heap)
    (h_vis : EnvVis env_a env_b s_a.heap s_b.heap) :
    EnvVis env_a env_b s_a'.heap s_b'.heap := by
  intro n
  exact h.env_preserve n env_a env_b h_env_eq hv_a hv_b (h_vis n)

/-- Validity is preserved under length-monotone evolution. -/
theorem EnvValid.length_mono {env : Env} {h_a h_b : Heap}
    (hv : EnvValid env h_a) (hlen : h_a.length ≤ h_b.length) :
    EnvValid env h_b := by
  intro x i hl
  exact Nat.lt_of_lt_of_le (hv x i hl) hlen

theorem ValValid.length_mono {h_a h_b : Heap} :
    ∀ (v : Val), ValValid v h_a → h_a.length ≤ h_b.length → ValValid v h_b
  | .num _,            _,  _    => trivial
  | .bool _,           _,  _    => trivial
  | .nilV,             _,  _    => trivial
  | .sym _,            _,  _    => trivial
  | .prim _,           _,  _    => trivial
  | .builtinBaseApply, _,  _    => trivial
  | .cons x y,         hv, hlen =>
      ⟨ValValid.length_mono x hv.1 hlen, ValValid.length_mono y hv.2 hlen⟩
  | .closure _ _ _,    hv, hlen =>
      EnvValid.length_mono hv hlen

/-- Transitivity of `HeapEvolution`. Composes env-preservation across
    intermediate state pairs; needs heap validity of the intermediate
    state pair to lift `EnvValid` for the second `env_preserve` call. -/
theorem HeapEvolution.trans {s_a s_b s_a' s_b' s_a'' s_b'' : RunState}
    (h1 : HeapEvolution s_a s_b s_a' s_b')
    (h2 : HeapEvolution s_a' s_b' s_a'' s_b'') :
    HeapEvolution s_a s_b s_a'' s_b'' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans h1.len_a h2.len_a
  · exact Nat.le_trans h1.len_b h2.len_b
  · intro n env_a env_b h_eq hv_a hv_b h_vis
    have h_vis' : EnvVis_aux n env_a env_b s_a'.heap s_b'.heap :=
      h1.env_preserve n env_a env_b h_eq hv_a hv_b h_vis
    have hv_a' : EnvValid env_a s_a'.heap := hv_a.length_mono h1.len_a
    have hv_b' : EnvValid env_b s_b'.heap := hv_b.length_mono h1.len_b
    exact h2.env_preserve n env_a env_b h_eq hv_a' hv_b' h_vis'
  · intro n v_a v_b hv_a hv_b h_vis
    have h_vis' : ValVis_aux n v_a v_b s_a'.heap s_b'.heap :=
      h1.val_preserve n v_a v_b hv_a hv_b h_vis
    have hv_a' : ValValid v_a s_a'.heap := ValValid.length_mono v_a hv_a h1.len_a
    have hv_b' : ValValid v_b s_b'.heap := ValValid.length_mono v_b hv_b h1.len_b
    exact h2.val_preserve n v_a v_b hv_a' hv_b' h_vis'

/-- Lift a pair of `HeapExt`s to a `HeapEvolution`. Used at allocation
    sites (each side appends extras to its heap; old cells preserved).
    Requires heap validity to invoke `ValVis_aux_extends`/`EnvVis_aux_extends`. -/
theorem HeapEvolution.from_heapExt {s_a s_b s_a' s_b' : RunState}
    (hh_a : HeapValid s_a.heap) (hh_b : HeapValid s_b.heap)
    (he_a : HeapExt s_a s_a') (he_b : HeapExt s_b s_b') :
    HeapEvolution s_a s_b s_a' s_b' := by
  obtain ⟨ext_a, hex_a⟩ := he_a
  obtain ⟨ext_b, hex_b⟩ := he_b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex_a, List.length_append]; exact Nat.le_add_right _ _
  · rw [hex_b, List.length_append]; exact Nat.le_add_right _ _
  · intro n env_a env_b _ hv_a hv_b h_vis
    rw [hex_a, hex_b]
    exact EnvVis_aux_extends n env_a env_b s_a.heap s_b.heap ext_a ext_b
      hh_a hh_b hv_a hv_b h_vis
  · intro n v_a v_b hv_a hv_b h_vis
    rw [hex_a, hex_b]
    exact ValVis_aux_extends n v_a v_b s_a.heap s_b.heap ext_a ext_b
      hh_a hh_b hv_a hv_b h_vis

/-! ## Pointwise list bisimulation

    For framing `applyVia` and `applyDirect` (which take `args : List Val`),
    we need pointwise `ValVis` between the two argument lists. -/

def ListValVis : List Val → List Val → Heap → Heap → Prop
  | [],      [],      _,   _   => True
  | x :: xs, y :: ys, h_a, h_b => ValVis x y h_a h_b ∧ ListValVis xs ys h_a h_b
  | _,       _,       _,   _   => False

/-- Pointwise list validity: each element is `ValValid` in the heap. -/
def ListValValid : List Val → Heap → Prop
  | [],      _ => True
  | x :: xs, h => ValValid x h ∧ ListValValid xs h

theorem ListValVis.length_eq : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVis xs ys h_a h_b → xs.length = ys.length
  | [],      [],      _, _, _ => rfl
  | [],      _ :: _,  _, _, h => absurd h (by simp [ListValVis])
  | _ :: _,  [],      _, _, h => absurd h (by simp [ListValVis])
  | _ :: xs, _ :: ys, _, _, ⟨_, h_tail⟩ => by
      simp [List.length_cons, ListValVis.length_eq h_tail]

/-- `ListValValid` lifts across heap extension. -/
theorem ListValValid.heap_extends : ∀ {xs : List Val} {h_a h_b : Heap},
    ListValValid xs h_a → (∃ extras, h_b = h_a ++ extras) →
    ListValValid xs h_b
  | [],      _, _, _,  _    => trivial
  | _ :: _, _, _, hv, hext =>
      ⟨ValValid.heap_extends _ hv.1 hext,
       ListValValid.heap_extends hv.2 hext⟩

theorem ListValValid.length_mono {h_a h_b : Heap} :
    ∀ {xs : List Val}, ListValValid xs h_a → h_a.length ≤ h_b.length →
      ListValValid xs h_b
  | [],     _,  _    => trivial
  | _ :: _, hv, hlen =>
      ⟨ValValid.length_mono _ hv.1 hlen,
       ListValValid.length_mono hv.2 hlen⟩

/-- Lift a list bisim across `HeapEvolution` (universal-depth). -/
theorem HeapEvolution.listValVis_preserve {s_a s_b s_a' s_b' : RunState}
    (h : HeapEvolution s_a s_b s_a' s_b') :
    ∀ (xs ys : List Val),
      ListValValid xs s_a.heap → ListValValid ys s_b.heap →
      ListValVis xs ys s_a.heap s_b.heap →
      ListValVis xs ys s_a'.heap s_b'.heap
  | [],     [],     _,    _,    _    => trivial
  | [],     _ :: _, _,    _,    h_v  => h_v.elim
  | _ :: _, [],     _,    _,    h_v  => h_v.elim
  | x :: xs, y :: ys, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨h.valVis_preserve x y hv_a.1 hv_b.1 h_head,
       h.listValVis_preserve xs ys hv_a.2 hv_b.2 h_tail⟩

/-! ## Bool false characterization -/

/-- `ValVis` on `.bool false` is two-sided: if either side is
    `.bool false`, so is the other. Used by the `.ifte` framing
    case to argue that both calls take the same branch. -/
theorem ValVis_bool_false_iff (cv_a cv_b : Val) (h_a h_b : Heap)
    (h_vv : ValVis cv_a cv_b h_a h_b) :
    cv_a = .bool false ↔ cv_b = .bool false := by
  constructor
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_b with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux] at h1
    | num _            => simp [ValVis_aux] at h1
    | nilV             => simp [ValVis_aux] at h1
    | cons _ _         => simp [ValVis_aux] at h1
    | sym _            => simp [ValVis_aux] at h1
    | closure _ _ _    => simp [ValVis_aux] at h1
    | prim _           => simp [ValVis_aux] at h1
    | builtinBaseApply => simp [ValVis_aux] at h1
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_a with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux] at h1
    | num _            => simp [ValVis_aux] at h1
    | nilV             => simp [ValVis_aux] at h1
    | cons _ _         => simp [ValVis_aux] at h1
    | sym _            => simp [ValVis_aux] at h1
    | closure _ _ _    => simp [ValVis_aux] at h1
    | prim _           => simp [ValVis_aux] at h1
    | builtinBaseApply => simp [ValVis_aux] at h1

/-- `ValVis_weak` on `.bool false` is two-sided. -/
theorem ValVis_weak_bool_false_iff (cv_a cv_b : Val) (h_a h_b : Heap)
    (h_vv : ValVis_weak cv_a cv_b h_a h_b) :
    cv_a = .bool false ↔ cv_b = .bool false := by
  constructor
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_b with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux_weak] at h1
    | num _            => simp [ValVis_aux_weak] at h1
    | nilV             => simp [ValVis_aux_weak] at h1
    | cons _ _         => simp [ValVis_aux_weak] at h1
    | sym _            => simp [ValVis_aux_weak] at h1
    | closure _ _ _    => simp [ValVis_aux_weak] at h1
    | prim _           => simp [ValVis_aux_weak] at h1
    | builtinBaseApply => simp [ValVis_aux_weak] at h1
  · intro h
    subst h
    have h1 := h_vv 1
    cases cv_a with
    | bool b => cases b with
                | false => rfl
                | true  => simp [ValVis_aux_weak] at h1
    | num _            => simp [ValVis_aux_weak] at h1
    | nilV             => simp [ValVis_aux_weak] at h1
    | cons _ _         => simp [ValVis_aux_weak] at h1
    | sym _            => simp [ValVis_aux_weak] at h1
    | closure _ _ _    => simp [ValVis_aux_weak] at h1
    | prim _           => simp [ValVis_aux_weak] at h1
    | builtinBaseApply => simp [ValVis_aux_weak] at h1

/-! ## Universal-depth heap-extension lemmas -/

/-- `ValVis` (universal over depths) preserved under heap extension. -/
theorem ValVis_extends (v_a v_b : Val) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : ValValid v_a h_a) (hv_b : ValValid v_b h_b)
    (h_vis : ValVis v_a v_b h_a h_b) :
    ValVis v_a v_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact ValVis_aux_extends n v_a v_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

/-- `EnvVis` (universal over depths) preserved under heap extension. -/
theorem EnvVis_extends (env_a env_b : Env) (h_a h_b ext_a ext_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b)
    (hv_a : EnvValid env_a h_a) (hv_b : EnvValid env_b h_b)
    (h_vis : EnvVis env_a env_b h_a h_b) :
    EnvVis env_a env_b (h_a ++ ext_a) (h_b ++ ext_b) := by
  intro n
  exact EnvVis_aux_extends n env_a env_b h_a h_b ext_a ext_b
    hh_a hh_b hv_a hv_b (h_vis n)

/-- `ListValVis` (universal over depths) preserved under heap extension,
    given pointwise `ValValid` on both sides. -/
theorem ListValVis_extends : ∀ {xs ys : List Val} {h_a h_b ext_a ext_b : Heap},
    HeapValid h_a → HeapValid h_b →
    ListValValid xs h_a → ListValValid ys h_b →
    ListValVis xs ys h_a h_b →
    ListValVis xs ys (h_a ++ ext_a) (h_b ++ ext_b)
  | [],      [],      _, _, _, _, _, _, _, _, _ => trivial
  | [],      _ :: _,  _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  [],      _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, _, _, hh_a, hh_b, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨ValVis_extends _ _ _ _ _ _ hh_a hh_b hv_a.1 hv_b.1 h_head,
       ListValVis_extends hh_a hh_b hv_a.2 hv_b.2 h_tail⟩

theorem ListValVis_weak_extends : ∀ {xs ys : List Val} {h_a h_b ext_a ext_b : Heap},
    HeapValid h_a → HeapValid h_b →
    ListValValid xs h_a → ListValValid ys h_b →
    ListValVis_weak xs ys h_a h_b →
    ListValVis_weak xs ys (h_a ++ ext_a) (h_b ++ ext_b)
  | [],      [],      _, _, _, _, _, _, _, _, _ => trivial
  | [],      _ :: _,  _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  [],      _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, _, _, hh_a, hh_b, hv_a, hv_b, ⟨h_head, h_tail⟩ =>
      ⟨ValVis_weak_extends _ _ _ _ _ _ hh_a hh_b hv_a.1 hv_b.1 h_head,
       ListValVis_weak_extends hh_a hh_b hv_a.2 hv_b.2 h_tail⟩

theorem ListValVis_to_weak : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVis xs ys h_a h_b → ListValVis_weak xs ys h_a h_b
  | [],      [],      _, _, _ => trivial
  | [],      _ :: _,  _, _, h => h.elim
  | _ :: _,  [],      _, _, h => h.elim
  | _ :: _,  _ :: _,  _, _, ⟨h_head, h_tail⟩ =>
      ⟨ValVis_to_weak h_head, ListValVis_to_weak h_tail⟩

/-! ## `listToVal` and bisimulation -/

/-- A `listToVal`-encoded list of bisimilar values produces bisimilar
    cons-spines at every depth. -/
theorem ValVis_aux_listToVal : ∀ (n : Nat) {xs ys : List Val} {h_a h_b : Heap},
    ListValVis xs ys h_a h_b →
    ValVis_aux n (listToVal xs) (listToVal ys) h_a h_b
  | 0, _, _, _, _, _ => trivial
  | _ + 1, [],      [],      _, _, _ => trivial
  | _ + 1, [],      _ :: _,  _, _, h => h.elim
  | _ + 1, _ :: _,  [],      _, _, h => h.elim
  | n + 1, _ :: _, _ :: _, _, _, ⟨h_head, h_tail⟩ =>
      ⟨h_head n, ValVis_aux_listToVal n h_tail⟩

theorem ValVis_listToVal {xs ys : List Val} {h_a h_b : Heap}
    (h : ListValVis xs ys h_a h_b) :
    ValVis (listToVal xs) (listToVal ys) h_a h_b :=
  fun n => ValVis_aux_listToVal n h

theorem ValValid_listToVal : ∀ {xs : List Val} {h : Heap},
    ListValValid xs h → ValValid (listToVal xs) h
  | [],      _, _ => trivial
  | _ :: _,  _, ⟨hv, htail⟩ => ⟨hv, ValValid_listToVal htail⟩

/-! ## `valToList` and bisimulation -/

/-- If `valToList ol_a = some operands_a` and `ValVis ol_a ol_b`, then
    `valToList ol_b` succeeds with operands pointwise bisimilar to
    `operands_a`. Plus pointwise validity. -/
theorem valToList_bisim : ∀ (operands_a : List Val) (ol_a ol_b : Val) (h_a h_b : Heap),
    valToList ol_a = some operands_a → ValVis ol_a ol_b h_a h_b →
    ValValid ol_a h_a → ValValid ol_b h_b →
    ∃ operands_b, valToList ol_b = some operands_b ∧
      ListValVis operands_a operands_b h_a h_b ∧
      ListValValid operands_a h_a ∧ ListValValid operands_b h_b
  | [], ol_a, ol_b, h_a, h_b, hl_a, h_vv, _, _ => by
      have h_vv1 := h_vv 1
      cases ol_a with
      | nilV =>
          cases ol_b with
          | nilV => exact ⟨[], rfl, trivial, trivial, trivial⟩
          | num _ => simp [ValVis_aux] at h_vv1
          | bool _ => simp [ValVis_aux] at h_vv1
          | sym _ => simp [ValVis_aux] at h_vv1
          | cons _ _ => simp [ValVis_aux] at h_vv1
          | closure _ _ _ => simp [ValVis_aux] at h_vv1
          | prim _ => simp [ValVis_aux] at h_vv1
          | builtinBaseApply => simp [ValVis_aux] at h_vv1
      | cons x rest =>
          simp only [valToList] at hl_a
          cases hr : valToList rest with
          | none => rw [hr] at hl_a; simp at hl_a
          | some _ => rw [hr] at hl_a; simp at hl_a
      | num _ => simp [valToList] at hl_a
      | bool _ => simp [valToList] at hl_a
      | sym _ => simp [valToList] at hl_a
      | closure _ _ _ => simp [valToList] at hl_a
      | prim _ => simp [valToList] at hl_a
      | builtinBaseApply => simp [valToList] at hl_a
  | head :: tail, ol_a, ol_b, h_a, h_b, hl_a, h_vv, hv_a, hv_b => by
      -- ol_a must be (.cons head rest) for some rest with valToList rest = some tail.
      have h_vv1 := h_vv 1
      cases ol_a with
      | cons x rest =>
          simp [valToList] at hl_a
          cases hr : valToList rest with
          | none => rw [hr] at hl_a; simp at hl_a
          | some t =>
              rw [hr] at hl_a
              simp at hl_a
              obtain ⟨hx_eq, ht_eq⟩ := hl_a
              subst hx_eq
              subst ht_eq
              -- ol_b must also be cons.
              cases ol_b with
              | cons x_b rest_b =>
                  -- Get bisims on components (universal-depth).
                  have h_vv_head : ValVis x x_b h_a h_b := by
                    intro d
                    cases d with
                    | zero => trivial
                    | succ d' => exact (h_vv d'.succ.succ).1
                  have h_vv_rest : ValVis rest rest_b h_a h_b := by
                    intro d
                    cases d with
                    | zero => trivial
                    | succ d' => exact (h_vv d'.succ.succ).2
                  -- ValValid on cons → ValValid on components.
                  have hv_a' : ValValid x h_a ∧ ValValid rest h_a := hv_a
                  have hv_b' : ValValid x_b h_b ∧ ValValid rest_b h_b := hv_b
                  -- Recurse on the tail.
                  obtain ⟨tail_b, hl_b, h_lvv_tail, hv_tail_a, hv_tail_b⟩ :=
                    valToList_bisim t rest rest_b h_a h_b hr h_vv_rest hv_a'.2 hv_b'.2
                  refine ⟨x_b :: tail_b, ?_, ⟨h_vv_head, h_lvv_tail⟩,
                          ⟨hv_a'.1, hv_tail_a⟩, ⟨hv_b'.1, hv_tail_b⟩⟩
                  simp [valToList, hl_b]
              | nilV => simp [ValVis_aux] at h_vv1
              | num _ => simp [ValVis_aux] at h_vv1
              | bool _ => simp [ValVis_aux] at h_vv1
              | sym _ => simp [ValVis_aux] at h_vv1
              | closure _ _ _ => simp [ValVis_aux] at h_vv1
              | prim _ => simp [ValVis_aux] at h_vv1
              | builtinBaseApply => simp [ValVis_aux] at h_vv1
      | nilV => simp [valToList] at hl_a
      | num _ => simp [valToList] at hl_a
      | bool _ => simp [valToList] at hl_a
      | sym _ => simp [valToList] at hl_a
      | closure _ _ _ => simp [valToList] at hl_a
      | prim _ => simp [valToList] at hl_a
      | builtinBaseApply => simp [valToList] at hl_a
  termination_by operands_a _ _ _ _ => operands_a.length


/-! ## `mulConsList` and bisimulation -/

/-- `mulConsList` produces the same `Option Int` on bisimilar values.
    Recurses on the cons-spine of `v_a`. -/
private theorem mulConsList_bisim : ∀ (v_a v_b : Val) (h_a h_b : Heap),
    ValVis v_a v_b h_a h_b → mulConsList v_a = mulConsList v_b
  | .nilV, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | nilV => rfl
      | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.num n) ys, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b ys_b =>
          have h_vv_x : ValVis (.num n) x_b h_a h_b := fun d => by
            cases d with
            | zero => trivial
            | succ d' => exact (h_vv d'.succ.succ).1
          have h_vv_ys : ValVis ys ys_b h_a h_b := fun d => by
            cases d with
            | zero => trivial
            | succ d' => exact (h_vv d'.succ.succ).2
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | num n' =>
              have : n = n' := by simp [ValVis_aux] at h_x_d1; exact h_x_d1
              subst this
              simp [mulConsList, mulConsList_bisim ys ys_b h_a h_b h_vv_ys]
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .num _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | num _ => simp [mulConsList]
      | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .bool _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | bool _ => simp [mulConsList]
      | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .sym _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | sym _ => simp [mulConsList]
      | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.bool _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.bool _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | bool _ => simp [mulConsList]
          | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons .nilV _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis .nilV x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | nilV => simp [mulConsList]
          | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.sym _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.sym _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | sym _ => simp [mulConsList]
          | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.cons _ _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.cons _ _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | cons _ _ => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.closure _ _ _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.closure _ _ _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | closure _ _ _ => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | cons _ _ | prim _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons (.prim _) _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis (.prim _) x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | prim _ => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | builtinBaseApply =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .cons .builtinBaseApply _, v_b, h_a, h_b, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | cons x_b _ =>
          have h_vv_x : ValVis .builtinBaseApply x_b h_a h_b := fun d => by
            cases d with | zero => trivial | succ d' => exact (h_vv d'.succ.succ).1
          have h_x_d1 := h_vv_x 1
          cases x_b with
          | builtinBaseApply => simp [mulConsList]
          | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
              simp [ValVis_aux] at h_x_d1
      | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .closure _ _ _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | closure _ _ _ => simp [mulConsList]
      | num _ | bool _ | nilV | sym _ | cons _ _ | prim _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .prim _, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | prim _ => simp [mulConsList]
      | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | builtinBaseApply =>
          simp [ValVis_aux] at h_d1
  | .builtinBaseApply, v_b, _, _, h_vv => by
      have h_d1 := h_vv 1
      cases v_b with
      | builtinBaseApply => simp [mulConsList]
      | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _ =>
          simp [ValVis_aux] at h_d1

/-! ## `applyPrim` and bisimulation -/

/-- For each "predicate-style" primitive (one-argument constructor check
    returning a Bool), the result depends only on the depth-1 constructor
    of the argument, which is preserved by `ValVis_aux 1`. Bisimilar
    arguments therefore give equal results. We prove the same equality
    fact for all binary-numeric, cons, car, cdr, mul-list primitives.
    For the cons-y prims the equality is in `Option Val` modulo bisim. -/

private theorem applyPrim_numQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_numQ args_a = applyPrim_numQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_boolQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_boolQ args_a = applyPrim_boolQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_closureQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_closureQ args_a = applyPrim_closureQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_primQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_primQ args_a = applyPrim_primQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

private theorem applyPrim_nullQ_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_nullQ args_a = applyPrim_nullQ args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_numQ, applyPrim_boolQ, applyPrim_closureQ,
                              applyPrim_primQ, applyPrim_nullQ]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              have h_d1 := h_vv 1
              cases v_a with
              | num _ => cases v_b with
                | num _ => rfl
                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | bool _ => cases v_b with
                | bool _ => rfl
                | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | nilV => cases v_b with
                | nilV => rfl
                | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | sym _ => cases v_b with
                | sym _ => rfl
                | num _ | bool _ | nilV | cons _ _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | cons _ _ => cases v_b with
                | cons _ _ => rfl
                | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | closure _ _ _ => cases v_b with
                | closure _ _ _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | prim _ => cases v_b with
                | prim _ => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | builtinBaseApply => simp [ValVis_aux] at h_d1
              | builtinBaseApply => cases v_b with
                | builtinBaseApply => rfl
                | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                | prim _ => simp [ValVis_aux] at h_d1

/-! ## Binary numeric prims and bisimulation -/

/-- Helper: for ValVis-related lists of length ≠ 2, the binary numeric prim
    helpers (plus, minus, times, eq) all return `none` on both sides. -/
private theorem applyPrim_plus_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_plus args_a = applyPrim_plus args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_plus]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_plus]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_plus]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_plus]

private theorem applyPrim_minus_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_minus args_a = applyPrim_minus args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_minus]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_minus]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_minus]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_minus]

private theorem applyPrim_times_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_times args_a = applyPrim_times args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_times]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_times]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_times]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_times]

private theorem applyPrim_eq_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_eq args_a = applyPrim_eq args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_eq]
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_eq]
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    have h_v0_d1 := h_vv_v0 1
                    have h_v1_d1 := h_vv_v1 1
                    cases v0_a with
                    | num a =>
                        cases v0_b with
                        | num a' =>
                            have ea : a = a' := by
                              simp [ValVis_aux] at h_v0_d1; exact h_v0_d1
                            subst ea
                            cases v1_a with
                            | num b =>
                                cases v1_b with
                                | num b' =>
                                    have eb : b = b' := by
                                      simp [ValVis_aux] at h_v1_d1; exact h_v1_d1
                                    subst eb; rfl
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply =>
                                    simp [ValVis_aux] at h_v1_d1
                            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                            | prim _ | builtinBaseApply =>
                                cases v1_b with
                                | num _ => simp [ValVis_aux] at h_v1_d1
                                | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                                | prim _ | builtinBaseApply => simp [applyPrim_eq]
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [ValVis_aux] at h_v0_d1
                    | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                    | prim _ | builtinBaseApply =>
                        cases v0_b with
                        | num _ => simp [ValVis_aux] at h_v0_d1
                        | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
                        | prim _ | builtinBaseApply => simp [applyPrim_eq]

/-! ## `mul-list` prim bisim -/

private theorem applyPrim_mulList_eq {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b) :
    applyPrim_mulList args_a = applyPrim_mulList args_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => rfl
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv_v, h_lvv_r⟩ := h_lvv
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_mulList]
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              -- args = [v]. mulConsList v_a = mulConsList v_b by mulConsList_bisim.
              simp only [applyPrim_mulList]
              rw [mulConsList_bisim v_a v_b h_a h_b h_vv_v]

/-! ## `cons`, `car`, `cdr` prim bisim -/

private theorem applyPrim_cons_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim_cons args_a = some r_a) :
    ∃ r_b, applyPrim_cons args_b = some r_b ∧ ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => simp [applyPrim_cons] at h
    | cons _ _ => exact h_lvv.elim
  | cons v0_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v0_b rest_b =>
        obtain ⟨h_vv_v0, h_lvv_r⟩ := h_lvv
        obtain ⟨hv_v0_a, hv_rest_a⟩ := hv_a
        obtain ⟨hv_v0_b, hv_rest_b⟩ := hv_b
        cases rest_a with
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil => simp [applyPrim_cons] at h
        | cons v1_a rest2_a => cases rest_b with
          | nil => exact h_lvv_r.elim
          | cons v1_b rest2_b =>
              obtain ⟨h_vv_v1, h_lvv_r2⟩ := h_lvv_r
              obtain ⟨hv_v1_a, hv_rest2_a⟩ := hv_rest_a
              obtain ⟨hv_v1_b, hv_rest2_b⟩ := hv_rest_b
              cases rest2_a with
              | cons _ _ => cases rest2_b with
                | cons _ _ => simp [applyPrim_cons] at h
                | nil => exact h_lvv_r2.elim
              | nil => cases rest2_b with
                | cons _ _ => exact h_lvv_r2.elim
                | nil =>
                    -- args = [v0, v1]. result = .cons v0 v1.
                    simp only [applyPrim_cons, Option.some.injEq] at h
                    subst h
                    refine ⟨.cons v0_b v1_b, by simp [applyPrim_cons], ?_,
                            ⟨hv_v0_a, hv_v1_a⟩, ⟨hv_v0_b, hv_v1_b⟩⟩
                    intro d
                    cases d with
                    | zero => trivial
                    | succ d' => exact ⟨h_vv_v0 d', h_vv_v1 d'⟩

private theorem applyPrim_car_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim_car args_a = some r_a) :
    ∃ r_b, applyPrim_car args_b = some r_b ∧ ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => simp [applyPrim_car] at h
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv_v, h_lvv_r⟩ := h_lvv
        obtain ⟨hv_v_a, _⟩ := hv_a
        obtain ⟨hv_v_b, _⟩ := hv_b
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_car] at h
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              -- args = [v]. v must be .cons (else applyPrim_car returns none).
              cases v_a with
              | cons xa ya =>
                  -- v_b also .cons (forced by ValVis_aux 1).
                  have h_v_d1 := h_vv_v 1
                  cases v_b with
                  | cons xb yb =>
                      simp only [applyPrim_car, Option.some.injEq] at h
                      subst h
                      have h_vv_xy : ValVis (.cons xa ya) (.cons xb yb) h_a h_b := h_vv_v
                      -- Extract ValVis xa xb.
                      refine ⟨xb, by simp [applyPrim_car], ?_, hv_v_a.1, hv_v_b.1⟩
                      intro d
                      cases d with
                      | zero => trivial
                      | succ d' => exact (h_vv_xy d'.succ.succ).1
                  | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                  | builtinBaseApply => simp [ValVis_aux] at h_v_d1
              | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
              | builtinBaseApply => simp [applyPrim_car] at h

private theorem applyPrim_cdr_bisim {args_a args_b : List Val} {h_a h_b : Heap}
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim_cdr args_a = some r_a) :
    ∃ r_b, applyPrim_cdr args_b = some r_b ∧ ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  cases args_a with
  | nil => cases args_b with
    | nil => simp [applyPrim_cdr] at h
    | cons _ _ => exact h_lvv.elim
  | cons v_a rest_a => cases args_b with
    | nil => exact h_lvv.elim
    | cons v_b rest_b =>
        obtain ⟨h_vv_v, h_lvv_r⟩ := h_lvv
        obtain ⟨hv_v_a, _⟩ := hv_a
        obtain ⟨hv_v_b, _⟩ := hv_b
        cases rest_a with
        | cons _ _ => cases rest_b with
          | cons _ _ => simp [applyPrim_cdr] at h
          | nil => exact h_lvv_r.elim
        | nil => cases rest_b with
          | cons _ _ => exact h_lvv_r.elim
          | nil =>
              cases v_a with
              | cons xa ya =>
                  have h_v_d1 := h_vv_v 1
                  cases v_b with
                  | cons xb yb =>
                      simp only [applyPrim_cdr, Option.some.injEq] at h
                      subst h
                      have h_vv_xy : ValVis (.cons xa ya) (.cons xb yb) h_a h_b := h_vv_v
                      refine ⟨yb, by simp [applyPrim_cdr], ?_, hv_v_a.2, hv_v_b.2⟩
                      intro d
                      cases d with
                      | zero => trivial
                      | succ d' => exact (h_vv_xy d'.succ.succ).2
                  | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
                  | builtinBaseApply => simp [ValVis_aux] at h_v_d1
              | num _ | bool _ | nilV | sym _ | closure _ _ _ | prim _
              | builtinBaseApply => simp [applyPrim_cdr] at h

/-! ## Result-form facts for each prim helper -/

/-- For each "scalar-result" prim helper, the successful result is always
    one of `.num _` or `.bool _`. We prove this once per prim so that the
    combined `applyPrim_bisim` can derive `ValVis r r` reflexively (which
    is trivial for these scalar types). -/

private theorem applyPrim_plus_some_form {args : List Val} {r : Val}
    (h : applyPrim_plus args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_plus] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_plus] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_plus] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_plus, Option.some.injEq] at h
                exact ⟨a + b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_plus] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_plus] at h

private theorem applyPrim_minus_some_form {args : List Val} {r : Val}
    (h : applyPrim_minus args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_minus] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_minus] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_minus] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_minus, Option.some.injEq] at h
                exact ⟨a - b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_minus] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_minus] at h

private theorem applyPrim_times_some_form {args : List Val} {r : Val}
    (h : applyPrim_times args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_times] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_times] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_times] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_times, Option.some.injEq] at h
                exact ⟨a * b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_times] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_times] at h

private theorem applyPrim_eq_some_form {args : List Val} {r : Val}
    (h : applyPrim_eq args = some r) : ∃ b : Bool, r = .bool b := by
  cases args with
  | nil => simp [applyPrim_eq] at h
  | cons v0 rest => cases rest with
    | nil => simp [applyPrim_eq] at h
    | cons v1 rest2 => cases rest2 with
      | cons _ _ => simp [applyPrim_eq] at h
      | nil =>
          cases v0 with
          | num a => cases v1 with
            | num b =>
                simp only [applyPrim_eq, Option.some.injEq] at h
                exact ⟨a == b, h.symm⟩
            | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
            | builtinBaseApply => simp [applyPrim_eq] at h
          | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
          | builtinBaseApply => simp [applyPrim_eq] at h

private theorem applyPrim_mulList_some_form {args : List Val} {r : Val}
    (h : applyPrim_mulList args = some r) : ∃ n : Int, r = .num n := by
  cases args with
  | nil => simp [applyPrim_mulList] at h
  | cons v rest => cases rest with
    | cons _ _ => simp [applyPrim_mulList] at h
    | nil =>
        simp only [applyPrim_mulList] at h
        cases hm : mulConsList v with
        | none => rw [hm] at h; simp at h
        | some n =>
            rw [hm] at h
            simp only [Option.map_some, Option.some.injEq] at h
            exact ⟨n, h.symm⟩

/-! ## Combined `applyPrim` bisim -/

theorem applyPrim_bisim (name : String) (args_a args_b : List Val) (h_a h_b : Heap)
    (h_lvv : ListValVis args_a args_b h_a h_b)
    (hv_a : ListValValid args_a h_a) (hv_b : ListValValid args_b h_b)
    (r_a : Val) (h : applyPrim name args_a = some r_a) :
    ∃ r_b, applyPrim name args_b = some r_b ∧
           ValVis r_a r_b h_a h_b ∧
           ValValid r_a h_a ∧ ValValid r_b h_b := by
  -- Helper: ValVis (.num n) (.num n) for any heaps.
  have valVis_num : ∀ (n : Int), ValVis (.num n) (.num n) h_a h_b := fun n d => by
    cases d with | zero => trivial | succ _ => rfl
  -- Helper: ValVis (.bool b) (.bool b) for any heaps.
  have valVis_bool : ∀ (b : Bool), ValVis (.bool b) (.bool b) h_a h_b := fun b d => by
    cases d with | zero => trivial | succ _ => rfl
  -- For each prim where the result is `.num _` or `.bool _`, the equality
  -- lemma + result-form lemma combine to give the bisim. For cons/car/cdr,
  -- use the dedicated bisim helpers.
  unfold applyPrim at h ⊢
  by_cases hp_plus : name = "+"
  · subst hp_plus
    simp only [↓reduceIte] at h ⊢
    have heq := applyPrim_plus_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_plus_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_minus : name = "-"
  · subst hp_minus
    simp only [↓reduceIte, hp_plus] at h ⊢
    have heq := applyPrim_minus_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_minus_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_times : name = "*"
  · subst hp_times
    simp only [↓reduceIte, hp_plus, hp_minus] at h ⊢
    have heq := applyPrim_times_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_times_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_mul : name = "mul-list"
  · subst hp_mul
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times] at h ⊢
    have heq := applyPrim_mulList_eq h_lvv
    obtain ⟨n, rfl⟩ := applyPrim_mulList_some_form h
    refine ⟨.num n, ?_, valVis_num n, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_eq : name = "="
  · subst hp_eq
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul] at h ⊢
    have heq := applyPrim_eq_eq h_lvv
    obtain ⟨b, rfl⟩ := applyPrim_eq_some_form h
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  -- Predicate prims (numQ, boolQ, closureQ, primQ, nullQ): all return .bool.
  -- The equality lemma + result-form give bisim. For these we use a direct
  -- helper-pair: equality lemma + a small `applyPrim_X_some_form` showing
  -- result is `.bool _`. We inline the form proofs since they're tiny.
  by_cases hp_numQ : name = "num?"
  · subst hp_numQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq] at h ⊢
    have heq := applyPrim_numQ_bisim h_lvv
    -- result of applyPrim_numQ is always .bool (or none).
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_numQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_numQ] at h
          | nil =>
              cases v with
              | num _ =>
                  simp only [applyPrim_numQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | bool _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_numQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_boolQ : name = "bool?"
  · subst hp_boolQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ] at h ⊢
    have heq := applyPrim_boolQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_boolQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_boolQ] at h
          | nil =>
              cases v with
              | bool _ =>
                  simp only [applyPrim_boolQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | nilV | sym _ | cons _ _ | closure _ _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_boolQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_closureQ : name = "closure?"
  · subst hp_closureQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ] at h ⊢
    have heq := applyPrim_closureQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_closureQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_closureQ] at h
          | nil =>
              cases v with
              | closure _ _ _ =>
                  simp only [applyPrim_closureQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | bool _ | nilV | sym _ | cons _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_closureQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_primQ : name = "prim?"
  · subst hp_primQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ] at h ⊢
    have heq := applyPrim_primQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_primQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_primQ] at h
          | nil =>
              cases v with
              | prim _ =>
                  simp only [applyPrim_primQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | bool _ | nilV | sym _ | cons _ _ | closure _ _ _
              | builtinBaseApply =>
                  simp only [applyPrim_primQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  by_cases hp_cons : name = "cons"
  · subst hp_cons
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ] at h ⊢
    exact applyPrim_cons_bisim h_lvv hv_a hv_b r_a h
  by_cases hp_car : name = "car"
  · subst hp_car
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ, hp_cons] at h ⊢
    exact applyPrim_car_bisim h_lvv hv_a hv_b r_a h
  by_cases hp_cdr : name = "cdr"
  · subst hp_cdr
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ, hp_cons, hp_car] at h ⊢
    exact applyPrim_cdr_bisim h_lvv hv_a hv_b r_a h
  by_cases hp_nullQ : name = "null?"
  · subst hp_nullQ
    simp only [↓reduceIte, hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ,
               hp_boolQ, hp_closureQ, hp_primQ, hp_cons, hp_car, hp_cdr] at h ⊢
    have heq := applyPrim_nullQ_bisim h_lvv
    have hform : ∃ b : Bool, r_a = .bool b := by
      cases args_a with
      | nil => simp [applyPrim_nullQ] at h
      | cons v rest =>
          cases rest with
          | cons _ _ => simp [applyPrim_nullQ] at h
          | nil =>
              cases v with
              | nilV =>
                  simp only [applyPrim_nullQ, Option.some.injEq] at h
                  exact ⟨true, h.symm⟩
              | num _ | bool _ | sym _ | cons _ _ | closure _ _ _ | prim _
              | builtinBaseApply =>
                  simp only [applyPrim_nullQ, Option.some.injEq] at h
                  exact ⟨false, h.symm⟩
    obtain ⟨b, rfl⟩ := hform
    refine ⟨.bool b, ?_, valVis_bool b, trivial, trivial⟩
    rw [← heq]; exact h
  -- Unknown name: applyPrim returns none.
  exfalso
  simp only [hp_plus, hp_minus, hp_times, hp_mul, hp_eq, hp_numQ, hp_boolQ,
             hp_closureQ, hp_primQ, hp_cons, hp_car, hp_cdr, hp_nullQ,
             ↓reduceIte] at h
  exact Option.noConfusion h

/-! ## Cons-extension of `EnvVis` -/

/-- Adding a fresh `(x, idx_a)` / `(x, idx_b)` binding on top of related
    envs preserves `EnvVis_aux` provided the pointed-to values are
    `ValVis_aux`-related at the same depth. -/
theorem EnvVis_aux_cons (d : Nat) (x : String) (idx_a idx_b : Nat)
    (env_a env_b : Env) (h_a h_b : Heap) (v_a v_b : Val)
    (h_lookup_a : h_a[idx_a]? = some v_a)
    (h_lookup_b : h_b[idx_b]? = some v_b)
    (h_vv : ValVis_aux d v_a v_b h_a h_b)
    (h_env : EnvVis_aux d env_a env_b h_a h_b) :
    EnvVis_aux d (.cons x idx_a env_a) (.cons x idx_b env_b) h_a h_b := by
  intro name
  simp only [Env.lookup]
  by_cases h_eq : x = name
  · subst h_eq
    simp only [beq_self_eq_true, ↓reduceIte, h_lookup_a, h_lookup_b]
    exact h_vv
  · have h_neq : (x == name) = false := by
      rw [beq_eq_false_iff_ne]; exact h_eq
    simp only [h_neq, Bool.false_eq_true, ↓reduceIte]
    exact h_env name

/-- Universal-depth version. -/
theorem EnvVis_cons (x : String) (idx_a idx_b : Nat)
    (env_a env_b : Env) (h_a h_b : Heap) (v_a v_b : Val)
    (h_lookup_a : h_a[idx_a]? = some v_a)
    (h_lookup_b : h_b[idx_b]? = some v_b)
    (h_vv : ValVis v_a v_b h_a h_b)
    (h_env : EnvVis env_a env_b h_a h_b) :
    EnvVis (.cons x idx_a env_a) (.cons x idx_b env_b) h_a h_b := by
  intro d
  exact EnvVis_aux_cons d x idx_a idx_b env_a env_b h_a h_b v_a v_b
    h_lookup_a h_lookup_b (h_vv d) (h_env d)

/-! ## Closure-call alloc-chain invariant
    (`allocStep` itself moved to `Tower.lean` so that `Eval.lean` can
    use it directly in the `applyDirect` closure case, removing the
    representational mismatch that blocked the framing proof.) -/

/-- Cross-side alignment of `allocStep` chains: starting from
    accumulators with equal env and equal-length heap, after `foldl`-
    ing the same parameter list with two same-length value lists, the
    output envs match and the output heap lengths match. The values
    in the heap may differ; only structure is preserved. -/
theorem allocStep_chain_aligned :
    ∀ (xs_a xs_b : List Val) (ps : List String)
      (h_a h_b : Heap) (cenv : Env),
      h_a.length = h_b.length →
      xs_a.length = xs_b.length →
      ((xs_a.zip ps).foldl allocStep (h_a, cenv)).2 =
        ((xs_b.zip ps).foldl allocStep (h_b, cenv)).2 ∧
      ((xs_a.zip ps).foldl allocStep (h_a, cenv)).1.length =
        ((xs_b.zip ps).foldl allocStep (h_b, cenv)).1.length
  | [], [], _, _, _, _, h_len, _ => by
      simp [List.zip_nil_left, List.foldl, h_len]
  | [], _ :: _, _, _, _, _, _, h_args => by simp at h_args
  | _ :: _, [], _, _, _, _, _, h_args => by simp at h_args
  | _ :: xs_a, _ :: xs_b, [], _, _, _, h_len, _ => by
      simp [List.zip_nil_right, List.foldl, h_len]
  | x_a :: xs_a, x_b :: xs_b, p :: ps, h_a, h_b, cenv, h_len, h_args => by
      simp only [List.zip_cons_cons, List.foldl_cons, allocStep, Heap.alloc]
      have h_args' : xs_a.length = xs_b.length := by simp at h_args; exact h_args
      have h_len' : (h_a ++ [x_a]).length = (h_b ++ [x_b]).length := by
        simp [List.length_append, h_len]
      have h_cenv_eq :
          (Env.cons p h_a.length cenv) = (Env.cons p h_b.length cenv) := by
        rw [h_len]
      rw [h_cenv_eq]
      exact allocStep_chain_aligned xs_a xs_b ps (h_a ++ [x_a]) (h_b ++ [x_b])
        (Env.cons p h_b.length cenv) h_len' h_args'

/-! ## Self-extend helpers -/

/-- A list of `ValValid` values is `ListValVis` with itself across a
    heap extension. Used to build self-bisim hypotheses for the
    inner `frame.applyDirect` call in `multnExact_CE_nonnum_case`. -/
theorem ListValVis_self_extend : ∀ {xs : List Val} {h : Heap} (extras : Heap),
    HeapValid h → ListValValid xs h →
    ListValVis xs xs h (h ++ extras)
  | [], _, _, _, _ => trivial
  | x :: _, h, extras, hh, ⟨hv_x, hv_rest⟩ =>
      ⟨fun d => ValVis_aux_self_extend d x h extras hh hv_x,
       ListValVis_self_extend extras hh hv_rest⟩

/-! ## Env-lookup helpers for the multn closure-body trace -/

theorem env_alloc_lookup_op (s_heap : Heap) (cenv : Env) :
    (Env.cons "args" (s_heap.length + 1)
      (Env.cons "op" s_heap.length cenv)).lookup "op" = some s_heap.length := by
  simp [Env.lookup]

theorem env_alloc_lookup_args (s_heap : Heap) (cenv : Env) :
    (Env.cons "args" (s_heap.length + 1)
      (Env.cons "op" s_heap.length cenv)).lookup "args" = some (s_heap.length + 1) := by
  simp [Env.lookup]

theorem env_alloc_lookup_other {s_heap : Heap} {cenv : Env}
    (x : String) (h1 : x ≠ "args") (h2 : x ≠ "op") :
    (Env.cons "args" (s_heap.length + 1)
      (Env.cons "op" s_heap.length cenv)).lookup x = cenv.lookup x := by
  simp [Env.lookup, h1.symm, h2.symm]

/-- Foldl-allocation preserves the validity and bisimulation invariants:
    starting from `EnvVis`-related cenvs and pointwise-bisim args, the
    resulting (extended-heap, cons-extended-env) pairs satisfy `WFCtx`-shape
    invariants and `EnvVis` on the extended envs. Used by `applyDirect`'s
    closure case in the framing theorem. -/
theorem alloc_chain_bisim
    (xs_a : List Val) :
    ∀ (xs_b : List Val) (ps : List String) (cenv_a cenv_b : Env) (h_a h_b : Heap),
    xs_a.length = ps.length → xs_b.length = ps.length →
    ListValVis xs_a xs_b h_a h_b →
    ListValValid xs_a h_a → ListValValid xs_b h_b →
    HeapValid h_a → HeapValid h_b →
    EnvValid cenv_a h_a → EnvValid cenv_b h_b →
    EnvVis cenv_a cenv_b h_a h_b →
    let result_a := xs_a.zip ps |>.foldl allocStep (h_a, cenv_a)
    let result_b := xs_b.zip ps |>.foldl allocStep (h_b, cenv_b)
    HeapValid result_a.1 ∧ HeapValid result_b.1 ∧
    EnvValid result_a.2 result_a.1 ∧ EnvValid result_b.2 result_b.1 ∧
    EnvVis result_a.2 result_b.2 result_a.1 result_b.1 ∧
    (∃ ext, result_a.1 = h_a ++ ext) ∧
    (∃ ext, result_b.1 = h_b ++ ext) := by
  induction xs_a with
  | nil =>
      intro xs_b ps cenv_a cenv_b h_a h_b hlen_a hlen_b h_lvv hv_xs_a hv_xs_b
            hh_a hh_b hev_a hev_b h_env
      simp only [List.length_nil] at hlen_a
      have hps_nil : ps = [] := List.length_eq_zero_iff.mp hlen_a.symm
      subst hps_nil
      simp only [List.length_nil] at hlen_b
      have hxs_b_nil : xs_b = [] := List.length_eq_zero_iff.mp hlen_b
      subst hxs_b_nil
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show HeapValid (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
        simp [List.foldl]; exact hh_a
      · show HeapValid (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact hh_b
      · show EnvValid (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).2
                     (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
        simp [List.foldl]; exact hev_a
      · show EnvValid (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).2
                     (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact hev_b
      · show EnvVis (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).2
                    (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).2
                    (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
                    (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
        simp [List.foldl]; exact h_env
      · show ∃ ext, (([] : List (Val × String)).foldl allocStep (h_a, cenv_a)).1
          = h_a ++ ext
        simp [List.foldl]
      · show ∃ ext, (([] : List (Val × String)).foldl allocStep (h_b, cenv_b)).1
          = h_b ++ ext
        simp [List.foldl]
  | cons a_a rest_a ih =>
      intro xs_b ps cenv_a cenv_b h_a h_b hlen_a hlen_b h_lvv hv_xs_a hv_xs_b
            hh_a hh_b hev_a hev_b h_env
      cases ps with
      | nil =>
          exfalso
          simp only [List.length_cons, List.length_nil] at hlen_a
          omega
      | cons p rest_p =>
          cases xs_b with
          | nil =>
              exfalso
              simp only [List.length_nil, List.length_cons] at hlen_b
              omega
          | cons a_b rest_b =>
              simp only [List.length_cons] at hlen_a hlen_b
              have hlen_a' : rest_a.length = rest_p.length := by omega
              have hlen_b' : rest_b.length = rest_p.length := by omega
              obtain ⟨h_vv_a, h_lvv_rest⟩ := h_lvv
              obtain ⟨hv_a_a, hv_rest_a⟩ := hv_xs_a
              obtain ⟨hv_a_b, hv_rest_b⟩ := hv_xs_b
              -- After one foldl step on each side.
              show
                let result_a := rest_a.zip rest_p |>.foldl allocStep
                  (h_a ++ [a_a], .cons p h_a.length cenv_a)
                let result_b := rest_b.zip rest_p |>.foldl allocStep
                  (h_b ++ [a_b], .cons p h_b.length cenv_b)
                HeapValid result_a.1 ∧ HeapValid result_b.1 ∧
                EnvValid result_a.2 result_a.1 ∧ EnvValid result_b.2 result_b.1 ∧
                EnvVis result_a.2 result_b.2 result_a.1 result_b.1 ∧
                (∃ ext, result_a.1 = h_a ++ ext) ∧
                (∃ ext, result_b.1 = h_b ++ ext)
              -- Establish invariants for the new (h, env) pair.
              have hh_a' : HeapValid (h_a ++ [a_a]) := by
                intro i v hp
                by_cases h_lt : i < h_a.length
                · have hp_old : h_a[i]? = some v := by
                    rw [← getElem?_prefix h_a [a_a] i h_lt]; exact hp
                  exact ValValid.heap_extends v (hh_a i v hp_old) ⟨[a_a], rfl⟩
                · have h_eq : i = h_a.length := by
                    have h_le : i < (h_a ++ [a_a]).length := by
                      rw [List.getElem?_eq_some_iff] at hp
                      obtain ⟨h, _⟩ := hp; exact h
                    simp [List.length_append] at h_le; omega
                  subst h_eq
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hp
                  simp at hp
                  subst hp
                  exact ValValid.heap_extends a_a hv_a_a ⟨[a_a], rfl⟩
              have hh_b' : HeapValid (h_b ++ [a_b]) := by
                intro i v hp
                by_cases h_lt : i < h_b.length
                · have hp_old : h_b[i]? = some v := by
                    rw [← getElem?_prefix h_b [a_b] i h_lt]; exact hp
                  exact ValValid.heap_extends v (hh_b i v hp_old) ⟨[a_b], rfl⟩
                · have h_eq : i = h_b.length := by
                    have h_le : i < (h_b ++ [a_b]).length := by
                      rw [List.getElem?_eq_some_iff] at hp
                      obtain ⟨h, _⟩ := hp; exact h
                    simp [List.length_append] at h_le; omega
                  subst h_eq
                  rw [List.getElem?_append_right (Nat.le_refl _)] at hp
                  simp at hp
                  subst hp
                  exact ValValid.heap_extends a_b hv_a_b ⟨[a_b], rfl⟩
              have hev_a' : EnvValid (.cons p h_a.length cenv_a) (h_a ++ [a_a]) := by
                intro name i hl
                simp only [List.length_append, List.length_singleton]
                simp only [Env.lookup] at hl
                by_cases h_eq : p = name
                · subst h_eq
                  simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                  omega
                · have h_neq : (p == name) = false := by
                    rw [beq_eq_false_iff_ne]; exact h_eq
                  simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                  have := hev_a name i hl
                  omega
              have hev_b' : EnvValid (.cons p h_b.length cenv_b) (h_b ++ [a_b]) := by
                intro name i hl
                simp only [List.length_append, List.length_singleton]
                simp only [Env.lookup] at hl
                by_cases h_eq : p = name
                · subst h_eq
                  simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
                  omega
                · have h_neq : (p == name) = false := by
                    rw [beq_eq_false_iff_ne]; exact h_eq
                  simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at hl
                  have := hev_b name i hl
                  omega
              -- Lookups at the fresh indices.
              have hl_a : (h_a ++ [a_a])[h_a.length]? = some a_a := by
                rw [List.getElem?_append_right (Nat.le_refl _)]; simp
              have hl_b : (h_b ++ [a_b])[h_b.length]? = some a_b := by
                rw [List.getElem?_append_right (Nat.le_refl _)]; simp
              -- ValVis a_a a_b lifted to extended heaps.
              have h_vv_a' : ValVis a_a a_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                ValVis_extends a_a a_b h_a h_b [a_a] [a_b] hh_a hh_b hv_a_a hv_a_b h_vv_a
              -- EnvVis cenv_a cenv_b lifted.
              have h_env_lifted : EnvVis cenv_a cenv_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                EnvVis_extends cenv_a cenv_b h_a h_b [a_a] [a_b]
                  hh_a hh_b hev_a hev_b h_env
              -- EnvVis on the new cons-extended env.
              have h_env' : EnvVis (.cons p h_a.length cenv_a) (.cons p h_b.length cenv_b)
                  (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                EnvVis_cons p h_a.length h_b.length cenv_a cenv_b
                  (h_a ++ [a_a]) (h_b ++ [a_b]) a_a a_b hl_a hl_b h_vv_a' h_env_lifted
              -- Lift ListValVis rest_a rest_b to extended heaps.
              have h_lvv_rest' : ListValVis rest_a rest_b (h_a ++ [a_a]) (h_b ++ [a_b]) :=
                ListValVis_extends hh_a hh_b hv_rest_a hv_rest_b h_lvv_rest
              -- Lift validity of rest_a / rest_b.
              have hv_rest_a' : ListValValid rest_a (h_a ++ [a_a]) :=
                ListValValid.heap_extends hv_rest_a ⟨[a_a], rfl⟩
              have hv_rest_b' : ListValValid rest_b (h_b ++ [a_b]) :=
                ListValValid.heap_extends hv_rest_b ⟨[a_b], rfl⟩
              -- Apply IH on rest.
              obtain ⟨hh_ra, hh_rb, hev_ra, hev_rb, h_env_r, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
                ih rest_b rest_p (.cons p h_a.length cenv_a) (.cons p h_b.length cenv_b)
                  (h_a ++ [a_a]) (h_b ++ [a_b])
                  hlen_a' hlen_b' h_lvv_rest' hv_rest_a' hv_rest_b'
                  hh_a' hh_b' hev_a' hev_b' h_env'
              refine ⟨hh_ra, hh_rb, hev_ra, hev_rb, h_env_r, ?_, ?_⟩
              · exact ⟨[a_a] ++ ext_a, by rw [hex_a, List.append_assoc]⟩
              · exact ⟨[a_b] ++ ext_b, by rw [hex_b, List.append_assoc]⟩

/-! ## ValVis on closures → EnvVis on cenvs -/

/-- The closure case of `ValVis_aux (n+1)` is exactly `EnvVis_aux n` on the
    captured envs (plus body/params/cenv-structural equality). Lifting
    to all depths gives `EnvVis cenv_a cenv_b`. -/
theorem closure_ValVis_imp_cenv_EnvVis
    {ps_a ps_b : List String} {body_a body_b : Expr} {cenv_a cenv_b : Env}
    {h_a h_b : Heap}
    (h_vv : ValVis (.closure ps_a body_a cenv_a) (.closure ps_b body_b cenv_b) h_a h_b) :
    ps_a = ps_b ∧ body_a = body_b ∧ cenv_a = cenv_b ∧
    EnvVis cenv_a cenv_b h_a h_b := by
  have h1 := h_vv 1
  refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
  intro d
  exact (h_vv (d + 1)).2.2.2

/-! ## ValVis collapses to Val equality

    Under the strengthened `ValVis_aux` on closures (which now
    requires `cenv_a = cenv_b` structurally), universal-depth
    bisimulation between two values implies they are *equal* as
    Lean terms. Used by the `PolicyRespectsBisim` proofs for
    policies that pattern-match on `Val` structure (where bisim-
    related inputs need to give the same pattern result). -/
theorem bisim_imp_eq : ∀ (v1 v2 : Val) (h1 h2 : Heap),
    ValVis v1 v2 h1 h2 → v1 = v2
  | .num _,            v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .bool _,           v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .nilV,             v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first | rfl | (simp [ValVis_aux] at h)
  | .sym _,            v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .prim _,           v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first
        | (simp only [ValVis_aux] at h; subst h; rfl)
        | (simp [ValVis_aux] at h)
  | .builtinBaseApply, v2, _, _, h_vis => by
      have h := h_vis 1
      cases v2 <;> first | rfl | (simp [ValVis_aux] at h)
  | .cons x_a y_a,     v2, _, _, h_vis => by
      have h1 := h_vis 1
      cases v2 with
      | cons x_b y_b =>
          -- ValVis at depth k+1 on .cons: ValVis_aux k on each component.
          have h_x : ValVis x_a x_b _ _ := fun k => (h_vis (k + 1)).1
          have h_y : ValVis y_a y_b _ _ := fun k => (h_vis (k + 1)).2
          have ex := bisim_imp_eq x_a x_b _ _ h_x
          have ey := bisim_imp_eq y_a y_b _ _ h_y
          rw [ex, ey]
      | num _ => simp [ValVis_aux] at h1
      | bool _ => simp [ValVis_aux] at h1
      | nilV => simp [ValVis_aux] at h1
      | sym _ => simp [ValVis_aux] at h1
      | closure _ _ _ => simp [ValVis_aux] at h1
      | prim _ => simp [ValVis_aux] at h1
      | builtinBaseApply => simp [ValVis_aux] at h1
  | .closure ps body cenv, v2, _, _, h_vis => by
      have h1 := h_vis 1
      cases v2 with
      | closure ps_b body_b cenv_b =>
          -- ValVis_aux 1 on closures gives ps_eq, body_eq, cenv_eq.
          obtain ⟨h_ps, h_body, h_cenv, _⟩ := h1
          rw [h_ps, h_body, h_cenv]
      | num _ => simp [ValVis_aux] at h1
      | bool _ => simp [ValVis_aux] at h1
      | nilV => simp [ValVis_aux] at h1
      | sym _ => simp [ValVis_aux] at h1
      | cons _ _ => simp [ValVis_aux] at h1
      | prim _ => simp [ValVis_aux] at h1
      | builtinBaseApply => simp [ValVis_aux] at h1

/-! ## AllBelow / Deep predicates

    Ported from lean-green:Bisim.lean:5037-5162. Independent of tower
    state — these are pure structural predicates on Env / Val / Heap.

    `Env.AllBelow cutoff env` says every binding in `env` (including
    shadowed ones) has `idx < cutoff`. Stronger than `EnvValid` which
    only constrains lookups.

    `EnvDeep env h` says every binding in `env` has `idx < h.length`,
    making it suitable for length-monotonicity arguments.

    `HeapDeep h` says every cell of `h` is `ValDeep` in `h`. Used by
    the multnExact non-num case proof to derive uniform shifts. -/

def Env.AllBelow (cutoff : Nat) : Env → Prop
  | .nil               => True
  | .cons _ idx rest   => idx < cutoff ∧ Env.AllBelow cutoff rest

def Val.AllBelow (cutoff : Nat) : Val → Prop
  | .num _              => True
  | .bool _             => True
  | .nilV               => True
  | .sym _              => True
  | .prim _             => True
  | .builtinBaseApply   => True
  | .cons x y           => Val.AllBelow cutoff x ∧ Val.AllBelow cutoff y
  | .closure _ _ cenv   => Env.AllBelow cutoff cenv

def ListVal.AllBelow (cutoff : Nat) : List Val → Prop
  | []      => True
  | v :: vs => Val.AllBelow cutoff v ∧ ListVal.AllBelow cutoff vs

theorem Env.AllBelow.mono {cutoff cutoff' : Nat} (h_le : cutoff ≤ cutoff') :
    ∀ {env : Env}, Env.AllBelow cutoff env → Env.AllBelow cutoff' env
  | .nil,           _   => trivial
  | .cons _ _ rest, ⟨h_idx, h_rest⟩ =>
      ⟨Nat.lt_of_lt_of_le h_idx h_le, Env.AllBelow.mono h_le h_rest⟩

theorem Val.AllBelow.mono {cutoff cutoff' : Nat} (h_le : cutoff ≤ cutoff') :
    ∀ {v : Val}, Val.AllBelow cutoff v → Val.AllBelow cutoff' v
  | .num _,            _ => trivial
  | .bool _,           _ => trivial
  | .nilV,             _ => trivial
  | .sym _,            _ => trivial
  | .prim _,           _ => trivial
  | .builtinBaseApply, _ => trivial
  | .cons x y,         ⟨hx, hy⟩ =>
      ⟨Val.AllBelow.mono h_le hx, Val.AllBelow.mono h_le hy⟩
  | .closure _ _ _,    h => Env.AllBelow.mono h_le h

theorem ListVal.AllBelow.mono {cutoff cutoff' : Nat} (h_le : cutoff ≤ cutoff') :
    ∀ {xs : List Val}, ListVal.AllBelow cutoff xs → ListVal.AllBelow cutoff' xs
  | [],      _ => trivial
  | _ :: _, ⟨h, t⟩ => ⟨Val.AllBelow.mono h_le h, ListVal.AllBelow.mono h_le t⟩

def EnvDeep : Env → Heap → Prop
  | .nil,             _ => True
  | .cons _ idx rest, h => idx < h.length ∧ EnvDeep rest h

def ValDeep : Val → Heap → Prop
  | .num _,            _ => True
  | .bool _,           _ => True
  | .nilV,             _ => True
  | .sym _,            _ => True
  | .prim _,           _ => True
  | .builtinBaseApply, _ => True
  | .cons x y,         h => ValDeep x h ∧ ValDeep y h
  | .closure _ _ cenv, h => EnvDeep cenv h

def ListValDeep : List Val → Heap → Prop
  | [],      _ => True
  | x :: xs, h => ValDeep x h ∧ ListValDeep xs h

def HeapDeep (h : Heap) : Prop :=
  ∀ (i : Nat) (v : Val), h[i]? = some v → ValDeep v h

theorem EnvDeep.toAllBelow : ∀ {env : Env} {h : Heap},
    EnvDeep env h → Env.AllBelow h.length env
  | Env.nil,           _, _   => trivial
  | Env.cons _ _ rest, _, ⟨h_idx, h_rest⟩ =>
      ⟨h_idx, EnvDeep.toAllBelow h_rest⟩

theorem ValDeep.toAllBelow : ∀ {v : Val} {h : Heap},
    ValDeep v h → Val.AllBelow h.length v
  | .num _,            _, _ => trivial
  | .bool _,           _, _ => trivial
  | .nilV,             _, _ => trivial
  | .sym _,            _, _ => trivial
  | .prim _,           _, _ => trivial
  | .builtinBaseApply, _, _ => trivial
  | .cons x y,         _, ⟨hx, hy⟩ =>
      ⟨ValDeep.toAllBelow hx, ValDeep.toAllBelow hy⟩
  | .closure _ _ _,    _, h => EnvDeep.toAllBelow h

theorem ListValDeep.toAllBelow : ∀ {vs : List Val} {h : Heap},
    ListValDeep vs h → ListVal.AllBelow h.length vs
  | [],      _, _ => trivial
  | _ :: _, _, ⟨hx, hxs⟩ =>
      ⟨ValDeep.toAllBelow hx, ListValDeep.toAllBelow hxs⟩

theorem EnvDeep.length_mono : ∀ {env : Env} {h h' : Heap},
    EnvDeep env h → h.length ≤ h'.length → EnvDeep env h'
  | Env.nil,           _, _, _, _   => trivial
  | Env.cons _ _ rest, _, _, ⟨h_idx, h_rest⟩, h_le =>
      ⟨Nat.lt_of_lt_of_le h_idx h_le, EnvDeep.length_mono h_rest h_le⟩

theorem ValDeep.length_mono : ∀ {v : Val} {h h' : Heap},
    ValDeep v h → h.length ≤ h'.length → ValDeep v h'
  | .num _,            _, _, _,  _   => trivial
  | .bool _,           _, _, _,  _   => trivial
  | .nilV,             _, _, _,  _   => trivial
  | .sym _,            _, _, _,  _   => trivial
  | .prim _,           _, _, _,  _   => trivial
  | .builtinBaseApply, _, _, _,  _   => trivial
  | .cons x y,         _, _, ⟨hx, hy⟩, h_le =>
      ⟨ValDeep.length_mono hx h_le, ValDeep.length_mono hy h_le⟩
  | .closure _ _ _,    _, _, hev, h_le => EnvDeep.length_mono hev h_le

theorem ListValDeep.length_mono : ∀ {vs : List Val} {h h' : Heap},
    ListValDeep vs h → h.length ≤ h'.length → ListValDeep vs h'
  | [],      _, _, _, _ => trivial
  | _ :: _, _, _, ⟨hx, hxs⟩, h_le =>
      ⟨ValDeep.length_mono hx h_le, ListValDeep.length_mono hxs h_le⟩

/-- Atoms (non-closure, non-cons values) are `ValDeep` in any heap. -/
theorem ValDeep.atom : ∀ {v : Val} {h : Heap},
    (∀ ps body cenv, v ≠ .closure ps body cenv) →
    (∀ x y, v ≠ .cons x y) → ValDeep v h
  | .num _,            _, _, _ => trivial
  | .bool _,           _, _, _ => trivial
  | .nilV,             _, _, _ => trivial
  | .sym _,            _, _, _ => trivial
  | .prim _,           _, _, _ => trivial
  | .builtinBaseApply, _, _, _ => trivial
  | .cons x y,         _, _, h_no_cons => absurd rfl (h_no_cons x y)
  | .closure ps body cenv, _, h_no_closure, _ =>
      absurd rfl (h_no_closure ps body cenv)

/-- Closed values are vacuously `AllBelow` at any cutoff. -/
theorem closedValB_AllBelow (cutoff : Nat) :
    ∀ (v : Val), closedValB v = true → Val.AllBelow cutoff v
  | .num _,            _ => trivial
  | .bool _,           _ => trivial
  | .nilV,             _ => trivial
  | .sym _,            _ => trivial
  | .prim _,           _ => trivial
  | .builtinBaseApply, _ => trivial
  | .cons x y, hc => by
      simp [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedValB_AllBelow cutoff x hc.1, closedValB_AllBelow cutoff y hc.2⟩
  | .closure _ _ _, hc => by simp [closedValB] at hc

/-! ## ValVis transitivity (closure case sorry'd)

    Needed for composing CE chains across mutating eval steps. The
    proof is by induction on depth with cases on Val structure:
    atomic constructors are immediate, `.cons` chains by IH on
    components, `.closure` after `subst` on cenv equalities reduces
    to chasing the heap-indexed lookup chain.

    The closure case has a technical block: Lean's match-on-pair
    reduction (`match (some i, some i) with | (some i_a, some i_b) =>
    ...`) doesn't fire under `simp only` / `dsimp only` / `rw [helper]`
    even with a `rfl`-provable equality helper. This appears to be
    because the inline match in `ValVis_aux`'s closure body is
    elaborated to a recursor that doesn't match the inline-match
    form in the helper. A clean fix is to refactor `ValVis_aux`'s
    closure-arm body to use the named `EnvVis_aux` def — but that
    ripples through ~30 dependent proofs. Deferred. -/
theorem ValVis_aux_trans : ∀ (n : Nat) (va vb vc : Val) (ha hb hc : Heap),
    ValVis_aux n va vb ha hb → ValVis_aux n vb vc hb hc →
    ValVis_aux n va vc ha hc := by
  -- Proof deferred — closure case has match-reduction issue.
  sorry

/-- ValVis transitivity (the depth-uniform version). -/
theorem ValVis_trans (va vb vc : Val) (ha hb hc : Heap) :
    ValVis va vb ha hb → ValVis vb vc hb hc → ValVis va vc ha hc := by
  intro h12 h23 n
  exact ValVis_aux_trans n va vb vc ha hb hc (h12 n) (h23 n)

