import Std
import Verified.VAE.Syntax
import Verified.VAE.SmallStep

namespace VAE

-- Soundness of SmallStep VAE
-- Every well-formed configuration evaluates to a value in finite steps.

-- helper: collect free variables in an expression
def Expr.fvs : Expr -> Std.HashSet String
  | num _ => {}
  | add e1 e2 => e1.fvs ∪ e2.fvs
  | mul e1 e2 => e1.fvs ∪ e2.fvs
  | val x e1 e2 => e1.fvs ∪ (e2.fvs.erase x)
  | id x => {x}

-- Well-Formed Configuration: fvs(e) ⊆ dom(σ)
def WF (config : Env × Expr) : Prop :=
  ∀ x ∈ config.snd.fvs, x ∈ config.fst

-- helper: check if an expression is a value
inductive Expr.isValue : Expr -> Prop where
  | num : Expr.isValue (.num n)

-- helper: WF Decomposition Theorems
-- fvs(e1) ⊆ fvs(e1 + e2) ⊆ dom(σ) -> fvs(e1) ⊆ dom(σ)
theorem WF.of_add_left (h : WF (env, .add e1 e2)) : WF (env, e1) :=
  fun x hx => h x (Std.HashSet.mem_union_iff.mpr (Or.inl hx))
-- fvs(e2) ⊆ fvs(e1 + e2) ⊆ dom(σ) -> fvs(e2) ⊆ dom(σ)
theorem WF.of_add_right (h : WF (env, .add e1 e2)) : WF (env, e2) :=
  fun x hx => h x (Std.HashSet.mem_union_iff.mpr (Or.inr hx))
-- fvs(e1) ⊆ fvs(e1 * e2) ⊆ dom(σ) -> fvs(e1) ⊆ dom(σ)
theorem WF.of_mul_left (h : WF (env, .mul e1 e2)) : WF (env, e1) :=
  fun x hx => h x (Std.HashSet.mem_union_iff.mpr (Or.inl hx))
-- fvs(e2) ⊆ fvs(e1 * e2) ⊆ dom(σ) -> fvs(e2) ⊆ dom(σ)
theorem WF.of_mul_right (h : WF (env, .mul e1 e2)) : WF (env, e2) :=
  fun x hx => h x (Std.HashSet.mem_union_iff.mpr (Or.inr hx))
-- fvs(e1) ⊆ fvs({x := e1; e2}) ⊆ dom(σ) -> fvs(e1) ⊆ dom(σ)
theorem WF.of_val_init (h : WF (env, .val x e1 e2)) : WF (env, e1) :=
  fun y hy => h y (Std.HashSet.mem_union_iff.mpr (Or.inl hy))
-- (fvs(e2) \ {x}) ⊆ fvs({x := e1; e2}) ⊆ dom(σ) -> (fvs(e2) \ {x}) ⊆ dom(σ)
theorem WF.of_val_filter (h : WF (env, .val x e1 e2)) :
    ∀ y, y ∈ e2.fvs.erase x -> y ∈ env :=
  fun y hy => h y (Std.HashSet.mem_union_iff.mpr (Or.inr hy))
-- (fvs(e2) \ {x}) ⊆ dom(σ) -> fvs(e2) ⊆ dom(σ[x -> n])
theorem WF.of_val_body (h : WF (env, .val x e1 e2)) (n : Int) :
    WF (env.insert x n, e2) :=
  fun y hy => by
    by_cases heq : x == y
    · exact Std.HashMap.mem_insert.mpr (Or.inl heq)
    · exact Std.HashMap.mem_insert.mpr (Or.inr
        (WF.of_val_filter h y (Std.HashSet.mem_erase.mpr ⟨Bool.eq_false_iff.mpr heq, hy⟩)))

-- helper: WF Composition Theorem
-- fvs(n) = ∅ ⊆ dom(σ)
theorem WF.num : WF (env, .num n) :=
  fun _ h => absurd h (by simp [Expr.fvs])
-- fvs(e1) ⊆ dom(σ) /\ fvs(e2) ⊆ dom(σ) -> fvs(e1 + e2) ⊆ dom(σ)
theorem WF.add (h1 : WF (env, e1)) (h2 : WF (env, e2)) : WF (env, .add e1 e2) :=
  fun x hx => (Std.HashSet.mem_union_iff.mp hx).elim (h1 x) (h2 x)
-- fvs(e1) ⊆ dom(σ) /\ fvs(e2) ⊆ dom(σ) -> fvs(e1 * e2) ⊆ dom(σ)
theorem WF.mul (h1 : WF (env, e1)) (h2 : WF (env, e2)) : WF (env, .mul e1 e2) :=
  fun x hx => (Std.HashSet.mem_union_iff.mp hx).elim (h1 x) (h2 x)
-- fvs(e1) ⊆ dom(σ) /\ (fvs(e2) \ {x}) ⊆ dom(σ) -> fvs({x := e1; e2}) ⊆ dom(σ)
theorem WF.mkVal (h1 : WF (env, e1))
    (h2 : ∀ y, y ∈ e2.fvs.erase x -> y ∈ env) : WF (env, .val x e1 e2) :=
  fun y hy => (Std.HashSet.mem_union_iff.mp hy).elim (h1 y) (h2 y)

-- helper: WF Monotonicity Theorem
-- dom(σ) ⊆ dom(σ') -> WF(σ, e) -> WF(σ', e)
theorem WF.mono (hwf : WF (env, e)) (hext : ∀ x, x ∈ env -> x ∈ env') :
    WF (env', e) :=
  fun x hx => hext x (hwf x hx)

-- Progress
theorem Step.progress (hwf : WF (env, e)) :
    e.isValue ∨ ∃ env' e', Step (env, e) (env', e')
  := by
  induction e with
  | num n => exact Or.inl .num -- e is a value
  | id x =>
    right
    -- As e is WF, x ∈ dom(σ)
    have hx : x ∈ env := by apply hwf; simp [Expr.fvs]
    -- σ(x) = n for some n
    let n := env.get x hx
    -- e steps to n
    exact ⟨_, .num n, Step.id hx⟩
  | add e1 e2 ih1 ih2 =>
      right
      match ih1 hwf.of_add_left, ih2 hwf.of_add_right with
      -- e1 steps
      | Or.inr ⟨env', e1', h⟩, _ => exact ⟨_, _, Step.add_left h⟩
      -- e1 is a value, e2 steps
      | Or.inl .num, Or.inr ⟨env', e2', h⟩ => exact ⟨_, _, Step.add_right h⟩
      -- e1 and e2 both are values
      | Or.inl .num, Or.inl .num => exact ⟨_, _, Step.add_val⟩
  | mul e1 e2 ih1 ih2 =>
    right
    match ih1 hwf.of_mul_left, ih2 hwf.of_mul_right with
    -- e1 steps
    | Or.inr ⟨env', e1', h⟩, _ => exact ⟨_, _, Step.mul_left h⟩
    -- e1 is a value, e2 steps
    | Or.inl .num, Or.inr ⟨env', e2', h⟩ => exact ⟨_, _, Step.mul_right h⟩
    -- e1 and e2 both are values
    | Or.inl .num, Or.inl .num => exact ⟨_, _, Step.mul_val⟩
  | val x e1 e2 ih1 _ =>
    right
    match ih1 hwf.of_val_init with
    -- e1 steps
    | Or.inr ⟨env', e1', h⟩ => exact ⟨_, _, Step.val_step h⟩
    -- e1 is a value
    | Or.inl .num => exact ⟨_, _, Step.val_bind⟩

-- small-step evaluation rules only add new bindings to environments
theorem Step.env_extends (h : Step config config') :
    ∀ x, x ∈ config.fst -> x ∈ config'.fst
  := by
  induction h with
  | add_left _ ih => intro x hx; exact ih x hx
  | add_right _ ih => intro x hx; exact ih x hx
  | add_val => intro x hx; exact hx
  | mul_left _ ih => intro x hx; exact ih x hx
  | mul_right _ ih => intro x hx; exact ih x hx
  | mul_val => intro x hx; exact hx
  | id _ => intro x hx; exact hx
  | val_step _ ih => intro x hx; exact ih x hx
  | val_bind => intro x hx; exact Std.HashMap.mem_insert.mpr (Or.inr hx)

-- Preservation
theorem Step.preservation (hwf : WF config)
    (h : Step config config') : WF config'
  := by
  revert hwf
  induction h with
  | add_val | mul_val | id _ =>
    intro hwf; exact WF.num
  | @val_bind σ x n e2 =>
    intro hwf; exact WF.of_val_body hwf n
  | add_left hsub ih =>
    intro hwf
    exact WF.add (ih (WF.of_add_left hwf))
      (WF.mono (WF.of_add_right hwf) hsub.env_extends)
  | add_right _ ih =>
    intro hwf
    exact WF.add WF.num (ih (WF.of_add_right hwf))
  | mul_left hsub ih =>
    intro hwf
    exact WF.mul (ih (WF.of_mul_left hwf))
      (WF.mono (WF.of_mul_right hwf) hsub.env_extends)
  | mul_right _ ih =>
    intro hwf
    exact WF.mul WF.num (ih (WF.of_mul_right hwf))
  | val_step hsub ih =>
    intro hwf
    exact WF.mkVal (ih (WF.of_val_init hwf))
      (fun y hy => hsub.env_extends y (WF.of_val_filter hwf y hy))

-- helper: get the size of an expression
def Expr.size : Expr -> Nat
  | num _ => 0
  | add e1 e2 => 1 + e1.size + e2.size
  | mul e1 e2 => 1 + e1.size + e2.size
  | val _ e1 e2 => 1 + e1.size + e2.size
  | id _ => 1

-- each step strictly decreases expression size
theorem Step.size_decreasing (h : Step config config') :
    config'.snd.size < config.snd.size
  := by
  induction h with
  | add_left _ ih | mul_left _ ih | val_step _ ih => simp [Expr.size]; omega
  | add_right _ ih | mul_right _ ih => simp [Expr.size]; omega
  | add_val | mul_val | id _ | val_bind => simp [Expr.size]

-- Termination
theorem Step.termination : WellFounded (fun c' c => Step c c') :=
  Subrelation.wf
    (fun h => size_decreasing h)
    (InvImage.wf (fun (c : Env × Expr) => c.snd.size) Nat.lt_wfRel.wf)

-- Soundness = Progress + Preservation + Termination
theorem Step.soundness (hwf : WF (env, e)) :
    ∃ env' n, MultiStep (env, e) (env', .num n) := by
  suffices h : ∀ c, Acc (fun c' c => Step c c') c -> WF c ->
      ∃ env' n, MultiStep c (env', .num n) from
    h _ (termination.apply _) hwf
  intro c acc
  induction acc with
  | intro c _ ih =>
    obtain ⟨env, e⟩ := c
    intro hwf
    cases progress hwf with
    | inl hv =>
      cases hv with
      | num => exact ⟨_, _, .refl⟩
    | inr hstep =>
      obtain ⟨env', e', hstep⟩ := hstep
      obtain ⟨env'', n, hmulti⟩ := ih _ hstep (preservation hwf hstep)
      exact ⟨env'', n, .step hstep hmulti⟩

-- Completeness
-- We cannot show completeness, as SmallStep VAE is not complete.
-- Counterexample:
--   ⟨∅, {x := 1; x} + x⟩ -> ⟨[x -> 1], x + x⟩ ->* ⟨[x ↦ 1], 2⟩
--   but ⟨∅, {x := 1; x} + x⟩ is not WF
--   as fvs({x := 1; x} + x) = {x} ⊄ dom(∅) = ∅

end VAE
