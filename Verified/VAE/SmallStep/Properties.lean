import Verified.VAE.Syntax
import Verified.VAE.SmallStep

namespace VAE

-- Soundness of SmallStep VAE
-- Every well-formed configuration evaluates to an integer

-- helper: collect free variables in an expression
def Expr.fvs : Expr -> List String
  | num _ => []
  | add e1 e2 => e1.fvs ++ e2.fvs
  | mul e1 e2 => e1.fvs ++ e2.fvs
  | val x e1 e2 => e1.fvs ++ (e2.fvs.filter (· != x))
  | id x => [x]

-- Well-Formed Expressions
def WF (env : Env) (e : Expr) : Prop := ∀ x ∈ e.fvs, (env x).isSome

-- helper: check if an expression is a value
inductive Expr.isValue : Expr -> Prop where
  | num : Expr.isValue (.num n)

-- Progress
theorem Reduce.progress (env : Env) (e : Expr) (hwf : WF env e) :
    e.isValue ∨ ∃ env' e', Reduce (env, e) (env', e')
  := by
  induction e with
  | num n => exact Or.inl .num
  | id x =>
    right
    have hx := hwf x (by simp [Expr.fvs])
    cases h : env x with
    | some n => exact ⟨_, _, Reduce.id h⟩
    | none => simp [h] at hx
  | add e1 e2 ih1 ih2 =>
    have hwf1 : WF env e1 := fun x hx => hwf x (List.mem_append_left _ hx)
    have hwf2 : WF env e2 := fun x hx => hwf x (List.mem_append_right _ hx)
    right
    cases ih1 hwf1 with
    | inl h1 => -- e1 is value
      cases ih2 hwf2 with
      | inl h2 => -- both e1 and e2 are values
        cases h1 with
        | num => cases h2 with
          | num => exact ⟨_, _, Reduce.add_val⟩
      | inr h2 => -- e2 can step
        obtain ⟨env', e2', h2⟩ := h2
        cases h1 with
        | num => exact ⟨_, _, Reduce.add_right h2⟩
    | inr h1 => -- e1 can step
      obtain ⟨env', e1', h1⟩ := h1
      exact ⟨_, _, Reduce.add_left h1⟩
  | mul e1 e2 ih1 ih2 =>
    have hwf1 : WF env e1 := fun x hx => hwf x (List.mem_append_left _ hx)
    have hwf2 : WF env e2 := fun x hx => hwf x (List.mem_append_right _ hx)
    right
    cases ih1 hwf1 with
    | inl h1 => -- e1 is value
      cases ih2 hwf2 with
      | inl h2 => -- both e1 and e2 are values
        cases h1 with
        | num => cases h2 with
          | num => exact ⟨_, _, Reduce.mul_val⟩
      | inr h2 => -- e2 can step
        obtain ⟨env', e2', h2⟩ := h2
        cases h1 with
        | num => exact ⟨_, _, Reduce.mul_right h2⟩
    | inr h1 => -- e1 can step
      obtain ⟨env', e1', h1⟩ := h1
      exact ⟨_, _, Reduce.mul_left h1⟩
  | val x e1 e2 ih1 ih2 =>
    have hwf1 : WF env e1 := fun y hy => hwf y (List.mem_append_left _ hy)
    right
    cases ih1 hwf1 with
    | inl h1 => -- e1 is value
      cases h1 with
      | num => exact ⟨_, _, Reduce.val_val⟩
    | inr h1 => -- e1 can step
      obtain ⟨env', e1', h1⟩ := h1
      exact ⟨_, _, Reduce.val_reduce h1⟩

-- helper: reduction only extends the environment (never removes bindings)
theorem Reduce.env_extends (h : Reduce c c') :
    ∀ y, (c.1 y).isSome → (c'.1 y).isSome := by
  induction h with
  | add_left _ ih | add_right _ ih | mul_left _ ih
  | mul_right _ ih | val_reduce _ ih => exact ih
  | add_val | mul_val | id _ => exact fun _ h => h
  | val_val =>
    intro y hy; simp only [Env.update]; split <;> simp_all

-- Preservation
theorem Reduce.preservation (hwf : WF c.1 c.2)
    (h : Reduce c c') : WF c'.1 c'.2 := by
  induction h with
  | add_val | mul_val | id _ => intro y hy; simp [Expr.fvs] at hy
  | add_right _ ih | mul_right _ ih => exact ih hwf
  | add_left hsub ih =>
    intro y hy
    cases List.mem_append.mp hy with
    | inl h => exact ih (fun z hz => hwf z (List.mem_append_left _ hz)) y h
    | inr h => exact env_extends hsub y (hwf y (List.mem_append_right _ h))
  | mul_left hsub ih =>
    intro y hy
    cases List.mem_append.mp hy with
    | inl h => exact ih (fun z hz => hwf z (List.mem_append_left _ hz)) y h
    | inr h => exact env_extends hsub y (hwf y (List.mem_append_right _ h))
  | val_reduce hsub ih =>
    intro y hy
    cases List.mem_append.mp hy with
    | inl h => exact ih (fun z hz => hwf z (List.mem_append_left _ hz)) y h
    | inr h => exact env_extends hsub y (hwf y (List.mem_append_right _ h))
  | @val_val env x n e2 =>
    intro y hy
    by_cases hyx : y = x
    · subst hyx; simp [Env.update]
    · simp only [Env.update]
      split <;> simp_all [beq_iff_eq]
      exact hwf y (List.mem_filter.mpr ⟨hy, by simp_all [bne]⟩)

-- helper: expression size (for termination arguments)
def Expr.size : Expr -> Nat
  | num _ => 0
  | add e1 e2 => 1 + e1.size + e2.size
  | mul e1 e2 => 1 + e1.size + e2.size
  | val _ e1 e2 => 1 + e1.size + e2.size
  | id _ => 1

-- helper: each reduction step strictly decreases expression size
theorem Reduce.size_decreasing (h : Reduce c c') : c'.2.size < c.2.size
  := by
  induction h with
  | add_left _ ih | mul_left _ ih | val_reduce _ ih => simp [Expr.size]; omega
  | add_right _ ih | mul_right _ ih => simp [Expr.size]; omega
  | add_val | mul_val | id _ | val_val => simp [Expr.size]

-- Termination
theorem Reduce.termination (env : Env) (e : Expr) (hwf : WF env e) :
    ∃ k env' n, ReduceK k (env, e) (env', .num n)
  := by
  suffices h : ∀ s env e, e.size ≤ s -> WF env e ->
      ∃ k env' n, ReduceK k (env, e) (env', .num n) from
    h e.size env e (Nat.le_refl _) hwf
  intro s
  induction s with
  | zero =>
    intro env e hs hwf
    cases e with
    | num n => exact ⟨0, env, n, ReduceK.refl⟩
    | id x => simp [Expr.size] at hs
    | add e1 e2 => simp [Expr.size] at hs
    | mul e1 e2 => simp [Expr.size] at hs
    | val x e1 e2 => simp [Expr.size] at hs
  | succ s ih =>
    intro env e hs hwf
    cases Reduce.progress env e hwf with
    | inl hv =>
      cases hv with
      | num => exact ⟨0, env, _, ReduceK.refl⟩
    | inr hstep =>
      obtain ⟨env', e', hstep⟩ := hstep
      have hwf' := preservation hwf hstep
      have hsd : e'.size < e.size := size_decreasing hstep
      obtain ⟨k, env'', n, hk⟩ := ih env' e' (by omega) hwf'
      exact ⟨k + 1, env'', n, ReduceK.step hstep hk⟩

-- Soundness = Progress + Preservation + Termination
theorem Reduce.soundness (env : Env) (e : Expr) (hwf : WF env e) :
    ∃ env' n, ReduceStar (env, e) (env', .num n)
  := by
  obtain ⟨k, env', n, hk⟩ := Reduce.termination env e hwf
  exact ⟨env', n, ReduceK_to_ReduceStar hk⟩

-- Completeness
-- Every configuration that evaluates to an integer is well-formed

-- However, we cannot show completeness, as SmallStep VAE is not complete
-- Counterexample:
--   < ∅, { x := 1; x } + x > -> < [x -> 1], x + x > ->* < [x -> 1], 2 >
--   but < ∅, { x := 1; x } + x > is not WF
--   as fvs({ x := 1; x } + x) = {x} ∉ dom(∅) = ∅

end VAE
