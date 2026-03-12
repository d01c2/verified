import Verified.VAE.Syntax

namespace VAE

inductive Reduce : Env × Expr -> Env × Expr -> Prop where
  | add_left :
    Reduce (env, e1) (env', e1') ->
    Reduce (env, .add e1 e2) (env', .add e1' e2)
  | add_right :
    Reduce (env, e2) (env', e2') ->
    Reduce (env, .add (.num n1) e2) (env', .add (.num n1) e2')
  | add_val : Reduce (env, .add (.num n1) (.num n2)) (env, .num (n1 + n2))
  | mul_left :
    Reduce (env, e1) (env', e1') ->
    Reduce (env, .mul e1 e2) (env', .mul e1' e2)
  | mul_right :
    Reduce (env, e2) (env', e2') ->
    Reduce (env, .mul (.num n1) e2) (env', .mul (.num n1) e2')
  | mul_val : Reduce (env, .mul (.num n1) (.num n2)) (env, .num (n1 * n2))
  | val_reduce :
    Reduce (env, e1) (env', e1') ->
    Reduce (env, .val x e1 e2) (env', .val x e1' e2)
  | val_val : Reduce (env, .val x (.num n) e2) (Env.update env x n, e2)
  | id : env x = some n -> Reduce (env, .id x) (env, .num n)

-- multi-step evaluation relations (reflexive-transitive closure)
inductive ReduceStar : Env × Expr -> Env × Expr -> Prop where
  | refl : ReduceStar c c
  | step : Reduce c c' -> ReduceStar c' c'' -> ReduceStar c c''

-- k-step evaluation relations
inductive ReduceK : Nat -> Env × Expr -> Env × Expr -> Prop where
  | refl : ReduceK 0 c c
  | step : Reduce c c' -> ReduceK k c' c'' -> ReduceK (k + 1) c c''

-- ReduceK implies ReduceStar
theorem ReduceK_to_ReduceStar (h : ReduceK k c c') : ReduceStar c c' := by
  induction h with
  | refl => exact ReduceStar.refl
  | step hstep _ ih => exact ReduceStar.step hstep ih

end VAE
