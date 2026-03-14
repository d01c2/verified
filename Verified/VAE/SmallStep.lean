import Verified.VAE.Syntax

namespace VAE

inductive Step : Env × Expr -> Env × Expr -> Prop where
  | add_left :
    Step (env, e1) (env', e1') ->
    Step (env, .add e1 e2) (env', .add e1' e2)
  | add_right :
    Step (env, e2) (env', e2') ->
    Step (env, .add (.num n1) e2) (env', .add (.num n1) e2')
  | add_val :
    Step (env, .add (.num n1) (.num n2)) (env, .num (n1 + n2))
  | mul_left :
    Step (env, e1) (env', e1') ->
    Step (env, .mul e1 e2) (env', .mul e1' e2)
  | mul_right :
    Step (env, e2) (env', e2') ->
    Step (env, .mul (.num n1) e2) (env', .mul (.num n1) e2')
  | mul_val :
    Step (env, .mul (.num n1) (.num n2)) (env, .num (n1 * n2))
  | val_step :
    Step (env, e1) (env', e1') ->
    Step (env, .val x e1 e2) (env', .val x e1' e2)
  | val_bind :
    Step (env, .val x (.num n) e2) (env.insert x n, e2)
  | id (h : x ∈ env) :
    Step (env, .id x) (env, .num (env.get x h))

-- multi-step evaluation relations (reflexive-transitive closure)
inductive MultiStep : Env × Expr -> Env × Expr -> Prop where
  | refl : MultiStep c c
  | step : Step c c' -> MultiStep c' c'' -> MultiStep c c''

end VAE
