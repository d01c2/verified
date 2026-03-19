import Verified.VAE.Syntax

namespace VAE

-- Evaluation Context
-- E ::= [·] | E + e | n + E | E * e | n * E | x := E; e
inductive EvalCtx where
  | hole
  | add_left (E : EvalCtx) (e : Expr)
  | add_right (n : Int) (E : EvalCtx)
  | mul_left (E : EvalCtx) (e : Expr)
  | mul_right (n : Int) (E : EvalCtx)
  | val_ctx (x : String) (E : EvalCtx) (e : Expr)

def EvalCtx.plug : EvalCtx -> Expr -> Expr
  | .hole, e => e
  | .add_left E e2, e => .add (E.plug e) e2
  | .add_right n E, e => .add (.num n) (E.plug e)
  | .mul_left E e2, e => .mul (E.plug e) e2
  | .mul_right n E, e => .mul (.num n) (E.plug e)
  | .val_ctx x E e2, e => .val x (E.plug e) e2

inductive CStep : Env × Expr -> Env × Expr -> Prop where
  | ctx (E : EvalCtx) :
    CStep (env, e) (env', e') ->
    CStep (env, E.plug e) (env', E.plug e')
  | add_val :
    CStep (env, .add (.num n1) (.num n2)) (env, .num (n1 + n2))
  | mul_val :
    CStep (env, .mul (.num n1) (.num n2)) (env, .num (n1 * n2))
  | val_bind :
    CStep (env, .val x (.num n) e2) (env.insert x n, e2)
  | id (h : x ∈ env) :
    CStep (env, .id x) (env, .num (env.get x h))

end VAE
