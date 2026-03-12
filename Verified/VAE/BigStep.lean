import Verified.VAE.Syntax

namespace VAE

inductive Eval : Env -> Expr -> Int -> Prop where
  | num n : Eval env (.num n) n
  | add :
    Eval env e1 n1 -> Eval env e2 n2 ->
    Eval env (.add e1 e2) (n1 + n2)
  | mul :
    Eval env e1 n1 -> Eval env e2 n2 ->
    Eval env (.mul e1 e2) (n1 * n2)
  | val :
    Eval env e1 n1 -> Eval (Env.update env x n1) e2 n2 ->
    Eval env (.val x e1 e2) n2
  | id : env x = some n -> Eval env (.id x) n

end VAE
