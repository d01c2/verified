import Verified.IMP.Syntax

namespace IMP

inductive Eval : Env -> Expr -> Value -> Prop where
  | num : Eval env (.num n) (.num n)
  | bool : Eval env (.bool b) (.bool b)
  | var : env x = some v -> Eval env (.var x) v
  | add :
    Eval env e1 (.num n1) -> Eval env e2 (.num n2) ->
    Eval env (.add e1 e2) (.num (n1 + n2))
  | mul :
    Eval env e1 (.num n1) -> Eval env e2 (.num n2) ->
    Eval env (.mul e1 e2) (.num (n1 * n2))
  | lt :
    Eval env e1 (.num n1) -> Eval env e2 (.num n2) ->
    Eval env (.lt e1 e2) (.bool (n1 < n2))

inductive Exec : Env -> Stmt -> Env -> Prop where
  | skip : Exec env .skip env
  | assign :
    Eval env e v ->
    Exec env (.assign x e) (Env.update env x v)
  | seq :
    Exec env s1 env1 -> Exec env1 s2 env2 ->
    Exec env (.seq s1 s2) env2
  | ite_true :
    Eval env e (.bool true) -> Exec env s1 env' ->
    Exec env (.ite e s1 s2) env'
  | ite_false :
    Eval env e (.bool false) -> Exec env s2 env' ->
    Exec env (.ite e s1 s2) env'
  | while_true :
    Eval env e (.bool true) -> Exec env s env' -> Exec env' (.while e s) env'' ->
    Exec env (.while e s) env''
  | while_false :
    Eval env e (.bool false) ->
    Exec env (.while e s) env

end IMP
