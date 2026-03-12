import Verified.IMP.Syntax

namespace IMP

@[coe] def Value.toExpr : Value -> Expr
  | .num n => .num n
  | .bool b => .bool b

instance : Coe Value Expr := ⟨Value.toExpr⟩

inductive Reduce : Env × Expr -> Env × Expr -> Prop where
  | var : env x = some v -> Reduce (env, .var x) (env, v)
  | add_left :
    Reduce (env, e1) (env, e1') ->
    Reduce (env, .add e1 e2) (env, .add e1' e2)
  | add_right :
    Reduce (env, e2) (env, e2') ->
    Reduce (env, .add (.num n1) e2) (env, .add (.num n1) e2')
  | add_val : Reduce (env, .add (.num n1) (.num n2)) (env, .num (n1 + n2))
  | mul_left :
    Reduce (env, e1) (env, e1') ->
    Reduce (env, .mul e1 e2) (env, .mul e1' e2)
  | mul_right :
    Reduce (env, e2) (env, e2') ->
    Reduce (env, .mul (.num n1) e2) (env, .mul (.num n1) e2')
  | mul_val : Reduce (env, .mul (.num n1) (.num n2)) (env, .num (n1 * n2))
  | lt_left :
    Reduce (env, e1) (env, e1') ->
    Reduce (env, .lt e1 e2) (env, .lt e1' e2)
  | lt_right :
    Reduce (env, e2) (env, e2') ->
    Reduce (env, .lt (.num n1) e2) (env, .lt (.num n1) e2')
  | lt_val : Reduce (env, .lt (.num n1) (.num n2)) (env, .bool (n1 < n2))

inductive Step : Env × Stmt -> Env × Stmt -> Prop where
  | assign_reduce :
    Reduce (env, e) (env, e') ->
    Step (env, .assign x e) (env, .assign x e')
  | assign_val (v : Value) : Step (env, .assign x v) (Env.update env x v, .skip)
  | seq_left :
    Step (env, s1) (env', s1') ->
    Step (env, .seq s1 s2) (env', .seq s1' s2)
  | seq_skip : Step (env, .seq .skip s2) (env, s2)
  | ite_reduce :
    Reduce (env, e) (env, e') ->
    Step (env, .ite e s1 s2) (env, .ite e' s1 s2)
  | ite_true : Step (env, .ite (.bool true) s1 s2) (env, s1)
  | ite_false : Step (env, .ite (.bool false) s1 s2) (env, s2)
  | while : Step (env, .while e s) (env, .ite e (.seq s (.while e s)) .skip)

end IMP
