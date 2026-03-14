import Std
import Verified.IMP.Syntax

namespace IMP

@[coe] def Value.toExpr : Value -> Expr
  | .num n => .num n
  | .bool b => .bool b

instance : Coe Value Expr := ⟨Value.toExpr⟩

inductive Expr.Step : Env × Expr -> Env × Expr -> Prop where
  | var (h : x ∈ env) :
    Expr.Step (env, .var x) (env, (env.get x h : Value))
  | add_left :
    Expr.Step (env, e1) (env, e1') ->
    Expr.Step (env, .add e1 e2) (env, .add e1' e2)
  | add_right :
    Expr.Step (env, e2) (env, e2') ->
    Expr.Step (env, .add (.num n1) e2) (env, .add (.num n1) e2')
  | add_val :
    Expr.Step (env, .add (.num n1) (.num n2)) (env, .num (n1 + n2))
  | mul_left :
    Expr.Step (env, e1) (env, e1') ->
    Expr.Step (env, .mul e1 e2) (env, .mul e1' e2)
  | mul_right :
    Expr.Step (env, e2) (env, e2') ->
    Expr.Step (env, .mul (.num n1) e2) (env, .mul (.num n1) e2')
  | mul_val :
    Expr.Step (env, .mul (.num n1) (.num n2)) (env, .num (n1 * n2))
  | lt_left :
    Expr.Step (env, e1) (env, e1') ->
    Expr.Step (env, .lt e1 e2) (env, .lt e1' e2)
  | lt_right :
    Expr.Step (env, e2) (env, e2') ->
    Expr.Step (env, .lt (.num n1) e2) (env, .lt (.num n1) e2')
  | lt_val :
    Expr.Step (env, .lt (.num n1) (.num n2)) (env, .bool (n1 < n2))

inductive Stmt.Step : Env × Stmt -> Env × Stmt -> Prop where
  | assign_step :
    Expr.Step (env, e) (env, e') ->
    Stmt.Step (env, .assign x e) (env, .assign x e')
  | assign_val (v : Value) :
    Stmt.Step (env, .assign x v) (env.insert x v, .skip)
  | seq_left :
    Stmt.Step (env, s1) (env', s1') ->
    Stmt.Step (env, .seq s1 s2) (env', .seq s1' s2)
  | seq_skip : Stmt.Step (env, .seq .skip s2) (env, s2)
  | ite_step :
    Expr.Step (env, e) (env, e') ->
    Stmt.Step (env, .ite e s1 s2) (env, .ite e' s1 s2)
  | ite_true :
    Stmt.Step (env, .ite (.bool true) s1 s2) (env, s1)
  | ite_false :
    Stmt.Step (env, .ite (.bool false) s1 s2) (env, s2)
  | while :
    Stmt.Step (env, .while e s) (env, .ite e (.seq s (.while e s)) .skip)

end IMP
