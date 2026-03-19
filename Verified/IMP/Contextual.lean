import Verified.IMP.Syntax

namespace IMP

-- Expression Evaluation Context
-- E ::= [·] | E + e | n + E | E * e | n * E | E < e | n < E
inductive Expr.EvalCtx where
  | hole
  | add_left (E : Expr.EvalCtx) (e : Expr)
  | add_right (n : Int) (E : Expr.EvalCtx)
  | mul_left (E : Expr.EvalCtx) (e : Expr)
  | mul_right (n : Int) (E : Expr.EvalCtx)
  | lt_left (E : Expr.EvalCtx) (e : Expr)
  | lt_right (n : Int) (E : Expr.EvalCtx)

def Expr.EvalCtx.plug : Expr.EvalCtx -> Expr -> Expr
  | .hole, e => e
  | .add_left E e2, e => .add (E.plug e) e2
  | .add_right n E, e => .add (.num n) (E.plug e)
  | .mul_left E e2, e => .mul (E.plug e) e2
  | .mul_right n E, e => .mul (.num n) (E.plug e)
  | .lt_left E e2, e => .lt (E.plug e) e2
  | .lt_right n E, e => .lt (.num n) (E.plug e)

-- Statement Evaluation Context
-- S ::= [·] | x := E | S; s | if E then s else s
inductive HoleSort where | expr | stmt

inductive Stmt.EvalCtx : HoleSort -> Type where
  | hole : Stmt.EvalCtx .stmt
  | assign (x : String) (E : Expr.EvalCtx) : Stmt.EvalCtx .expr
  | seq (S : Stmt.EvalCtx h) (s : Stmt) : Stmt.EvalCtx h
  | ite (E : Expr.EvalCtx) (s1 s2 : Stmt) : Stmt.EvalCtx .expr

def Stmt.EvalCtx.plugExpr : Stmt.EvalCtx .expr -> Expr -> Stmt
  | .assign x E, e => .assign x (E.plug e)
  | .seq S s, e => .seq (S.plugExpr e) s
  | .ite E s1 s2, e => .ite (E.plug e) s1 s2

def Stmt.EvalCtx.plugStmt : Stmt.EvalCtx .stmt -> Stmt -> Stmt
  | .hole, s => s
  | .seq S s2, s => .seq (S.plugStmt s) s2

inductive Expr.CStep : Env -> Expr -> Expr -> Prop where
  | ctx (E : Expr.EvalCtx) :
    Expr.CStep env e e' ->
    Expr.CStep env (E.plug e) (E.plug e')
  | var (h : x ∈ env) :
    Expr.CStep env (.var x) ((env.get x h).toExpr)
  | add_val :
    Expr.CStep env (.add (.num n1) (.num n2)) (.num (n1 + n2))
  | mul_val :
    Expr.CStep env (.mul (.num n1) (.num n2)) (.num (n1 * n2))
  | lt_val :
    Expr.CStep env (.lt (.num n1) (.num n2)) (.bool (n1 < n2))

inductive CExec : Env × Stmt -> Env × Stmt -> Prop where
  | ctx_expr (S : Stmt.EvalCtx .expr) :
    Expr.CStep env e e' ->
    CExec (env, S.plugExpr e) (env, S.plugExpr e')
  | ctx_stmt (S : Stmt.EvalCtx .stmt) :
    CExec (env, s) (env', s') ->
    CExec (env, S.plugStmt s) (env', S.plugStmt s')
  | assign_num :
    CExec (env, .assign x (.num n)) (env.insert x (.num n), .skip)
  | assign_bool :
    CExec (env, .assign x (.bool b)) (env.insert x (.bool b), .skip)
  | seq_skip :
    CExec (env, .seq .skip s2) (env, s2)
  | ite_true :
    CExec (env, .ite (.bool true) s1 s2) (env, s1)
  | ite_false :
    CExec (env, .ite (.bool false) s1 s2) (env, s2)
  | while :
    CExec (env, .while e s) (env, .ite e (.seq s (.while e s)) .skip)

end IMP
