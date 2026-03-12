namespace IMP

inductive Expr where
  | num (n : Int)
  | bool (b : Bool)
  | var (x : String)
  | add (e1 e2 : Expr)
  | mul (e1 e2 : Expr)
  | lt (e1 e2 : Expr)

inductive Stmt where
  | skip
  | assign (x : String) (e : Expr)
  | seq (s1 s2 : Stmt)
  | ite (e : Expr) (s1 s2 : Stmt)
  | while (e : Expr) (s : Stmt)

inductive Value where
  | num (n : Int)
  | bool (b : Bool)

abbrev Env := String -> Option Value

-- helper: update the environment
def Env.update (env : Env) (x : String) (v : Value) : Env :=
  fun y => if y == x then some v else env y

end IMP
