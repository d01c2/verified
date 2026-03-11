namespace Imp

inductive Expr where
  | num (n : Int)
  | bool (b: Bool)
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

abbrev Env := String -> Value

end Imp
