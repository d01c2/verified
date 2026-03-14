import Std

namespace VAE

inductive Expr where
  | num (n : Int)
  | add (e1 e2 : Expr)
  | mul (e1 e2 : Expr)
  | val (x : String) (e1 : Expr) (e2 : Expr)
  | id (x : String)

abbrev Env := Std.HashMap String Int

end VAE
