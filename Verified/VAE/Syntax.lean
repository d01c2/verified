namespace VAE

inductive Expr where
  | num (n : Int)
  | add (e1 e2 : Expr)
  | mul (e1 e2 : Expr)
  | val (x : String) (e1 : Expr) (e2 : Expr)
  | id (x : String)

abbrev Env := String -> Option Int

-- helper: update the environment
def Env.update (env : Env) (x : String) (v : Int) : Env :=
  fun y => if y == x then some v else env y

end VAE
