import Verified.IMP.Syntax
import Verified.IMP.BigStep

namespace IMP

-- Equivalence of Statements: while unfolding
theorem while_unfold :
    Exec env (.while e s) env' <->
    Exec env (.ite e (.seq s (.while e s)) .skip) env' where
  mp h := match h with
    | .while_true he hs hw => .ite_true he (.seq hs hw)
    | .while_false he => .ite_false he .skip
  mpr h := match h with
    | .ite_true he (.seq hs hw) => .while_true he hs hw
    | .ite_false he .skip => .while_false he

-- Determinism of Expression Evaluation
theorem Eval.deterministic
    (h1 : Eval env e v1) (h2 : Eval env e v2) :
    v1 = v2 :=
  match h1, h2 with
  | .num, .num => rfl
  | .bool, .bool => rfl
  | .var _, .var _ => rfl
  | .add he1 he2, .add he1' he2' =>
    match Eval.deterministic he1 he1', Eval.deterministic he2 he2' with
    | rfl, rfl => rfl
  | .mul he1 he2, .mul he1' he2' =>
    match Eval.deterministic he1 he1', Eval.deterministic he2 he2' with
    | rfl, rfl => rfl
  | .lt he1 he2, .lt he1' he2' =>
    match Eval.deterministic he1 he1', Eval.deterministic he2 he2' with
    | rfl, rfl => rfl

-- Determinism of Statement Execution
theorem Exec.deterministic
    (h1 : Exec env s env') (h2 : Exec env s env'') :
    env' = env'' :=
  match h1, h2 with
  | .skip, .skip => rfl
  | .assign heval, .assign heval' =>
    match Eval.deterministic heval heval' with
    | rfl => rfl
  | .seq hs1 hs2, .seq hs1' hs2' =>
    match Exec.deterministic hs1 hs1' with
    | rfl => Exec.deterministic hs2 hs2'
  | .ite_true _ hs, .ite_true _ hs' => Exec.deterministic hs hs'
  | .ite_true he _, .ite_false he' _ => nomatch Eval.deterministic he he'
  | .ite_false he _, .ite_true he' _ => nomatch Eval.deterministic he he'
  | .ite_false _ hs, .ite_false _ hs' => Exec.deterministic hs hs'
  | .while_true _ hs hw, .while_true _ hs' hw' =>
    match Exec.deterministic hs hs' with
    | rfl => Exec.deterministic hw hw'
  | .while_true he _ _, .while_false he' => nomatch Eval.deterministic he he'
  | .while_false he, .while_true he' _ _ => nomatch Eval.deterministic he he'
  | .while_false _, .while_false _ => rfl

end IMP
