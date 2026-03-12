import Verified.IMP.Syntax
import Verified.IMP.BigStep

namespace IMP

-- Equivalence of Statements

theorem while_unfold :
    Exec env (.while e s) env' <-> Exec env (.ite e (.seq s (.while e s)) .skip) env'
  := by
  constructor
  · -- (->)
    intro h
    cases h with
    | while_true he hs hw => exact Exec.ite_true he (Exec.seq hs hw)
    | while_false he => exact Exec.ite_false he Exec.skip
  · -- (<-)
    intro h
    cases h with
    | ite_true he hs =>
      cases hs with
      | seq hs hw => exact Exec.while_true he hs hw
    | ite_false he hs =>
      cases hs with
      | skip => exact Exec.while_false he

-- Determinism of BigStep IMP

theorem Eval.deterministic (h1 : Eval env e v1) (h2 : Eval env e v2) :
    v1 = v2 := by
  induction h1 generalizing v2 with
  | num => cases h2; rfl
  | bool => cases h2; rfl
  | var h1 => cases h2 with
    | var h2 => rw [h1] at h2; injection h2
  | add he1 he2 ih1 ih2 =>
    cases h2 with
    | add he1' he2' =>
      have := ih1 he1'; injection this with this
      have := ih2 he2'; injection this with this
      subst_vars; rfl
  | mul he1 he2 ih1 ih2 =>
    cases h2 with
      | mul he1' he2' =>
        have := ih1 he1'; injection this with this
        have := ih2 he2'; injection this with this
        subst_vars; rfl
  | lt he1 he2 ih1 ih2 =>
    cases h2 with
    | lt he1' he2' =>
      have := ih1 he1'; injection this with this
      have := ih2 he2'; injection this with this
      subst_vars; rfl

theorem Exec.deterministic (h1 : Exec env s env') (h2 : Exec env s env'') :
    env' = env'' := by
  induction h1 generalizing env'' with
  | skip => cases h2; rfl
  | assign heval =>
    cases h2 with
    | assign heval' =>
      have := Eval.deterministic heval heval'
      subst this; rfl
  | seq hs1 hs2 ih1 ih2 =>
    cases h2 with
    | seq hs1' hs2' =>
      have := ih1 hs1'; subst this
      exact ih2 hs2'
  | ite_true heval hs ih =>
    cases h2 with
    | ite_true heval' hs' => exact ih hs'
    | ite_false heval' hs' =>
      have := Eval.deterministic heval heval'
      cases this
  | ite_false heval hs ih =>
    cases h2 with
    | ite_true heval' hs' =>
      have := Eval.deterministic heval heval'
      cases this
    | ite_false heval' hs' => exact ih hs'
  | while_true heval hs hw ih_s ih_w =>
    cases h2 with
    | while_true heval' hs' hw' =>
      have := ih_s hs'; subst this
      exact ih_w hw'
    | while_false heval' =>
      have := Eval.deterministic heval heval'
      cases this
  | while_false heval =>
    cases h2 with
    | while_true heval' hs' hw' =>
      have := Eval.deterministic heval heval'
      cases this
    | while_false => rfl

end IMP
