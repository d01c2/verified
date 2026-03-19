import Std
import Verified.VAE.Syntax
import Verified.VAE.SmallStep

namespace VAE

-- Soundness of SmallStep VAE

-- helper: collect free variables
def Expr.fvs : Expr -> Std.HashSet String
  | num _ => {}
  | add e1 e2 => e1.fvs ∪ e2.fvs
  | mul e1 e2 => e1.fvs ∪ e2.fvs
  | val x e1 e2 => e1.fvs ∪ (e2.fvs.erase x)
  | id x => {x}

-- Well-Formed Configuration: fvs(e) ⊆ dom(σ)
def WF (config : Env × Expr) : Prop :=
  ∀ x ∈ config.snd.fvs, x ∈ config.fst

-- helper: check if an expression is a value
inductive Expr.isValue : Expr -> Prop where
  | num : Expr.isValue (.num n)

-- WF Decomposition
theorem WF.of_add_left
    (h : WF (env, .add e1 e2)) :
    WF (env, e1) :=
  fun x hx =>
    h x (Std.HashSet.mem_union_iff.mpr (.inl hx))

theorem WF.of_add_right
    (h : WF (env, .add e1 e2)) :
    WF (env, e2) :=
  fun x hx =>
    h x (Std.HashSet.mem_union_iff.mpr (.inr hx))

theorem WF.of_mul_left
    (h : WF (env, .mul e1 e2)) :
    WF (env, e1) :=
  fun x hx =>
    h x (Std.HashSet.mem_union_iff.mpr (.inl hx))

theorem WF.of_mul_right
    (h : WF (env, .mul e1 e2)) :
    WF (env, e2) :=
  fun x hx =>
    h x (Std.HashSet.mem_union_iff.mpr (.inr hx))

theorem WF.of_val_init
    (h : WF (env, .val x e1 e2)) :
    WF (env, e1) :=
  fun y hy =>
    h y (Std.HashSet.mem_union_iff.mpr (.inl hy))

theorem WF.of_val_filter
    (h : WF (env, .val x e1 e2)) :
    ∀ y, y ∈ e2.fvs.erase x -> y ∈ env :=
  fun y hy =>
    h y (Std.HashSet.mem_union_iff.mpr (.inr hy))

theorem WF.of_val_body
    (h : WF (env, .val x e1 e2)) (n : Int) :
    WF (env.insert x n, e2) :=
  fun y hy => by
    by_cases heq : x == y
    · exact Std.HashMap.mem_insert.mpr
        (.inl heq)
    · exact Std.HashMap.mem_insert.mpr (.inr
        (WF.of_val_filter h y
          (Std.HashSet.mem_erase.mpr
            ⟨Bool.eq_false_iff.mpr heq, hy⟩)))

-- WF Composition
theorem WF.num : WF (env, .num n) :=
  fun _ h => absurd h (by simp [Expr.fvs])

theorem WF.add
    (h1 : WF (env, e1)) (h2 : WF (env, e2)) :
    WF (env, .add e1 e2) :=
  fun x hx =>
    (Std.HashSet.mem_union_iff.mp hx).elim
      (h1 x) (h2 x)

theorem WF.mul
    (h1 : WF (env, e1)) (h2 : WF (env, e2)) :
    WF (env, .mul e1 e2) :=
  fun x hx =>
    (Std.HashSet.mem_union_iff.mp hx).elim
      (h1 x) (h2 x)

theorem WF.mkVal
    (h1 : WF (env, e1)) (h2 : ∀ y, y ∈ e2.fvs.erase x -> y ∈ env) :
    WF (env, .val x e1 e2) :=
  fun y hy =>
    (Std.HashSet.mem_union_iff.mp hy).elim
      (h1 y) (h2 y)

-- WF Monotonicity
theorem WF.mono
    (hwf : WF (env, e)) (hext : ∀ x, x ∈ env -> x ∈ env') :
    WF (env', e) :=
  fun x hx => hext x (hwf x hx)

-- Progress
theorem Step.progress
    (hwf : WF (env, e)) :
    e.isValue ∨ ∃ env' e', Step (env, e) (env', e') :=
  match e with
  | .num _ => .inl .num
  | .id x =>
    let hx := hwf x (by simp [Expr.fvs])
    .inr ⟨_, .num (env.get x hx), .id hx⟩
  | .add _ _ =>
    match Step.progress hwf.of_add_left, Step.progress hwf.of_add_right with
    | .inr ⟨_, _, h⟩, _ =>
      .inr ⟨_, _, .add_left h⟩
    | .inl .num, .inr ⟨_, _, h⟩ =>
      .inr ⟨_, _, .add_right h⟩
    | .inl .num, .inl .num =>
      .inr ⟨_, _, .add_val⟩
  | .mul _ _ =>
    match Step.progress hwf.of_mul_left, Step.progress hwf.of_mul_right with
    | .inr ⟨_, _, h⟩, _ =>
      .inr ⟨_, _, .mul_left h⟩
    | .inl .num, .inr ⟨_, _, h⟩ =>
      .inr ⟨_, _, .mul_right h⟩
    | .inl .num, .inl .num =>
      .inr ⟨_, _, .mul_val⟩
  | .val _ _ _ =>
    match Step.progress hwf.of_val_init with
    | .inr ⟨_, _, h⟩ =>
      .inr ⟨_, _, .val_step h⟩
    | .inl .num => .inr ⟨_, _, .val_bind⟩
termination_by e

-- helper: Step rules only extend environments
theorem Step.env_extends
    (h : Step config config') (x : String) (hx : x ∈ config.fst) :
    x ∈ config'.fst :=
  match h with
  | .add_left hsub =>
    Step.env_extends hsub x hx
  | .add_right hsub =>
    Step.env_extends hsub x hx
  | .add_val => hx
  | .mul_left hsub =>
    Step.env_extends hsub x hx
  | .mul_right hsub =>
    Step.env_extends hsub x hx
  | .mul_val => hx
  | .id _ => hx
  | .val_step hsub =>
    Step.env_extends hsub x hx
  | .val_bind =>
    Std.HashMap.mem_insert.mpr (.inr hx)

-- Preservation
theorem Step.preservation
    (hwf : WF config) (h : Step config config') :
    WF config' :=
  match h with
  | .add_val | .mul_val | .id _ => WF.num
  | .val_bind => WF.of_val_body hwf _
  | .add_left hsub =>
    WF.add
      (Step.preservation hwf.of_add_left hsub)
      (WF.mono hwf.of_add_right
        hsub.env_extends)
  | .add_right hsub =>
    WF.add WF.num
      (Step.preservation
        hwf.of_add_right hsub)
  | .mul_left hsub =>
    WF.mul
      (Step.preservation hwf.of_mul_left hsub)
      (WF.mono hwf.of_mul_right
        hsub.env_extends)
  | .mul_right hsub =>
    WF.mul WF.num
      (Step.preservation
        hwf.of_mul_right hsub)
  | .val_step hsub =>
    WF.mkVal
      (Step.preservation hwf.of_val_init hsub)
      (fun y hy =>
        hsub.env_extends y
          (WF.of_val_filter hwf y hy))

-- helper: expression size
def Expr.size : Expr -> Nat
  | num _ => 0
  | add e1 e2 => 1 + e1.size + e2.size
  | mul e1 e2 => 1 + e1.size + e2.size
  | val _ e1 e2 => 1 + e1.size + e2.size
  | id _ => 1

-- each step strictly decreases expression size
theorem Step.size_decreasing
    (h : Step config config') :
    config'.snd.size < config.snd.size :=
  match h with
  | .add_left hsub =>
    have := Step.size_decreasing hsub
    by simp [Expr.size]; omega
  | .add_right hsub =>
    have := Step.size_decreasing hsub
    by simp [Expr.size]; omega
  | .mul_left hsub =>
    have := Step.size_decreasing hsub
    by simp [Expr.size]; omega
  | .mul_right hsub =>
    have := Step.size_decreasing hsub
    by simp [Expr.size]; omega
  | .val_step hsub =>
    have := Step.size_decreasing hsub
    by simp [Expr.size]; omega
  | .add_val | .mul_val
  | .id _ | .val_bind =>
    by simp [Expr.size]

-- Termination
theorem Step.termination :
    WellFounded (fun c' c => Step c c') :=
  Subrelation.wf
    (fun h => size_decreasing h)
    (InvImage.wf
      (fun (c : Env × Expr) => c.snd.size)
      Nat.lt_wfRel.wf)

-- Soundness = Progress + Preservation + Termination
theorem Step.soundness
    (hwf : WF (env, e)) :
    ∃ env' n, MultiStep (env, e) (env', .num n) := by
  suffices h : ∀ c,
      Acc (fun c' c => Step c c') c →
      WF c →
      ∃ env' n, MultiStep c (env', .num n) from
    h _ (termination.apply _) hwf
  intro c acc
  induction acc with
  | intro c _ ih =>
    obtain ⟨env, e⟩ := c
    intro hwf
    match progress hwf with
    | .inl .num => exact ⟨_, _, .refl⟩
    | .inr ⟨_, _, hstep⟩ =>
      have ⟨env'', n, hmulti⟩ :=
        ih _ hstep (preservation hwf hstep)
      exact ⟨env'', n, .step hstep hmulti⟩

-- Completeness
-- We cannot show completeness, as SmallStep
-- VAE is not complete. Counterexample:
--   ⟨∅, {x := 1; x} + x⟩ ->
--   ⟨[x -> 1], x + x⟩ ->* ⟨[x ↦ 1], 2⟩
--   but ⟨∅, {x := 1; x} + x⟩ is not WF
--   as fvs({x := 1; x} + x) = {x} ⊄ dom(∅)

end VAE
