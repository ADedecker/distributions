import spaces.test_function
import measure_theory.measure.lebesgue

open measure_theory
open_locale test_function

abbreviation distribution {E : Type*} [normed_group E] [normed_space ℝ E] (Ω : set E) 
  (F : Type*) [normed_group F] [normed_space ℝ F] (n : with_top ℕ) : Type* :=
Cc^n⟮Ω, E, ℝ; ℝ⟯ →L[ℝ] F

localized "notation `𝓓'` := distribution" in distribution

namespace distribution

variables {E : Type*} [normed_group E] [normed_space ℝ E] (Ω : set E) 
  (F : Type*) [normed_group F] [normed_space ℝ F] (n : with_top ℕ)

noncomputable def dirac (x : E) : 𝓓' Ω ℝ n := 
  (bounded_continuous_function.eval_clm ℝ x) ∘L 
  (bounded_cont_diff_map.to_bounded_continuous_map ℝ E ℝ n) ∘L
  (test_function.to_bounded_cont_diff_mapL)

@[simp] lemma dirac_apply (x : E) (f : Cc^n⟮Ω, E, ℝ; ℝ⟯) : dirac Ω n x f = f x := rfl

noncomputable def dirac' (x : E) : Cc^n⟮Ω, E, ℝ; ℝ⟯ →L[ℝ] ℝ :=
let tmp : Cc^n⟮Ω, E, ℝ; ℝ⟯ →ₗ[ℝ] ℝ :=
  { to_fun := λ f, f x,
    map_add' := λ f g, rfl,
    map_smul' := λ c f, rfl } in
{ to_linear_map := tmp,
  cont :=
  begin
    change continuous tmp,
    rw test_function.continuous_iff_of_linear_of_normed_codomain tmp,
    intros K hK,
    refine ⟨0, 1, zero_lt_one, λ f hf, _⟩,
    change ∥f x∥ ≤ _,
    rw [one_mul],
    sorry,
  end }



--noncomputable def of_measure [measurable_space E] (x : E) (μ : measure E) : 
--  𝓓' Ω ℝ n := 
--  (L1.integral_clm) ∘L 
--  --(bounded_continuous_function.to_Lp 1 μ)

end distribution