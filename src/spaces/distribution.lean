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
  (bounded_cont_diff_map.to_bounded_continuous_function ℝ E ℝ n) ∘L
  (test_function.to_bounded_cont_diff_mapL)

@[simp] lemma dirac_apply (x : E) (f : Cc^n⟮Ω, E, ℝ; ℝ⟯) : dirac Ω n x f = f x := rfl

noncomputable def of_measure [measurable_space E] [opens_measurable_space E] 
  (μ : measure E) [is_finite_measure_on_compacts μ] : 
  𝓓' Ω ℝ n := 
(L1.integral_clm) ∘L (test_function.to_Lp n 1 μ)

@[simp] lemma of_measure_apply [measurable_space E] [opens_measurable_space E] 
  (μ : measure E) [is_finite_measure_on_compacts μ] (f : Cc^n⟮Ω, E, ℝ; ℝ⟯) : 
  of_measure Ω n μ f = ∫ x : E, f x ∂μ := 
by rw [of_measure, integral_eq f (f.integrable μ), L1.integral_eq]; refl

noncomputable def dirac' [measurable_space E] [opens_measurable_space E] (x : E) : 𝓓' Ω ℝ n := 
  of_measure Ω n (measure.dirac x)

lemma dirac_eq_dirac' [measurable_space E] [opens_measurable_space E] (x : E) : 
  dirac Ω n x = dirac' Ω n x :=
begin
  ext f,
  rw [dirac', dirac_apply, of_measure_apply, integral_dirac]
end

end distribution

section dderiv -- This will be generalized to fderiv, but I want to do some tests

variables (Ω : set ℝ) (F : Type*) [normed_group F] [normed_space ℝ F]

--def dderivₗ : 𝓓' Ω F ⊤ →ₗ[ℝ] 𝓓' Ω F ⊤ :=

end dderiv