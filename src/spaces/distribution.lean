import spaces.test_function

open_locale test_function

def distribution {E : Type*} [normed_group E] [normed_space ℝ E] (Ω : set E) 
  (F : Type*) [normed_group F] [normed_space ℝ F] (n : with_top ℕ) : Type* :=
Cc^n⟮Ω, E, ℝ; ℝ⟯ →L[ℝ] F

localized "notation `𝓓'` := distribution" in 
  test_function

namespace distribution

variables {E : Type*} [normed_group E] [normed_space ℝ E] (Ω : set E) 
  (F : Type*) [normed_group F] [normed_space ℝ F] (n : with_top ℕ)

def dirac (x : E) : 𝓓' Ω ℝ n := sorry

end distribution