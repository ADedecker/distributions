import spaces.times_cont_diff_map_support_in

private def test_function_submodule (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (n : with_top ℕ) : 
submodule 𝕜 (E → F) :=
{ carrier := {f | } }