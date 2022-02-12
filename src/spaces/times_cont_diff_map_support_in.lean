import spaces.bounded_times_cont_diff_map

open topological_space

def times_cont_diff_map_supported_in (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (K : set E)
  (n : with_top ℕ) : submodule 𝕜 (E → F) :=
{ carrier := {f | times_cont_diff 𝕜 n f ∧ ∀ x ∉ K, f x = 0},
  zero_mem' := ⟨times_cont_diff_zero_fun, λ x hx, rfl⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, λ x hx, 
    by rw [pi.add_apply, hf.2 x hx, hg.2 x hx, add_zero]⟩,
  smul_mem' := λ c f hf, ⟨times_cont_diff_const.smul hf.1, λ x hx,
    by rw [pi.smul_apply, hf.2 x hx, smul_zero]⟩ }

def to_bounded_times_cont_diff_map 