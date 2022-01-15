import geometry.manifold.times_cont_mdiff_map

open topological_space set
open_locale manifold

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
(s : set E)
(F : Type*) [normed_group F] [normed_space 𝕜 F]
(n : with_top ℕ)

@[protect_proj]
structure times_cont_diff_map_on :=
(to_fun                 : E → F)
(eq_zero                : ∀ x ∉ s, to_fun x = 0)
(times_cont_diff_to_fun : times_cont_diff_on 𝕜 n to_fun s)

def times_cont_diff_map := times_cont_diff_map_on 𝕜 (univ : set E) F

#check iterated_fderiv_within

#check times_cont_mdiff_map

example : topological_space (C^n⟮s; F⟯[𝕜]) := infer_instance