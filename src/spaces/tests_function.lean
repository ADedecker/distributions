import geometry.manifold.times_cont_mdiff_map

open function topological_space

open_locale manifold

variables (𝕂 : Type*) [nondiscrete_normed_field 𝕂] 
  {E : Type*} [normed_group E] [normed_space 𝕂 E] (Ω : opens E) 
  (F : Type*) [normed_group F] [normed_space 𝕂 F] 

structure compact_times_cont_diff_map_on (n : with_top ℕ) (K : set Ω) extends C^n⟮𝓘(𝕂, E), Ω; 𝓘(𝕂, F), F⟯ :=
(support_subset : support to_fun ⊆ K)

localized "notation `D^` n `_` K `⟮` Ω `, ` F `⟯[` 𝕂 `]` :=
  compact_times_cont_diff_map_on 𝕂 Ω F n K" in distribution
localized "notation `D_` K `⟮` Ω `, ` F `⟯[` 𝕂 `]` :=
  compact_times_cont_diff_map_on 𝕂 Ω F ⊤ K" in distribution

structure compact_times_cont_diff_map (n : with_top ℕ) extends C^n⟮𝓘(𝕂, E), Ω; 𝕂⟯ :=
(compact_support : ∃ K, is_compact K ∧ support to_fun ⊆ K)

abbreviation test_function_on (K : set Ω) := compact_times_cont_diff_map_on 𝕂 Ω ⊤ K