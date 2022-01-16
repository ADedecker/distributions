import geometry.manifold.times_cont_mdiff_map

open topological_space set
open_locale manifold

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
(Ω : set E)
(F : Type*) [normed_group F] [normed_space 𝕜 F]
(n : with_top ℕ)

@[protect_proj]
structure times_cont_diff_map_on :=
(to_fun                 : E → F)
(eq_zero                : ∀ x ∉ Ω, to_fun x = 0)
(times_cont_diff_to_fun : times_cont_diff_on 𝕜 n to_fun Ω)

def times_cont_diff_map := times_cont_diff_map_on 𝕜 (univ : set E) F

localized "notation `C^` n `⟮` Ω `, ` F `⟯[` 𝕂 `]` :=
  times_cont_diff_map_on 𝕂 Ω F n" in distribution

def times_cont_diff_map_on.to_part_fun (f : C^n⟮Ω, F⟯[𝕜]) (x : Ω) : F := 
f.to_fun x

instance : topological_space (C^n⟮Ω, F⟯[𝕜]) := sorry

@[protect_proj]
structure times_cont_diff_map_supported_on (K : set Ω) extends C^n⟮Ω, F⟯[𝕜] :=
(support_in : function.support (to_times_cont_diff_map_on.to_part_fun 𝕜 Ω F n) ⊆ K)

localized "notation `C^` n`⟮` Ω `, ` F `; ` K`⟯[` 𝕂 `]` :=
  times_cont_diff_map_supported_on 𝕂 Ω F n K" in distribution

instance foo (K : set Ω) : topological_space (C^n⟮Ω, F; K⟯[𝕜]) := infer_instance