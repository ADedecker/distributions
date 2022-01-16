import analysis.convex.basic
import topology.algebra.module.basic
import .topology_algebra_lattice

open topological_space filter

open_locale topological_space

section locally_convex_space

variables (𝕂 E : Type*) [ordered_semiring 𝕂] [add_comm_monoid E] [module 𝕂 E] 
  [topological_space 𝕂] [topological_space E] [topological_ring 𝕂] [has_continuous_add E]
  [has_continuous_smul 𝕂 E]

class locally_convex_space :=
(exists_convex_nhds_zero' : ∀ s ∈ (𝓝 0 : filter E), ∃ c ∈ (𝓝 0 : filter E), c ⊆ s ∧ convex 𝕂 c)

lemma locally_convex_space.exists_convex_nhds_zero [locally_convex_space 𝕂 E] {s : set E}
  (hs : s ∈ (𝓝 0 : filter E)) : ∃ c ∈ (𝓝 0 : filter E), c ⊆ s ∧ convex 𝕂 c :=
@locally_convex_space.exists_convex_nhds_zero' 𝕂 E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› s hs

def locally_convex_space.nhds_zero_basis_convex [h : locally_convex_space 𝕂 E] : 
  (𝓝 0 : filter E).has_basis (λ c : set E, c ∈ (𝓝 0 : filter E) ∧ convex 𝕂 c) id :=
⟨ λ t, 
  ⟨ λ ht, 
    let ⟨c, c_mem_nhds, c_sub_t, c_convex⟩ := locally_convex_space.exists_convex_nhds_zero 𝕂 E ht in 
    ⟨c, ⟨c_mem_nhds, c_convex⟩, c_sub_t⟩, 
    λ ⟨c, ⟨c_mem_nhds, _⟩, c_sub_t⟩, filter.mem_of_superset c_mem_nhds c_sub_t ⟩ ⟩

def locally_convex_space.nhds_basis_convex [h : locally_convex_space 𝕂 E] (x : E) : 
  (𝓝 x).has_basis (λ c : set E, c ∈ (𝓝 x) ∧ convex 𝕂 c) id :=
sorry

lemma locally_convex_space_of_convex_nhds_basis {ι : Type*} {b : ι → set E} {p : ι → Prop}
  (hbasis : (𝓝 0 : filter E).has_basis p b) (hconvex : ∀ i, p i → convex 𝕂 (b i)) :
  locally_convex_space 𝕂 E :=
⟨λ s hs, let ⟨i, h_pi, h_sub⟩ := hbasis.mem_iff.mp hs in 
  ⟨b i, hbasis.mem_of_mem h_pi, h_sub, hconvex i (h_pi)⟩⟩

end locally_convex_space

section lattice_ops

variables {ι 𝕂 E : Type*} [ordered_semiring 𝕂] [add_comm_monoid E] [module 𝕂 E] 
  [topological_space 𝕂] [topological_ring 𝕂]
  {t : topological_space E} [@has_continuous_add E t _] [@has_continuous_smul 𝕂 E _ _ t] 
  {ts : ι → topological_space E} [Π i, @has_continuous_add E (ts i) _] 
  [Π i, @has_continuous_smul 𝕂 E _ _ (ts i)] 

#check nhds_infi
#check has_basis_supr

--instance locally_convex_infi : @locally_convex_space 𝕂 E _ _ _ _ (⨅ i, ts i) _ _ _ :=
--@locally_convex_space_of_convex_nhds_basis 𝕂  E _ _ _ _ (⨅ i, ts i) _ _ _ (set E)

end lattice_ops