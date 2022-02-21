import spaces.times_cont_diff_map_support_in
import ..tsupport

open filter topological_space set
open_locale topological_space filter pointwise

section prelim

variables {α : Type*} (S : set α) [topological_space α]

def cocompact_in : filter α :=
⨅ (s : set S) (h : is_compact s), 𝓟 (coe '' s : set α)ᶜ

lemma has_basis_cocompact_in' : (cocompact_in S).has_basis (is_compact : set S → Prop) 
  (compl ∘ image coe) :=
has_basis_binfi_principal'
  (λ s hs t ht, ⟨s ∪ t, hs.union ht, compl_subset_compl.2 
    (image_subset _ $ subset_union_left s t),
    compl_subset_compl.2 (image_subset _ $ subset_union_right s t)⟩)
  ⟨∅, is_compact_empty⟩

lemma has_basis_cocompact_in : (cocompact_in S).has_basis (λ K : set α, is_compact K ∧ K ⊆ S) 
  compl :=
sorry

lemma cocompact_le_cocompact_in : cocompact α ≤ cocompact_in S :=
λ s hs, let ⟨t, ht, hts⟩ := (has_basis_cocompact_in' S).mem_iff.mp hs in 
  mem_cocompact.mpr ⟨coe '' t, ht.image continuous_subtype_coe, hts⟩

end prelim

private def test_function_submodule (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (Ω : set E) 
  (n : with_top ℕ) : submodule 𝕜 (E → F) :=
{ carrier := {f | times_cont_diff 𝕜 n f ∧ f =ᶠ[cocompact_in Ω] 0}, -- TODO !!!!!!
  zero_mem' := ⟨times_cont_diff_zero_fun, by refl⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, 
    by filter_upwards [hf.2, hg.2] using λ x hfx hgx, 
      by rw [pi.add_apply, hfx, hgx, pi.zero_apply, add_zero]⟩,
  smul_mem' := λ c f hf, ⟨times_cont_diff_const.smul hf.1, 
    by filter_upwards [hf.2] using λ x hfx, 
      by rw [pi.smul_apply, hfx, pi.zero_apply, smul_zero]⟩ }

def test_function (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] [normed_group E] 
  [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (Ω : set E) (n : with_top ℕ) :=
↥(test_function_submodule 𝕜 E F Ω n)

localized "notation `Cc^`n`⟮`Ω`,`E`,`F`;`𝕜`⟯` := test_function 𝕜 E F Ω n" in 
  test_function

namespace test_function

section general

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {Ω : set E} {n : with_top ℕ} 
  {f g : Cc^n⟮Ω, E, F; 𝕜⟯} {x : E}

instance : add_comm_group (Cc^n⟮Ω, E, F; 𝕜⟯) := submodule.add_comm_group _
instance : module 𝕜 (Cc^n⟮Ω, E, F; 𝕜⟯) := submodule.module _

instance : has_coe_to_fun (Cc^n⟮Ω, E, F; 𝕜⟯) (λ _, E → F) := ⟨λ f, f.1⟩

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
by {ext, exact H x}

lemma times_cont_diff (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  times_cont_diff 𝕜 n f :=
f.2.1

lemma eventually_eq_cocompact_in (f : Cc^n⟮Ω, E, F; 𝕜⟯) : 
  f =ᶠ[cocompact_in Ω] 0 :=
f.2.2

lemma eventually_eq_cocompact (f : Cc^n⟮Ω, E, F; 𝕜⟯) : 
  f =ᶠ[cocompact E] 0 :=
cocompact_le_cocompact_in Ω f.2.2

variables (𝕜) (F) (n)

def of_support_in (K : compacts E) (hK : ↑K ⊆ Ω)
  (f : times_cont_diff_map_supported_in 𝕜 E F K n) : 
Cc^n⟮Ω, E, F; 𝕜⟯ :=
⟨f, f.times_cont_diff, (has_basis_cocompact_in Ω).mem_iff.mpr ⟨K, ⟨K.2, hK⟩, f.supported_in⟩⟩

def to_support_in {K : set E} (f : Cc^n⟮Ω, E, F; 𝕜⟯) (hK : ∀ x ∉ K, f x = 0) :
  times_cont_diff_map_supported_in 𝕜 E F K n :=
⟨f, f.times_cont_diff, hK⟩

def of_support_inₗ (K : compacts E) (hK : ↑K ⊆ Ω) :
  times_cont_diff_map_supported_in 𝕜 E F K n 
    →ₗ[𝕜] Cc^n⟮Ω, E, F; 𝕜⟯ :=
{ to_fun := of_support_in 𝕜 F n K hK,
  map_add' := sorry,
  map_smul' := sorry }

end general

section real

variables {E F : Type*} [normed_group E] [normed_group F]
  [normed_space ℝ E] [normed_space ℝ F] {n : with_top ℕ} {Ω : set E}
  {f g : Cc^n⟮Ω, E, F; ℝ⟯} {x : E}

private noncomputable def tmp_topology : topological_space (Cc^n⟮Ω, E, F; ℝ⟯) := 
  ⨆ (K : compacts E) (hK : ↑K ⊆ Ω), coinduced (of_support_inₗ ℝ F n K hK) infer_instance

local notation `𝓣₀` := tmp_topology

protected def topology : topological_space (Cc^n⟮Ω, E, F; ℝ⟯) := 
Inf { t | 𝓣₀ ≤ t ∧ @topological_add_group _ t _ ∧ @has_continuous_smul ℝ _ _ _ t ∧ 
          @locally_convex_space ℝ _ _ _ _ t }

local notation `𝓣` := test_function.topology

private lemma topology_le_iff {t : topological_space (Cc^n⟮Ω, E, F; ℝ⟯)} 
  (h₁ : @topological_add_group _ t _) (h₂ : @has_continuous_smul ℝ _ _ _ t) 
  (h₃ : @locally_convex_space ℝ _ _ _ _ t) :
𝓣 ≤ t ↔ 𝓣₀ ≤ t :=
sorry -- consequence of general lemma

private def basis_zero : filter_basis Cc^n⟮Ω, E, F; ℝ⟯ :=
{ sets := { s | s ∈ (⨆ (K : compacts E) (hK : ↑K ⊆ Ω), (𝓝 0).map (of_support_in ℝ F n K hK)) ∧ 
                convex ℝ s ∧ absorbent ℝ s ∧ s = -s },
  nonempty := ⟨univ, univ_mem, convex_univ, absorbent_univ, neg_univ.symm⟩,
  inter_sets := λ s t hs ht, ⟨s ∩ t, ⟨inter_mem hs.1 ht.1, hs.2.1.inter ht.2.1, 
    sorry /- absorbent_inter doesn't exist -/, by rw [inter_neg, ← hs.2.2.2, ← ht.2.2.2]⟩, subset_refl _⟩ }

private noncomputable def add_group_basis_zero : add_group_filter_basis Cc^n⟮Ω, E, F; ℝ⟯ := 
{ zero' := sorry,
  add' := sorry,
  neg' := sorry,
  conj' := sorry,
  ..basis_zero }

private noncomputable def module_basis_zero : module_filter_basis ℝ Cc^n⟮Ω, E, F; ℝ⟯ :=
{ smul' := sorry,
  smul_left' := sorry,
  smul_right' := sorry,
  ..add_group_basis_zero }

private noncomputable def basis_topology : topological_space (Cc^n⟮Ω, E, F; ℝ⟯) := 
module_basis_zero.topology

local notation `𝓣₁` := basis_topology

private lemma topology_eq_basis_topology : (𝓣 : topological_space Cc^n⟮Ω, E, F; ℝ⟯) = 𝓣₁ :=
sorry

attribute [instance] test_function.topology

lemma continuous_iff_of_linear {G : Type*} [tG : topological_space G] [add_comm_group G] [module ℝ G] 
  [topological_add_group G] [has_continuous_smul ℝ G] [locally_convex_space ℝ G] 
  (φ : Cc^n⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] G) : 
  continuous φ ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), continuous (φ ∘ₗ of_support_inₗ ℝ F n K hK) :=
begin
  let tC : Π (K : compacts E) (hK : ↑K ⊆ Ω), topological_space 
    (times_cont_diff_map_supported_in ℝ E F K n) :=
    infer_instance,
  calc  continuous φ 
      ↔ 𝓣 ≤ tG.induced φ : continuous_iff_le_induced
  ... ↔ 𝓣₀ ≤ tG.induced φ : 
          topology_le_iff (topological_add_group_induced _) (has_continuous_smul_induced _) sorry
  ... ↔ ∀ (K : compacts E), (⨆ (hK : ↑K ⊆ Ω), coinduced (of_support_inₗ ℝ F n K hK) _) 
          ≤ tG.induced φ : supr_le_iff
  ... ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), coinduced (of_support_inₗ ℝ F n K hK) _ ≤ tG.induced φ : 
          forall_congr (λ K, supr_le_iff)
  ... ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), _ ≤ (tG.induced φ).induced (of_support_inₗ ℝ F n K hK) : 
          forall_congr (λ K, forall_congr $ λ hK, coinduced_le_iff_le_induced)
  ... ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), _ ≤ tG.induced (φ ∘ₗ of_support_inₗ ℝ F n K hK) : 
          forall_congr (λ K, forall_congr $ λ hK, by rw [linear_map.coe_comp, induced_compose])
  ... ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), continuous (φ ∘ₗ of_support_inₗ ℝ F n K hK) : 
          forall_congr (λ K, forall_congr $ λ hK, continuous_iff_le_induced.symm),
end

lemma continuous_iff_of_linear_of_normed_codomain' {G : Type*} [normed_group G] 
  [normed_space ℝ G] (T : Cc^n⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] G) : 
  continuous T ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), ∃ (p : ℕ), ∃ C > 0, ∀ f, 
    ∥T (of_support_in ℝ F n K hK f)∥ ≤ 
      C * (⨆ (i ≤ p) (hin : ↑i ≤ n) (x : E), ∥iterated_fderiv ℝ i f x∥) :=
begin
  rw [continuous_iff_of_linear, forall_congr],
  intros K,
  rw forall_congr,
  intros hK,
  rw [times_cont_diff_map_supported_in.continuous_iff_of_linear, exists_congr],
  intros p,
  refl
end

lemma continuous_iff_of_linear_of_normed_codomain {G : Type*} [normed_group G] 
  [normed_space ℝ G] (T : Cc^n⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] G) : 
  continuous T ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), ∃ (p : ℕ), ∃ C > (0 : ℝ), ∀ f : Cc^n⟮Ω, E, F; ℝ⟯, 
    (∀ x ∉ K, f x = 0) → ∥T f∥ ≤ 
      C * (⨆ (i ≤ p) (hin : ↑i ≤ n) (x : E), ∥iterated_fderiv ℝ i f x∥) :=
begin
  rw [continuous_iff_of_linear_of_normed_codomain', forall_congr],
  intros K,
  rw [forall_congr],
  intros hK,
  rw [exists_congr],
  intros p,
  rw [exists_congr],
  intros C,
  rw [exists_congr],
  intros hC,
  split; intros H f,
  { intro hf,
    convert H (to_support_in ℝ F n f hf),
    ext,
    refl },
  { exact H (of_support_in ℝ F n K hK f) (λ x hx, f.supported_in x hx) }
end

-- TODO : formulate this in term of bounded subsets

end real

end test_function