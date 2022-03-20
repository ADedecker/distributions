import spaces.cont_diff_map_support_in
import measure_theory.function.l1_space
import analysis.locally_convex.with_seminorms

open filter topological_space set measure_theory
open_locale topological_space filter pointwise bounded_cont_diff_map ennreal

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
{ carrier := {f | cont_diff 𝕜 n f ∧ f =ᶠ[cocompact_in Ω] 0}, -- TODO !!!!!!
  zero_mem' := ⟨cont_diff_zero_fun, by refl⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, 
    by filter_upwards [hf.2, hg.2] using λ x hfx hgx, 
      by rw [pi.add_apply, hfx, hgx, pi.zero_apply, add_zero]⟩,
  smul_mem' := λ c f hf, ⟨cont_diff_const.smul hf.1, 
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

lemma cont_diff (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  cont_diff 𝕜 n f :=
f.2.1

protected lemma continuous (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  continuous f :=
f.cont_diff.continuous

lemma eventually_eq_cocompact_in (f : Cc^n⟮Ω, E, F; 𝕜⟯) : 
  f =ᶠ[cocompact_in Ω] 0 :=
f.2.2

lemma eventually_eq_cocompact (f : Cc^n⟮Ω, E, F; 𝕜⟯) : 
  f =ᶠ[cocompact E] 0 :=
cocompact_le_cocompact_in Ω f.2.2

lemma has_compact_support (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  has_compact_support f :=
begin
  rw [has_compact_support_iff_eventually_eq, coclosed_compact_eq_cocompact],
  exact f.eventually_eq_cocompact
end

protected def tsupport (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  compacts E :=
⟨tsupport f, f.has_compact_support⟩

protected lemma tsupport_subset (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  ↑f.tsupport ⊆ Ω :=
begin
  sorry
end

variables (𝕜) (F) (n)

def of_support_in (K : compacts E) (hK : ↑K ⊆ Ω)
  (f : cont_diff_map_supported_in 𝕜 E F K n) : 
Cc^n⟮Ω, E, F; 𝕜⟯ :=
⟨f, f.cont_diff, (has_basis_cocompact_in Ω).mem_iff.mpr ⟨K, ⟨K.2, hK⟩, f.supported_in⟩⟩

def to_support_in {K : set E} (f : Cc^n⟮Ω, E, F; 𝕜⟯) (hK : ∀ x ∉ K, f x = 0) :
  cont_diff_map_supported_in 𝕜 E F K n :=
⟨f, f.cont_diff, hK⟩

def to_support_in_tsupport (f : Cc^n⟮Ω, E, F; 𝕜⟯) :
  cont_diff_map_supported_in 𝕜 E F f.tsupport n :=
⟨f, f.cont_diff, λ x, image_eq_zero_of_nmem_tsupport⟩

def of_support_inₗ (K : compacts E) (hK : ↑K ⊆ Ω) :
  cont_diff_map_supported_in 𝕜 E F K n 
    →ₗ[𝕜] Cc^n⟮Ω, E, F; 𝕜⟯ :=
{ to_fun := of_support_in 𝕜 F n K hK,
  map_add' := λ f g, by ext; refl,
  map_smul' := λ f g, by ext; refl }

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

private lemma tmp_topology_le_topology : 
  (𝓣₀ : topological_space (Cc^n⟮Ω, E, F; ℝ⟯)) ≤ 𝓣 := 
le_Inf (λ t ht, ht.1)

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

private lemma continuous_of_support_in {K : compacts E} {hK : ↑K ⊆ Ω} : 
  @continuous _ _ _ 𝓣 (of_support_in ℝ F n K hK) :=
@continuous.comp _ _ _ _ 𝓣₀ 𝓣 _ _ (continuous_id_of_le tmp_topology_le_topology) 
  (continuous_supr_rng $ continuous_supr_rng $ continuous_coinduced_rng)

attribute [instance] test_function.topology

instance : topological_add_group Cc^n⟮Ω, E, F; ℝ⟯ := 
topological_add_group_Inf (λ t ht, ht.2.1)

instance : has_continuous_smul ℝ Cc^n⟮Ω, E, F; ℝ⟯ := 
has_continuous_smul_Inf (λ t ht, ht.2.2.1)

instance : locally_convex_space ℝ Cc^n⟮Ω, E, F; ℝ⟯ := 
sorry

variables (F n)

noncomputable def of_support_inL (K : compacts E) (hK : ↑K ⊆ Ω) :
  cont_diff_map_supported_in ℝ E F K n →L[ℝ] Cc^n⟮Ω, E, F; ℝ⟯ :=
{ to_linear_map := of_support_inₗ ℝ F n K hK,
  cont := continuous_of_support_in } 

variables {F n}

lemma continuous_iff_of_linear {G : Type*} [tG : topological_space G] [add_comm_group G] [module ℝ G] 
  [topological_add_group G] [has_continuous_smul ℝ G] [locally_convex_space ℝ G] 
  (φ : Cc^n⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] G) : 
  continuous φ ↔ ∀ (K : compacts E) (hK : ↑K ⊆ Ω), continuous (φ ∘ₗ of_support_inₗ ℝ F n K hK) :=
begin
  let tC : Π (K : compacts E) (hK : ↑K ⊆ Ω), topological_space 
    (cont_diff_map_supported_in ℝ E F K n) :=
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

-- TODO : can we have different domains ?
lemma continuous_of_commutes_of_linear {F' : Type*} [normed_group F']
  [normed_space ℝ F'] (φ : Cc^n⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] Cc^n⟮Ω, E, F'; ℝ⟯) 
  (ψ : Π (K : compacts E) (hK : ↑K ⊆ Ω), 
    cont_diff_map_supported_in ℝ E F K n →L[ℝ] cont_diff_map_supported_in ℝ E F' K n)
  (hcomm : ∀ (K : compacts E) (hK : ↑K ⊆ Ω), 
    φ ∘ₗ of_support_inₗ ℝ F n K hK = of_support_inₗ ℝ F' n K hK ∘ₗ ↑(ψ K hK)) :
  continuous φ :=
begin
  rw continuous_iff_of_linear,
  intros K hK,
  rw hcomm K hK,
  exact ((of_support_inL F' n K hK).comp (ψ K hK)).continuous
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
  rw [cont_diff_map_supported_in.continuous_iff_of_linear, exists_congr],
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

noncomputable def to_bounded_cont_diff_map (f : Cc^n⟮Ω, E, F; ℝ⟯) : 
  B^n⟮E,F;ℝ⟯ :=
(f.to_support_in_tsupport ℝ F n).to_bounded_cont_diff_map

noncomputable def to_bounded_cont_diff_mapₗ : 
  Cc^n⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] B^n⟮E ,F ; ℝ⟯ := 
{ to_fun := to_bounded_cont_diff_map,
  map_add' := λ f g, by ext; refl,
  map_smul' := λ c f, by ext; refl }

noncomputable def to_bounded_cont_diff_mapL : 
  Cc^n⟮Ω, E, F; ℝ⟯ →L[ℝ] B^n⟮E ,F ; ℝ⟯ := 
{ to_linear_map := to_bounded_cont_diff_mapₗ,
  cont := 
  begin
    change continuous to_bounded_cont_diff_mapₗ,
    rw continuous_iff_of_linear,
    intros K hK,
    exact cont_diff_map_supported_in.to_bounded_cont_diff_mapL.continuous
  end }

lemma mem_ℒp (f : Cc^n⟮Ω, E, F; ℝ⟯) 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : mem_ℒp f p μ :=
f.continuous.mem_ℒp_of_has_compact_support f.has_compact_support p μ

lemma integrable (f : Cc^n⟮Ω, E, F; ℝ⟯) 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (μ : measure E)
  [is_finite_measure_on_compacts μ] : integrable f μ :=
mem_ℒp_one_iff_integrable.mp (f.mem_ℒp 1 μ)

variable (n)

noncomputable def to_Lpₗ
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : 
  (Cc^n⟮Ω, E, F; ℝ⟯) →ₗ[ℝ] (Lp F p μ) :=
{ to_fun := λ f, (f.mem_ℒp p μ).to_Lp f,
  map_add' := λ f g, (f.mem_ℒp p μ).to_Lp_add (g.mem_ℒp p μ),
  map_smul' := λ c f, (f.mem_ℒp p μ).to_Lp_const_smul c }  

noncomputable def to_Lp
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : 
  (Cc^n⟮Ω, E, F; ℝ⟯) →L[ℝ] (Lp F p μ) :=
{ to_linear_map := to_Lpₗ n p μ,
  cont := 
  begin
    change continuous (to_Lpₗ n p μ),
    rw continuous_iff_of_linear,
    intros K hK,
    exact (cont_diff_map_supported_in.to_Lp n p μ).continuous,
  end } 

variable {n}

section infinity

lemma differentiable (f : Cc^⊤⟮Ω, E, F; ℝ⟯) : differentiable ℝ f := 
f.cont_diff.differentiable le_top

protected noncomputable def fderiv (f : Cc^⊤⟮Ω, E, F; ℝ⟯) : Cc^⊤⟮Ω, E, E →L[ℝ] F; ℝ⟯ := 
of_support_in ℝ (E →L[ℝ] F) ⊤ f.tsupport f.tsupport_subset (f.to_support_in_tsupport ℝ F ⊤).fderiv

@[simp] lemma fderiv_apply (f : Cc^⊤⟮Ω, E, F; ℝ⟯) (x : E) : f.fderiv x = fderiv ℝ f x := rfl

protected noncomputable def fderivₗ : Cc^⊤⟮Ω, E, F; ℝ⟯ →ₗ[ℝ] Cc^⊤⟮Ω, E, E →L[ℝ] F; ℝ⟯ := 
{ to_fun := test_function.fderiv,
  map_add' := λ f g,
  begin
    ext x : 1,
    exact fderiv_add f.differentiable.differentiable_at
      g.differentiable.differentiable_at,
  end,
  map_smul' := λ a f,
  begin
    ext x : 1,
    exact fderiv_const_smul f.differentiable.differentiable_at _
  end }

protected noncomputable def fderivL : Cc^⊤⟮Ω, E, F; ℝ⟯ →L[ℝ] Cc^⊤⟮Ω, E, E →L[ℝ] F; ℝ⟯ := 
{ to_linear_map := test_function.fderivₗ,
  cont := 
  begin
    change continuous test_function.fderivₗ,
    exact continuous_of_commutes_of_linear _ 
      (λ K hK, cont_diff_map_supported_in.fderivL) (λ K hK, rfl)
  end }

end infinity

end real

end test_function