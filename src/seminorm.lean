import analysis.locally_convex.with_seminorms

open topological_space set filter

open_locale topological_space

section any_field

variables {ι 𝕜 E F : Type*} [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space F] [topological_add_group F]

def seminorm_family.comp (q : seminorm_family 𝕜 F ι) (f : E →ₗ[𝕜] F) : 
  seminorm_family 𝕜 E ι :=
λ i, (q i).comp f

lemma seminorm.sup_comp (p q : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : 
  (p ⊔ q).comp f = p.comp f ⊔ q.comp f := rfl

lemma seminorm_family.finset_sup_comp (q : seminorm_family 𝕜 F ι) (s : finset ι) 
  (f : E →ₗ[𝕜] F) : (s.sup q).comp f = s.sup (q.comp f) := 
begin
  ext x,
  rw [seminorm.comp_apply, seminorm.finset_sup_apply, seminorm.finset_sup_apply],
  refl
end

lemma seminorm_family.basis_sets_comp (q : seminorm_family 𝕜 F ι) (f : E →ₗ[𝕜] F) :
  (q.comp f).basis_sets = preimage f '' q.basis_sets :=
begin
  rw [seminorm_family.basis_sets, seminorm_family.basis_sets, image_Union₂],
  refine Union_congr (λ s, Union_congr $ λ r, _),
  rw image_Union,
  refine Union_congr (λ hr, _),
  rw [image_singleton, singleton_eq_singleton_iff, ← q.finset_sup_comp, 
      seminorm.ball_comp, map_zero],
end

lemma linear_map.with_seminorms_induced [hι : nonempty ι] {q : seminorm_family 𝕜 F ι} [with_seminorms q] 
  (f : E →ₗ[𝕜] F) : @with_seminorms 𝕜 E ι _ _ _ _ (q.comp f) (induced f infer_instance) := 
begin
  letI : topological_space E := induced f infer_instance,
  letI : topological_add_group E := topological_add_group_induced f,
  refine (q.comp f).with_seminorms_of_has_basis _,
  simp_rw [nhds_induced, map_zero, q.basis_sets_comp],
  exact (q.has_basis.comap f).to_has_basis 
    (λ U hU, ⟨f ⁻¹' U, mem_image_of_mem _ hU, subset_rfl⟩) 
    (λ V ⟨U, hU, hUV⟩, ⟨U, hU, hUV ▸ subset_rfl⟩)
end

lemma seminorm.ball_eq_preimage_ball (p : seminorm 𝕜 E) {r : ℝ} (hr : 0 < r) : 
  p.ball 0 r = p ⁻¹' (metric.ball 0 r) :=
begin
  ext x,
  change (_ < _) ↔ (_ < _),
  rw [sub_zero, dist_zero_right, real.norm_of_nonneg (p.nonneg x)]
end

lemma seminorm_family.filter_eq_infi [nonempty ι] (p : seminorm_family 𝕜 E ι) : 
  p.module_filter_basis.to_filter_basis.filter = ⨅ i, (𝓝 0).comap (p i) := 
begin
  refine le_antisymm (le_infi $ λ i, _) _,
  { rw p.module_filter_basis.to_filter_basis.has_basis.le_basis_iff (metric.nhds_basis_ball.comap _),
    intros ε hε,
    refine ⟨(p i).ball 0 ε, _, _⟩,
    { convert p.basis_sets_mem {i} hε,
      rw finset.sup_singleton },
    { rw [id, (p i).ball_eq_preimage_ball hε] } },
  { rw p.module_filter_basis.to_filter_basis.has_basis.ge_iff,
    rintros U (hU : U ∈ p.basis_sets),
    rw p.basis_sets_iff at hU,
    rcases hU with ⟨s, r, hr, rfl⟩,
    rw [id, seminorm.ball_finset_sup_eq_Inter _ _ _ hr, s.Inter_mem_sets],
    intros i hi,
    refine mem_infi_of_mem i ⟨metric.ball 0 r, metric.ball_mem_nhds 0 hr, _⟩,
    rw [(p i).ball_eq_preimage_ball hr] }
end

lemma seminorm_family.with_seminorms_iff_nhds_eq_infi [topological_space E] 
  [topological_add_group E] [nonempty ι] (p : seminorm_family 𝕜 E ι) :
  with_seminorms p ↔ (𝓝 0 : filter E) = ⨅ i, (𝓝 0).comap (p i) :=
begin
  rw ← p.filter_eq_infi,
  split,
  { intro h, 
    rw h.topology_eq_with_seminorms,
    exact add_group_filter_basis.nhds_zero_eq _ },
  { exact p.with_seminorms_of_nhds }
end

--#check seminorm_family.has_basis
--#check filter.mem_infi

def seminorm_family.Union {ι' : ι → Type*} (Q : Π i, seminorm_family 𝕜 E (ι' i)) :
  seminorm_family 𝕜 E (Σ i, ι' i) := λ ⟨i, i'⟩, Q i i'

--#check finset.sigma_image_fst_preimage_mk
--#check mem_Union₂_of_mem
--#check finite.to_finset.nonempty
--#check finset.lt_inf'_iff

--lemma seminorm_family.mem_basis_sets_Union_iff {ι' : ι → Type*} (Q : Π i, seminorm_family 𝕜 E (ι' i)) (U : set E) :
--  U ∈ (seminorm_family.Union Q).basis_sets ↔ ∃ (I : set ι) (hI : I.finite) (V : ι → set E),
--    (∀ i ∈ I, V i ∈ (Q i).basis_sets) ∧ (⋂ i ∈ I, V i) ⊆ U :=
--begin
--  classical,
--  split,
--  { rw [seminorm_family.basis_sets, mem_Union₂],
--    rintros ⟨s, r, hU⟩,
--    rw [mem_Union] at hU,
--    rcases hU with ⟨hr, rfl : _ = _⟩,
--    let s₁ := s.image sigma.fst,
--    let s₂ := λ i, s.preimage (sigma.mk i) (sigma_mk_injective.inj_on _),
--    have : s = s₁.sigma s₂ := s.sigma_image_fst_preimage_mk.symm,
--    refine ⟨s₁, finset.finite_to_set _, (λ i, ((s₂ i).sup (Q i)).ball (0 : E) r), 
--            (λ i hi, mem_Union_of_mem (s₂ i) $ mem_Union₂_of_mem hr rfl), _⟩,
--    rw [this, finset.sup_sigma, seminorm.ball_finset_sup_eq_Inter _ _ _ hr],
--    exact subset_rfl },
--  { rintros ⟨I, hI, V, hV, hU⟩,
--    by_cases h : I.nonempty,
--    { simp_rw [seminorm_family.basis_sets, mem_Union₂] at ⊢ hV,
--      choose! s₂ hs₂ using hV,
--      choose! R hR using hs₂,
--      let s₁ : finset ι := hI.to_finset,
--      have : s₁.nonempty := (finite.to_finset.nonempty hI).mpr h,
--      let r := s₁.inf' this R,
--      refine ⟨s₁.sigma s₂, r, _⟩,
--      simp_rw [mem_Union] at ⊢ hR,
--      choose hR hV using hR,
--      change ∀ i ∈ I, _ = _ at hV,
--      refine ⟨(finset.lt_inf'_iff this R).mpr (λ i hi, hR i (hI.mem_to_finset.mp hi)), (_ : _ = _)⟩,
--      rw [finset.sup_sigma, seminorm.ball_finset_sup_eq_Inter],
--      refine Inter_congr (λ i, _),
--      rw hI.mem_to_finset,
--      refine Inter_congr (λ hi, _),
--      exact hV i hi },
--    sorry }
--end

--lemma with_seminorms_infi {ι' : ι → Type*} [hι' : ∀ i, nonempty (ι' i)] {Q : Π i, seminorm_family 𝕜 E (ι' i)} 
--  {T : ι → topological_space E} (H : ∀ i, @with_seminorms 𝕜 E (ι' i) _ _ _ _ (Q i) (T i))
--  (H' : ∀ i, @topological_add_group E (T i) _) :
--  @with_seminorms 𝕜 E (Σ i, ι' i) _ _ _ (hι.cases_on $ λ i, nonempty_sigma.mpr ⟨i, hι' i⟩) 
--  (seminorm_family.Union Q) (⨅ i, T i) :=
--begin
--  letI : nonempty (Σ i, ι' i) := (hι.cases_on $ λ i, nonempty_sigma.mpr ⟨i, hι' i⟩),
--  letI : topological_space E := ⨅ i, T i,
--  letI : topological_add_group E := topological_add_group_infi H',
--  refine seminorm_family.with_seminorms_of_has_basis _ _,
--  simp_rw [nhds_infi, seminorm_family.mem_basis_sets_Union_iff],
--  refine (has_basis_infi (λ i, @seminorm_family.has_basis 𝕜 E (ι' i) _ _ _ _ (T i) (Q i) (H i))).to_has_basis 
--    (λ ⟨I, V⟩ ⟨hI, hV⟩, _) _,
--  --dsimp at this,
--end

end any_field

section real

variables {ι E F : Type*} [hι : nonempty ι] [add_comm_group E] [module ℝ E]
  [add_comm_group F] [module ℝ F] [topological_space F] [topological_add_group F]

lemma with_seminorms_infi {ι' : ι → Type*} [hι' : ∀ i, nonempty (ι' i)] {Q : Π i, seminorm_family ℝ E (ι' i)} 
  {T : ι → topological_space E} (H : ∀ i, @with_seminorms ℝ E (ι' i) _ _ _ _ (Q i) (T i))
  (H' : ∀ i, @topological_add_group E (T i) _) :
  @with_seminorms ℝ E (Σ i, ι' i) _ _ _ (hι.cases_on $ λ i, nonempty_sigma.mpr ⟨i, hι' i⟩) 
  (seminorm_family.Union Q) (⨅ i, T i) :=
begin
  letI : nonempty (Σ i, ι' i) := (hι.cases_on $ λ i, nonempty_sigma.mpr ⟨i, hι' i⟩),
  letI t : topological_space E := ⨅ i, T i,
  letI : topological_add_group E := topological_add_group_infi H',
  letI : locally_convex_space ℝ E := sorry,
  let ι'' : Type := sorry,
  let p : seminorm_family ℝ E ι'' := sorry,
  letI : nonempty ι'' := sorry,
  letI H : with_seminorms p := sorry, -- All those sorries are true 
  refine ⟨(_ : t = _)⟩,
  rw H.topology_eq_with_seminorms,
  refine seminorm_family.with_seminorms_of_has_basis _ _,
  simp_rw [nhds_infi, seminorm_family.mem_basis_sets_Union_iff],
  refine (has_basis_infi (λ i, @seminorm_family.has_basis 𝕜 E (ι' i) _ _ _ _ (T i) (Q i) (H i))).to_has_basis 
    (λ ⟨I, V⟩ ⟨hI, hV⟩, _) _,
  --dsimp at this,
end

end real

--lemma finset.with_seminorms_inf {q : seminorm}