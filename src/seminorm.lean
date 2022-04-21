import analysis.locally_convex.with_seminorms

open topological_space set filter function nnreal

open_locale topological_space nnreal

section any_field

variables {ι 𝕜 E F : Type*} [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space F] [topological_add_group F]

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

def seminorm_family.comp (q : seminorm_family 𝕜 F ι) (f : E →ₗ[𝕜] F) : 
  seminorm_family 𝕜 E ι :=
λ i, (q i).comp f

def seminorm_family.comp_apply (q : seminorm_family 𝕜 F ι) (i : ι) (f : E →ₗ[𝕜] F) : 
  q.comp f i = (q i).comp f :=
rfl

lemma seminorm.sup_comp (p q : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : 
  (p ⊔ q).comp f = p.comp f ⊔ q.comp f := rfl

lemma seminorm_family.finset_sup_comp (q : seminorm_family 𝕜 F ι) (s : finset ι) 
  (f : E →ₗ[𝕜] F) : (s.sup q).comp f = s.sup (q.comp f) := 
begin
  ext x,
  rw [seminorm.comp_apply, seminorm.finset_sup_apply, seminorm.finset_sup_apply],
  refl
end

-- Is it worth keeping ?
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

lemma linear_map.with_seminorms_induced [hι : nonempty ι] {q : seminorm_family 𝕜 F ι} [hq : with_seminorms q] 
  (f : E →ₗ[𝕜] F) : @with_seminorms 𝕜 E ι _ _ _ _ (q.comp f) (induced f infer_instance) := 
begin
  letI : topological_space E := induced f infer_instance,
  letI : topological_add_group E := topological_add_group_induced f,
  rw [(q.comp f).with_seminorms_iff_nhds_eq_infi, nhds_induced, map_zero,
      q.with_seminorms_iff_nhds_eq_infi.mp hq, comap_infi],
  refine infi_congr (λ i, _),
  exact comap_comap
end

lemma seminorm_family.with_seminorms_congr {ι' : Type*} [nonempty ι] [nonempty ι']
  (p : seminorm_family 𝕜 F ι) {f : ι' → ι} (hf : surjective f) [hp : with_seminorms p] :
  with_seminorms (p ∘ f) :=
begin
  rw seminorm_family.with_seminorms_iff_nhds_eq_infi at ⊢ hp,
  rw [hp, infi, infi, ← hf.range_comp]
end

def seminorm_family.Union {ι' : ι → Type*} (Q : Π i, seminorm_family 𝕜 E (ι' i)) :
  seminorm_family 𝕜 E (Σ i, ι' i) := λ ⟨i, i'⟩, Q i i'

lemma with_seminorms_infi {ι' : ι → Type*} [hι : nonempty ι] [hι' : ∀ i, nonempty (ι' i)] 
  {Q : Π i, seminorm_family 𝕜 E (ι' i)} 
  {T : ι → topological_space E} (H : ∀ i, @with_seminorms 𝕜 E (ι' i) _ _ _ _ (Q i) (T i))
  (H' : ∀ i, @topological_add_group E (T i) _) :
  @with_seminorms 𝕜 E (Σ i, ι' i) _ _ _ (hι.cases_on $ λ i, nonempty_sigma.mpr ⟨i, hι' i⟩) 
  (seminorm_family.Union Q) (⨅ i, T i) :=
begin
  simp [seminorm_family.with_seminorms_iff_nhds_eq_infi] at H,
  letI : nonempty (Σ i, ι' i) := (hι.cases_on $ λ i, nonempty_sigma.mpr ⟨i, hι' i⟩),
  letI : topological_space E := ⨅ i, T i,
  letI : topological_add_group E := topological_add_group_infi H',
  rw [(seminorm_family.Union Q).with_seminorms_iff_nhds_eq_infi, nhds_infi, infi_sigma],
  refine infi_congr (λ i, _),
  rw [H i],
  exact infi_congr (λ hi, rfl)
end

lemma seminorm.nhds_0_comap_sup (p q : seminorm 𝕜 E) : 
  (𝓝 0).comap (p ⊔ q : seminorm 𝕜 E) = (𝓝 0).comap p ⊓ (𝓝 0).comap q :=
begin
  rw (metric.nhds_basis_ball.comap (_)).ext ((metric.nhds_basis_ball.comap p).inf (metric.nhds_basis_ball.comap q)),
  { refine λ ε hε, ⟨⟨ε, ε⟩, ⟨hε, hε⟩, _⟩,
    dsimp only,
    rw [← p.ball_eq_preimage_ball hε, ← q.ball_eq_preimage_ball hε, ← seminorm.ball_sup,
        (p ⊔ q).ball_eq_preimage_ball hε] },
  { rintros ⟨ε₁, ε₂⟩ ⟨hε₁, hε₂⟩,
    have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂,
    refine ⟨min ε₁ ε₂, hε, _⟩,
    dsimp only,
    rw [← (p ⊔ q).ball_eq_preimage_ball hε, seminorm.ball_sup, p.ball_eq_preimage_ball hε,
        q.ball_eq_preimage_ball hε],
    exact inter_subset_inter 
      (preimage_mono $ metric.ball_subset_ball $ min_le_left _ _) 
      (preimage_mono $ metric.ball_subset_ball $ min_le_right _ _) }
end

lemma comap_const_of_mem' {α β : Type*} {x : α} {f : filter α} (h : ∀ V ∈ f, x ∈ V) : comap (λ y : β, x) f = ⊤ :=
begin
  ext W,
  suffices : (∃ (t : set α), t ∈ f ∧ (λ (y : β), x) ⁻¹' t ⊆ W) ↔ W = univ,
  by simpa,
  split,
  { rintro ⟨V, V_in, hW⟩,
    simpa [preimage_const_of_mem (h V V_in),  univ_subset_iff] using hW },
  { rintro rfl,
    use univ,
    simp [univ_mem] },
end

lemma seminorm_family.nhds_0_comap_finset_sup (p : seminorm_family 𝕜 E ι) (s : finset ι) :
  (𝓝 0).comap (s.sup p : seminorm 𝕜 E) = s.inf (λ i, (𝓝 0).comap (p i)) :=
begin
  classical,
  refine s.induction_on _ _,
  { rw [finset.sup_empty, finset.inf_empty, seminorm.bot_eq_zero, seminorm.coe_zero,
        pi.zero_def, comap_const_of_mem'],
    exact λ V, mem_of_mem_nhds },
  { intros i t hit h,
    rw [finset.sup_insert, finset.inf_insert, seminorm.nhds_0_comap_sup, h] }
end

lemma seminorm.is_bounded_iff_of_directed_dom [nonempty ι] {ι' : Type*}
  (p : seminorm_family 𝕜 E ι) (q : seminorm_family 𝕜 F ι') (f : E →ₗ[𝕜] F) 
  (h : directed (≤) p) : 
  seminorm.is_bounded p q f ↔ ∀ j, ∃ i : ι, ∃ C : ℝ≥0, C ≠ 0 ∧ (q j).comp f ≤ C • (p i) :=
begin
  rw [seminorm.is_bounded, forall_congr],
  intros j,
  split,
  { rintros ⟨s, C, hC, hle⟩,
    rcases h.finset_le s with ⟨i, hi⟩,
    rw ← finset.sup_le_iff at hi,
    exact ⟨i, C, hC, hle.trans (seminorm.smul_le_smul hi le_rfl)⟩ },
  { rintros ⟨i, C, hC, hle⟩,
    refine ⟨{i}, C, hC, _⟩,
    rwa finset.sup_singleton }
end

lemma seminorm.finset_sup_apply' (p : ι → seminorm 𝕜 F) {s : finset ι} (hs : s.nonempty) (x : F) :
  s.sup p x = s.sup' hs (λ i, p i x) :=
begin
  refine finset.nonempty.cons_induction _ _ hs,
  { intros i,
    rw [finset.sup_singleton, finset.sup'_singleton] },
  { intros i s his hs ih,
    rw [finset.sup_cons, finset.sup'_cons hs, seminorm.sup_apply, ih] }
end

--section unique
--
--variables [unique ι] [t : topological_space E] (p : seminorm_family 𝕜 E ι) [with_seminorms p]
--
--def with_seminorms.to_pseudo_metric_space : has_dist E :=
--{  }
--
--def with_seminorms.to_semi_normed_group : semi_normed_group E :=
--{  }
--
--def with_seminorms.to_normed_space_of_singleton_of_t2 [t : topological_space E] 
--
--end unique

--lemma with_seminorms_sup_of_fintype [fintype ι] [hι : nonempty ι] 
--  {p : seminorm_family 𝕜 F ι} [with_seminorms p] : 
--  with_seminorms (λ u : unit, finset.univ.sup p) :=
--begin
--  sorry
--end

end any_field

--lemma finset.with_seminorms_inf {q : seminorm}