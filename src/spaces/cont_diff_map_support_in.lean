import spaces.bounded_cont_diff_map
import analysis.normed.group.basic
import measure_theory.function.lp_space

open topological_space function measure_theory set filter
open_locale bounded_cont_diff_map topological_space ennreal bounded_continuous_function

section prelim

theorem continuous_multilinear_map.ext_iff {ι 𝕜 F : Type*} {E : ι → Type*} [decidable_eq ι] [nondiscrete_normed_field 𝕜] 
  [Π i, normed_group (E i)] [normed_group F] [Π i, normed_space 𝕜 (E i)] [normed_space 𝕜 F] 
  {f g : continuous_multilinear_map 𝕜 E F} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, continuous_multilinear_map.ext⟩

lemma has_fderiv_at.tsupport_subset {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {f : E → F} {f' : E → E →L[𝕜] F} (hf : ∀ x, has_fderiv_at f (f' x) x) :
  tsupport f' ⊆ tsupport f :=
begin
  intros x,
  contrapose,
  rw [not_mem_closure_support_iff_eventually_eq, not_mem_closure_support_iff_eventually_eq],
  intros h,
  filter_upwards [h.eventually_eq_nhds],
  intros y hy,
  exact has_fderiv_at.unique (hf y) ((has_fderiv_at_const 0 y).congr_of_eventually_eq hy)
end

lemma fderiv_tsupport_subset {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {f : E → F} (hf : differentiable 𝕜 f) :
  tsupport (fderiv 𝕜 f) ⊆ tsupport f :=
has_fderiv_at.tsupport_subset (λ x, (hf x).has_fderiv_at)

lemma iterated_fderiv_tsupport_subset {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf : with_top ℕ} {i : ℕ} {f : E → F} (hf : cont_diff 𝕜 nf f)
  (hif : (i : with_top ℕ) ≤ nf) :
  tsupport (iterated_fderiv 𝕜 i f) ⊆ tsupport f :=
begin
  induction i with i hi,
  { refine subset_of_eq (congr_arg closure _),
    ext x,
    refine not_iff_not_of_iff _,
    simp only [continuous_multilinear_map.ext_iff, iterated_fderiv_zero_apply, 
                continuous_multilinear_map.zero_apply, forall_const], },
  { have hif' : (i : with_top ℕ) < nf := 
      lt_of_lt_of_le (with_top.coe_lt_coe.mpr $ i.lt_succ_self) hif,
    have hdf : differentiable 𝕜 (iterated_fderiv 𝕜 i f) :=
      (cont_diff_iff_continuous_differentiable.mp hf).2 i hif',
    calc tsupport (iterated_fderiv 𝕜 (i+1) f)
        = tsupport (fderiv 𝕜 $ iterated_fderiv 𝕜 i f) : by
          { refine congr_arg closure _,
            ext x,
            refine not_iff_not_of_iff _,
            rw [iterated_fderiv_succ_eq_comp_left, comp_apply, 
                (continuous_multilinear_curry_left_equiv _ _ _).map_eq_zero_iff] }
    ... ⊆ tsupport (iterated_fderiv 𝕜 i f) : fderiv_tsupport_subset hdf
    ... ⊆ tsupport f : hi hif'.le }
end

lemma has_compact_support_iterated_fderiv {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf : with_top ℕ} {i : ℕ} {f : E → F} (hf : cont_diff 𝕜 nf f) (hsupp : has_compact_support f)
  (hif : (i : with_top ℕ) ≤ nf) : has_compact_support (iterated_fderiv 𝕜 i f) :=
compact_of_is_closed_subset hsupp (is_closed_tsupport _) (iterated_fderiv_tsupport_subset hf hif)

lemma continuous.mem_ℒp_of_has_compact_support {α E : Type*} [hα : nonempty α]
  [topological_space α] {m : measurable_space α} [t2_space α] [opens_measurable_space α] 
  [normed_group E] [measurable_space E] [borel_space E]
  [second_countable_topology_either α E]  -- TODO : this should be removable because we are integrating
                                          -- on a compact subset
  {f : α → E} (hf : continuous f) (hsupp : has_compact_support f)
  (p : ℝ≥0∞) (μ : measure α) [is_finite_measure_on_compacts μ]:
  mem_ℒp f p μ := 
begin
  have : bdd_above (range $ norm ∘ f),
    from hf.norm.bdd_above_range_of_has_compact_support hsupp.norm,
  refine mem_ℒp.of_le 
    (mem_ℒp_indicator_const p hsupp.measurable_set (⨆ x, ∥f x∥) (or.inr hsupp.measure_lt_top.ne))
    hf.ae_strongly_measurable (ae_of_all _ $ λ x, _),
  rw norm_indicator_eq_indicator_norm,
  refine set.le_indicator (λ a _, _) (λ a, _) x,
  { rw real.norm_of_nonneg (le_csupr_of_le this hα.some (norm_nonneg _)),
    exact le_csupr this a },
  { intros ha,
    simpa using not_mem_of_not_mem_closure ha }
end

end prelim

private def cont_diff_map_supported_in_submodule (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (K : set E)
  (n : with_top ℕ) : submodule 𝕜 (E → F) :=
{ carrier := {f | cont_diff 𝕜 n f ∧ ∀ x ∉ K, f x = 0},
  zero_mem' := ⟨cont_diff_zero_fun, λ x hx, rfl⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, λ x hx, 
    by rw [pi.add_apply, hf.2 x hx, hg.2 x hx, add_zero]⟩,
  smul_mem' := λ c f hf, ⟨cont_diff_const.smul hf.1, λ x hx,
    by rw [pi.smul_apply, hf.2 x hx, smul_zero]⟩ }

def cont_diff_map_supported_in (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (K : set E)
  (n : with_top ℕ) := ↥(cont_diff_map_supported_in_submodule 𝕜 E F K n)

namespace cont_diff_map_supported_in

section any_set

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {K : set E} {n : with_top ℕ} 
  {f g : cont_diff_map_supported_in 𝕜 E F K n} {x : E}

instance : add_comm_group (cont_diff_map_supported_in 𝕜 E F K n) := submodule.add_comm_group _
instance : module 𝕜 (cont_diff_map_supported_in 𝕜 E F K n) := submodule.module _
instance : has_coe_to_fun (cont_diff_map_supported_in 𝕜 E F K n) (λ _, E → F) := ⟨λ f, f.1⟩

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
by {ext, exact H x}

protected lemma cont_diff (f : cont_diff_map_supported_in 𝕜 E F K n) :
  cont_diff 𝕜 n f :=
f.2.1

protected lemma continuous (f : cont_diff_map_supported_in 𝕜 E F K n) :
  continuous f :=
f.cont_diff.continuous

lemma supported_in (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  ∀ x ∉ K, f x = 0 :=
f.2.2

lemma support_subset (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  support f ⊆ K :=
support_subset_iff'.mpr f.2.2

end any_set

section compact

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {K : compacts E} {n : with_top ℕ} 
  {f g : cont_diff_map_supported_in 𝕜 E F K n} {x : E}

lemma has_compact_support (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  has_compact_support f :=
has_compact_support.intro K.2 f.supported_in

lemma tsupport_subset (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  tsupport f ⊆ K :=
closure_minimal f.support_subset K.2.is_closed

def of_support_subset {f : E → F} (hf : cont_diff 𝕜 n f) (hsupp : support f ⊆ K) :
  cont_diff_map_supported_in 𝕜 E F K n :=
⟨f, ⟨hf, λ x hx, by_contra $ λ hxn, hx (hsupp hxn)⟩⟩

protected lemma bounded (f : cont_diff_map_supported_in 𝕜 E F K n) {i : ℕ} (hi : ↑i ≤ n) : 
  ∃ C, ∀ x, ∥iterated_fderiv 𝕜 i f x∥ ≤ C :=
continuous.bounded_above_of_compact_support 
  ((cont_diff_iff_continuous_differentiable.mp f.cont_diff).1 i hi)
  (has_compact_support_iterated_fderiv f.cont_diff f.has_compact_support hi)

def to_bounded_cont_diff_map (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  B^n⟮E,F;𝕜⟯ :=
⟨f, f.cont_diff, λ i hi, f.bounded hi⟩

lemma to_bounded_cont_diff_map_injective :
  injective (to_bounded_cont_diff_map : cont_diff_map_supported_in 𝕜 E F K n → B^n⟮E,F;𝕜⟯) :=
begin
  intros f g hfg,
  ext x,
  change to_bounded_cont_diff_map f x = _,
  rw hfg,
  refl
end

def to_bounded_cont_diff_mapₗ : 
  cont_diff_map_supported_in 𝕜 E F K n →ₗ[𝕜] (B^n⟮E,F;𝕜⟯) :=
{ to_fun := to_bounded_cont_diff_map,
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl }

noncomputable instance : topological_space (cont_diff_map_supported_in 𝕜 E F K n) :=
topological_space.induced to_bounded_cont_diff_mapₗ infer_instance

noncomputable instance : uniform_space (cont_diff_map_supported_in 𝕜 E F K n) :=
uniform_space.comap to_bounded_cont_diff_mapₗ infer_instance

instance : topological_add_group (cont_diff_map_supported_in 𝕜 E F K n) :=
topological_add_group_induced _

instance : has_continuous_smul 𝕜 (cont_diff_map_supported_in 𝕜 E F K n) :=
has_continuous_smul_induced _

noncomputable! def to_bounded_cont_diff_mapL : 
  cont_diff_map_supported_in 𝕜 E F K n →L[𝕜] (B^n⟮E,F;𝕜⟯) :=
{ to_linear_map := to_bounded_cont_diff_mapₗ,
  cont := continuous_induced_dom }

lemma continuous_iff {X : Type*} [topological_space X] 
  (φ : X → cont_diff_map_supported_in 𝕜 E F K n) : 
  continuous φ ↔ continuous 
    (cont_diff_map_supported_in.to_bounded_cont_diff_map ∘ φ) :=
⟨λ hφ, to_bounded_cont_diff_mapL.continuous.comp hφ, continuous_induced_rng⟩

lemma continuous_of_commutes {𝕜' E' F' : Type*} [normed_group E'] [normed_group F']
  [nondiscrete_normed_field 𝕜'] [normed_space 𝕜' E'] [normed_space 𝕜' F'] {K' : compacts E'}
  (φ : cont_diff_map_supported_in 𝕜 E F K n → cont_diff_map_supported_in 𝕜' E' F' K' n)
  (ψ : B^n⟮E,F;𝕜⟯ → B^n⟮E',F';𝕜'⟯) (hcont : continuous ψ)
  (hcomm : to_bounded_cont_diff_map ∘ φ = ψ ∘ to_bounded_cont_diff_map) :
  continuous φ :=
begin
  rw [continuous_iff, hcomm],
  exact hcont.comp to_bounded_cont_diff_mapL.continuous
end

protected def cast_of_le {k : with_top ℕ} (hkn : k ≤ n) (f : cont_diff_map_supported_in 𝕜 E F K n) :
  cont_diff_map_supported_in 𝕜 E F K k :=
⟨f, f.cont_diff.of_le hkn, f.supported_in⟩

protected def cast_of_leₗ {k : with_top ℕ} (hkn : k ≤ n) :
  cont_diff_map_supported_in 𝕜 E F K n →ₗ[𝕜] cont_diff_map_supported_in 𝕜 E F K k :=
{ to_fun := cont_diff_map_supported_in.cast_of_le hkn,
  map_add' := λ f g, by ext; refl,
  map_smul' := λ c f, by ext; refl }

protected noncomputable! def cast_of_leL {k : with_top ℕ} (hkn : k ≤ n) :
  (cont_diff_map_supported_in 𝕜 E F K n) →L[𝕜] (cont_diff_map_supported_in 𝕜 E F K k) :=
{ to_linear_map := cont_diff_map_supported_in.cast_of_leₗ hkn,
  cont := continuous_induced_rng 
    ((bounded_cont_diff_map.cast_of_leL 𝕜 E F hkn).comp (to_bounded_cont_diff_mapL)).continuous }

protected noncomputable def iterated_fderivL {i : ℕ} (hi : (i : with_top ℕ) ≤ n) : 
  (cont_diff_map_supported_in 𝕜 E F K n) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
bounded_cont_diff_map.iterated_fderivL hi ∘L to_bounded_cont_diff_mapL

protected lemma has_basis_zero : 
  (𝓝 0 : filter $ cont_diff_map_supported_in 𝕜 E F K n).has_basis 
  (λ Nε : ℕ × ℝ, 0 < Nε.2) (λ Nε, ⋂ (i : ℕ) (hiN : i ≤ Nε.1) (hi : ↑i ≤ n), 
    cont_diff_map_supported_in.iterated_fderivL hi ⁻¹' metric.ball 0 Nε.2) :=
begin
  rw [nhds_induced],
  convert bounded_cont_diff_map.has_basis_zero.comap to_bounded_cont_diff_mapₗ,
  ext,
  simp only [mem_Inter, mem_preimage, mem_ball_zero_iff],
  refl
end

section zero

noncomputable instance : metric_space (cont_diff_map_supported_in 𝕜 E F K 0) :=
metric_space.induced (to_bounded_cont_diff_mapL : cont_diff_map_supported_in 𝕜 E F K 0 →L[𝕜] _) 
  to_bounded_cont_diff_map_injective infer_instance

noncomputable instance : normed_group (cont_diff_map_supported_in 𝕜 E F K 0) :=
{ to_metric_space := infer_instance,
  ..normed_group.induced 
    (to_bounded_cont_diff_mapL : cont_diff_map_supported_in 𝕜 E F K 0 →L[𝕜] _)
      .to_linear_map.to_add_monoid_hom to_bounded_cont_diff_map_injective }

lemma norm_def {f : cont_diff_map_supported_in 𝕜 E F K 0} : ∥f∥ = ∥to_bounded_cont_diff_mapL f∥ := rfl

-- TODO : add `cont_diff_map_supported_in.to_bounded_continuous_function`
lemma le_norm {f : cont_diff_map_supported_in 𝕜 E F K 0} (x : E) : ∥f x∥ ≤ ∥f∥ := 
bounded_continuous_function.norm_coe_le_norm 
  (bounded_cont_diff_map.to_bounded_continuous_function 𝕜 E F 0 (to_bounded_cont_diff_mapL f)) x

noncomputable! instance : normed_space 𝕜 (cont_diff_map_supported_in 𝕜 E F K 0) :=
{ norm_smul_le := λ c f, 
  begin
    rw [norm_def, norm_def, continuous_linear_map.map_smul],
    exact normed_space.norm_smul_le _ _
  end }

end zero

section infinity

lemma differentiable (f : cont_diff_map_supported_in 𝕜 E F K ⊤) : differentiable 𝕜 f := 
f.cont_diff.differentiable le_top

noncomputable def fderiv (f : cont_diff_map_supported_in 𝕜 E F K ⊤) : 
  cont_diff_map_supported_in 𝕜 E (E →L[𝕜] F) K ⊤ := 
of_support_subset (cont_diff_top_iff_fderiv.mp f.cont_diff).2 
  (subset_closure.trans $ (fderiv_tsupport_subset f.differentiable).trans f.tsupport_subset)

noncomputable def fderivₗ : cont_diff_map_supported_in 𝕜 E F K ⊤ 
  →ₗ[𝕜] cont_diff_map_supported_in 𝕜 E (E →L[𝕜] F) K ⊤ := 
{ to_fun := cont_diff_map_supported_in.fderiv,
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

noncomputable def fderivL : cont_diff_map_supported_in 𝕜 E F K ⊤ 
  →L[𝕜] cont_diff_map_supported_in 𝕜 E (E →L[𝕜] F) K ⊤ := 
{ to_linear_map := fderivₗ,
  cont := continuous_induced_rng 
    (bounded_cont_diff_map.fderivL ∘L to_bounded_cont_diff_mapL).continuous }

end infinity

lemma mem_ℒp (f : cont_diff_map_supported_in 𝕜 E F K n) 
  [measurable_space 𝕜] [opens_measurable_space 𝕜] 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : mem_ℒp f p μ :=
f.continuous.mem_ℒp_of_has_compact_support f.has_compact_support p μ

variables (n)

def to_Lpₗ [measurable_space 𝕜] [opens_measurable_space 𝕜] 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : 
  (cont_diff_map_supported_in 𝕜 E F K n) →ₗ[𝕜] (Lp F p μ) :=
{ to_fun := λ f, (f.mem_ℒp p μ).to_Lp f,
  map_add' := λ f g, (f.mem_ℒp p μ).to_Lp_add (g.mem_ℒp p μ),
  map_smul' := λ c f, (f.mem_ℒp p μ).to_Lp_const_smul c }

lemma coe_fn_to_Lpₗ [measurable_space 𝕜] [opens_measurable_space 𝕜] 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  to_Lpₗ n p μ f =ᵐ[μ] f :=
(f.mem_ℒp p μ).coe_fn_to_Lp

noncomputable! def to_Lp_zero [measurable_space 𝕜] [opens_measurable_space 𝕜] 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : 
  (cont_diff_map_supported_in 𝕜 E F K 0) →L[𝕜] (Lp F p μ) :=
{ to_linear_map := to_Lpₗ 0 p μ,
  cont := 
  begin
    -- TODO : unify with `continuous.mem_ℒp_of_has_compact_support`
    have hK₁ : measurable_set ↑K := K.compact.measurable_set,
    have hK₂ : μ ↑K ≠ ∞ := K.compact.measure_lt_top.ne,
    change continuous (to_Lpₗ 0 p μ),
    refine linear_map.continuous_of_bound (to_Lpₗ 0 p μ) 
      (∥indicator_const_Lp p hK₁ hK₂ (1 : ℝ)∥) (λ f, _),
    rw [mul_comm],
    refine Lp.norm_le_mul_norm_of_ae_le_mul _,
    filter_upwards [f.coe_fn_to_Lpₗ 0 p μ, 
      (indicator_const_Lp_coe_fn : indicator_const_Lp p hK₁ hK₂ (1 : ℝ) =ᵐ[μ] _)],
    intros x hx₁ hx₂,
    rw [hx₁, hx₂, ← norm_norm f, ← norm_smul, ← indicator_const_smul_apply, norm_indicator_eq_indicator_norm],
    refine set.le_indicator (λ a _, _) (λ a ha, _) x,
    { rw [smul_eq_mul, mul_one, norm_norm],
      exact le_norm _ },
    { rw [f.supported_in _ ha, norm_zero] }
  end }

noncomputable! def to_Lp [measurable_space 𝕜] [opens_measurable_space 𝕜] 
  {m : measurable_space E} [opens_measurable_space E] [measurable_space F] 
  [second_countable_topology F] [borel_space F] (p : ℝ≥0∞) (μ : measure E) [fact (1 ≤ p)]
  [is_finite_measure_on_compacts μ] : 
  (cont_diff_map_supported_in 𝕜 E F K n) →L[𝕜] (Lp F p μ) :=
{ to_fun := λ f, (f.mem_ℒp p μ).to_Lp f,
  map_add' := λ f g, (f.mem_ℒp p μ).to_Lp_add (g.mem_ℒp p μ),
  map_smul' := λ c f, (f.mem_ℒp p μ).to_Lp_const_smul c,
  cont := ((to_Lp_zero p μ).comp (cont_diff_map_supported_in.cast_of_leL (zero_le _))).continuous }  

end compact

section real

variables {E F G : Type*} [normed_group E] [normed_group F] [normed_group G]
  [normed_space ℝ E] [normed_space ℝ F] [normed_space ℝ G] {K : compacts E} 
  {n : with_top ℕ} {f g : cont_diff_map_supported_in ℝ E F K n} {x : E}

lemma continuous_iff_of_linear (T : cont_diff_map_supported_in ℝ E F K n →ₗ[ℝ] G) : 
  continuous T ↔ ∃ (p : ℕ), ∃ C > 0, ∀ f : cont_diff_map_supported_in ℝ E F K n, 
    ∥T f∥ ≤ C * (⨆ (i ≤ p) (hin : ↑i ≤ n) (x : E), ∥iterated_fderiv ℝ i f x∥) :=
begin
  sorry
end

end real

end cont_diff_map_supported_in