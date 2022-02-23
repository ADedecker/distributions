import spaces.bounded_cont_diff_map
import analysis.normed.group.basic
import ..compacts

open topological_space function
open_locale bounded_cont_diff_map topological_space

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

lemma supported_in (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  ∀ x ∉ K, f x = 0 :=
f.2.2

end any_set

section compact

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {K : compacts E} {n : with_top ℕ} 
  {f g : cont_diff_map_supported_in 𝕜 E F K n} {x : E}

lemma has_compact_support (f : cont_diff_map_supported_in 𝕜 E F K n) : 
  has_compact_support f :=
has_compact_support.intro K.2 f.supported_in

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

def to_bounded_cont_diff_mapₗ : 
  cont_diff_map_supported_in 𝕜 E F K n →ₗ[𝕜] (B^n⟮E,F;𝕜⟯) :=
{ to_fun := to_bounded_cont_diff_map,
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl }

noncomputable instance : topological_space (cont_diff_map_supported_in 𝕜 E F K n) :=
topological_space.induced to_bounded_cont_diff_mapₗ infer_instance

instance : topological_add_group (cont_diff_map_supported_in 𝕜 E F K n) :=
topological_add_group_induced _

instance : has_continuous_smul 𝕜 (cont_diff_map_supported_in 𝕜 E F K n) :=
has_continuous_smul_induced _

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