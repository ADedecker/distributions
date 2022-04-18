import analysis.calculus.cont_diff
import topology.continuous_function.bounded
import analysis.seminorm
import ..seminorm
import ..bases

open set filter function
open_locale bounded_continuous_function topological_space nnreal

section prelim

lemma infi_binfi_le {ι α : Type*} [partial_order ι] [complete_lattice α] {f : ι → α} :
  (⨅ i (j ≤ i), f j) = (⨅ i, f i) :=
le_antisymm (le_infi $ λ i, infi_le_of_le i $ binfi_le' i le_rfl) (le_infi $ λ i, le_infi₂ $ λ j hj, infi_le f j)

lemma binfi_le_binfi_le {ι α : Type*} [partial_order ι] [complete_lattice α] {f : ι → α} {n : ι} :
  (⨅ (i ≤ n) (j ≤ i), f j) = (⨅ (i ≤ n), f i) :=
le_antisymm 
  (le_infi₂ $ λ i hi, infi_le_of_le i $ infi_le_of_le hi $ binfi_le' i le_rfl) 
  (le_infi₂ $ λ i hi, le_infi₂ $ λ j hj, binfi_le' j $ hj.trans hi)

noncomputable def _root_.continuous_linear_equiv.comp_left_continuous_bounded {𝕜 : Type*} 
  (α : Type*) {β γ : Type*} [topological_space α] [nondiscrete_normed_field 𝕜] 
  {_ : normed_group β} {_ : normed_group γ} [normed_space 𝕜 β] [normed_space 𝕜 γ] (g : β ≃L[𝕜] γ) :
  (α →ᵇ β) ≃L[𝕜] (α →ᵇ γ) :=
continuous_linear_equiv.equiv_of_inverse 
  (g.to_continuous_linear_map.comp_left_continuous_bounded α) 
  (g.symm.to_continuous_linear_map.comp_left_continuous_bounded α) 
  (begin
    intros f,
    ext x,
    simp_rw [continuous_linear_equiv.coe_def_rev, 
              continuous_linear_map.comp_left_continuous_bounded_apply,
              continuous_linear_equiv.coe_coe, continuous_linear_equiv.symm_apply_apply],
  end)
  (begin
    intros f,
    ext x,
    simp_rw [continuous_linear_equiv.coe_def_rev, 
              continuous_linear_map.comp_left_continuous_bounded_apply,
              continuous_linear_equiv.coe_coe, continuous_linear_equiv.apply_symm_apply]
  end)

@[simp] lemma _root_.continuous_linear_equiv.comp_left_continuous_bounded_apply {𝕜 α β γ : Type*} 
  [topological_space α] [nondiscrete_normed_field 𝕜] {_ : normed_group β} {_ : normed_group γ} 
  [normed_space 𝕜 β] [normed_space 𝕜 γ] (g : β ≃L[𝕜] γ) (f : α →ᵇ β) (x : α) :
  (g.comp_left_continuous_bounded α f) x = g (f x) :=
rfl

lemma iterated_fderiv_add {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf ng : with_top ℕ} {i : ℕ} {f g : E → F} (hf : cont_diff 𝕜 nf f)
  (hg : cont_diff 𝕜 ng g) (hif : (i : with_top ℕ) ≤ nf) 
  (hig : (i : with_top ℕ) ≤ ng) : 
iterated_fderiv 𝕜 i (f + g) = (iterated_fderiv 𝕜 i f) + (iterated_fderiv 𝕜 i g) :=
begin
  induction i with i hi,
  { ext x, simp },
  { ext x h, 
    have hif' : (i : with_top ℕ) < nf := 
      lt_of_lt_of_le (with_top.coe_lt_coe.mpr $ nat.lt_succ_self _) hif,
    have hig' : (i : with_top ℕ) < ng := 
      lt_of_lt_of_le (with_top.coe_lt_coe.mpr $ nat.lt_succ_self _) hig,
    have hdf : differentiable 𝕜 (iterated_fderiv 𝕜 i f) :=
      (cont_diff_iff_continuous_differentiable.mp hf).2 i hif',
    have hdg : differentiable 𝕜 (iterated_fderiv 𝕜 i g) :=
      (cont_diff_iff_continuous_differentiable.mp hg).2 i hig',
    calc iterated_fderiv 𝕜 (i+1) (f + g) x h 
        = fderiv 𝕜 (iterated_fderiv 𝕜 i (f + g)) x (h 0) (fin.tail h) : rfl
    ... = fderiv 𝕜 (iterated_fderiv 𝕜 i f + iterated_fderiv 𝕜 i g) x (h 0) (fin.tail h) : 
            by rw hi hif'.le hig'.le
    ... = (fderiv 𝕜 (iterated_fderiv 𝕜 i f) + fderiv 𝕜 (iterated_fderiv 𝕜 i g)) 
              x (h 0) (fin.tail h) : 
            by rw [pi.add_def, fderiv_add hdf.differentiable_at hdg.differentiable_at]; refl
    ... = (iterated_fderiv 𝕜 (i+1) f + iterated_fderiv 𝕜 (i+1) g) x h : rfl }
end

lemma iterated_fderiv_smul {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf : with_top ℕ} {i : ℕ} {a : 𝕜} {f : E → F} (hf : cont_diff 𝕜 nf f)
  (hif : (i : with_top ℕ) ≤ nf) : 
iterated_fderiv 𝕜 i (a • f) = a • (iterated_fderiv 𝕜 i f) :=
begin
  induction i with i hi,
  { ext, simp },
  { ext x h,
    have hif' : (i : with_top ℕ) < nf := 
      lt_of_lt_of_le (with_top.coe_lt_coe.mpr $ nat.lt_succ_self _) hif,
    have hdf : differentiable 𝕜 (iterated_fderiv 𝕜 i f) :=
      (cont_diff_iff_continuous_differentiable.mp hf).2 i hif',
    calc iterated_fderiv 𝕜 (i+1) (a • f) x h
        = fderiv 𝕜 (iterated_fderiv 𝕜 i (a • f)) x (h 0) (fin.tail h) : rfl
    ... = fderiv 𝕜 (a • iterated_fderiv 𝕜 i f) x (h 0) (fin.tail h) : 
            by rw hi hif'.le
    ... = (a • fderiv 𝕜 (iterated_fderiv 𝕜 i f)) x (h 0) (fin.tail h) :
            by rw [pi.smul_def, fderiv_const_smul hdf.differentiable_at]; refl
    ... = (a • iterated_fderiv 𝕜 (i+1) f) x h : rfl }
end

lemma iterated_fderiv_neg {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf : with_top ℕ} {i : ℕ} {f : E → F} (hf : cont_diff 𝕜 nf f)
  (hif : (i : with_top ℕ) ≤ nf) : 
iterated_fderiv 𝕜 i (-f) = -(iterated_fderiv 𝕜 i f) :=
calc iterated_fderiv 𝕜 i (-f) 
    = iterated_fderiv 𝕜 i ((-1 : 𝕜) • f) : by rw [neg_one_smul]
... = (-1 : 𝕜) • iterated_fderiv 𝕜 i f : iterated_fderiv_smul hf hif
... = -(iterated_fderiv 𝕜 i f) : by ext; exact neg_one_smul _ _

end prelim

private def bounded_cont_diff_map_submodule (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  (n : with_top ℕ) : submodule 𝕜 (E → F) :=
{ carrier := {f | cont_diff 𝕜 n f ∧ ∀ (i : ℕ), ↑i ≤ n → 
                  ∃ C, ∀ x, ∥iterated_fderiv 𝕜 i f x∥ ≤ C },
  zero_mem' := ⟨cont_diff_zero_fun, λ i hi, ⟨0, λ x, 
    by rw [pi.zero_def, iterated_fderiv_within_zero_fun, pi.zero_apply, norm_zero]⟩⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, λ i hi, 
    let ⟨Cf, hCf⟩ := hf.2 i hi, ⟨Cg, hCg⟩ := hg.2 i hi in ⟨Cf + Cg, λ x, 
    by {rw [iterated_fderiv_add hf.1 hg.1 hi hi], exact norm_add_le_of_le (hCf x) (hCg x)}⟩⟩,
  smul_mem' := λ c f hf, ⟨cont_diff_const.smul hf.1, λ i hi, 
    let ⟨C, hC⟩ := hf.2 i hi in ⟨∥c∥ * C, λ x, 
    by {rw [iterated_fderiv_smul hf.1 hi, pi.smul_apply, norm_smul],
        exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _) }⟩⟩ }

def bounded_cont_diff_map (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  (n : with_top ℕ) := ↥(bounded_cont_diff_map_submodule 𝕜 E F n)

localized "notation `B^`n`⟮`E`,`F`;`𝕜`⟯` := bounded_cont_diff_map 𝕜 E F n" in 
  bounded_cont_diff_map

namespace bounded_cont_diff_map

section any_field

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {n : with_top ℕ} {f g : B^n⟮E, F; 𝕜⟯} {x : E}

instance : add_comm_group (B^n⟮E, F; 𝕜⟯) := submodule.add_comm_group _
instance : module 𝕜 (B^n⟮E, F; 𝕜⟯) := submodule.module _
instance : has_coe_to_fun (B^n⟮E, F; 𝕜⟯) (λ _, E → F) := ⟨λ f, f.1⟩

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
by {ext, exact H x}

lemma bounded (f : B^n⟮E, F; 𝕜⟯) {i : ℕ} (hi : (i : with_top ℕ) ≤ n) : 
  ∃ C, ∀ x, ∥iterated_fderiv 𝕜 i f x∥ ≤ C :=
f.2.2 i hi

lemma cont_diff (f : B^n⟮E, F; 𝕜⟯) :
  cont_diff 𝕜 n f :=
f.2.1

@[simp] lemma coe_zero : ((0 : B^n⟮E, F; 𝕜⟯) : E → F) = 0 := rfl
lemma zero_apply : (0 : B^n⟮E, F; 𝕜⟯) x = 0 := rfl

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl
lemma add_apply : (f + g) x = f x + g x := rfl

@[simp] lemma coe_smul {r : 𝕜} : ⇑(r • f) = r • f := rfl
lemma smul_apply {r : 𝕜} : (r • f) x = r • (f x) := rfl

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

protected noncomputable def iterated_fderiv (i : ℕ)
  (f : B^n⟮E, F; 𝕜⟯) : 
  E →ᵇ (E [×i]→L[𝕜] F) :=
if hi : (i : with_top ℕ) ≤ n then
{ to_fun := iterated_fderiv 𝕜 i f,
  continuous_to_fun := 
  begin
    have := f.cont_diff,
    rw cont_diff_iff_continuous_differentiable at this,
    exact this.1 i hi
  end,
  map_bounded' := 
  begin
    rcases f.bounded hi with ⟨C, hC⟩,
    use C + C,
    intros x y,
    simp [dist_eq_norm, norm_sub_le_of_le (hC x) (hC y)]
  end }
else 0

@[simp] protected lemma iterated_fderiv_apply_of_le {i : ℕ} (hi : (i : with_top ℕ) ≤ n) 
  (f : B^n⟮E, F; 𝕜⟯) : 
  f.iterated_fderiv i x = iterated_fderiv 𝕜 i f x := 
begin
  rw bounded_cont_diff_map.iterated_fderiv,
  split_ifs,
  refl
end

@[simp] protected lemma iterated_fderiv_apply_of_gt {i : ℕ} (hi : n < (i : with_top ℕ)) 
  (f : B^n⟮E, F; 𝕜⟯) : 
  f.iterated_fderiv i x = 0 := 
begin
  rw lt_iff_not_ge' at hi,
  rw bounded_cont_diff_map.iterated_fderiv,
  split_ifs,
  { contradiction },
  { refl }
end

@[simp] protected lemma iterated_fderiv_add (i : ℕ) :
  (f + g).iterated_fderiv i = f.iterated_fderiv i + g.iterated_fderiv i :=
begin
  ext x : 1,
  by_cases hi : ↑i ≤ n,
  { rw [bounded_continuous_function.add_apply, 
        bounded_cont_diff_map.iterated_fderiv_apply_of_le hi,
        bounded_cont_diff_map.iterated_fderiv_apply_of_le hi, 
        bounded_cont_diff_map.iterated_fderiv_apply_of_le hi,
        bounded_cont_diff_map.coe_add,
        iterated_fderiv_add f.cont_diff g.cont_diff hi hi],
    refl },
  { rw ← lt_iff_not_ge' at hi,
    rw [bounded_continuous_function.add_apply, 
        bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi,
        bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi, 
        bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi,
        add_zero] }
end

@[simp] protected lemma iterated_fderiv_smul (i : ℕ) {r : 𝕜} :
  (r • f).iterated_fderiv i = r • f.iterated_fderiv i :=
begin
  ext x : 1,
  by_cases hi : ↑i ≤ n,
  { rw [bounded_continuous_function.smul_apply,
        bounded_cont_diff_map.iterated_fderiv_apply_of_le hi,
        bounded_cont_diff_map.iterated_fderiv_apply_of_le hi,
        bounded_cont_diff_map.coe_smul,
        iterated_fderiv_smul f.cont_diff hi],
    refl },
  { rw ← lt_iff_not_ge' at hi,
    rw [bounded_continuous_function.smul_apply, 
        bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi,
        bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi, 
        smul_zero] }
end

lemma coe_apply_eq_iterated_fderiv_0 (f : B^n⟮E, F; 𝕜⟯) (x : E) :
  f x = f.iterated_fderiv 0 x fin_zero_elim :=
by rw [f.iterated_fderiv_apply_of_le (zero_le _), iterated_fderiv_zero_apply]

protected noncomputable def iterated_fderivₗ (i : ℕ) :
  B^n⟮E, F; 𝕜⟯ →ₗ[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
{ to_fun := λ f, f.iterated_fderiv i,
  map_add' := λ f g, bounded_cont_diff_map.iterated_fderiv_add i,
  map_smul' :=λ r f, bounded_cont_diff_map.iterated_fderiv_smul i }

@[simp] protected lemma iterated_fderivₗ_apply {i : ℕ} (hi : (i : with_top ℕ) ≤ n) 
  (f : B^n⟮E, F; 𝕜⟯) : 
  bounded_cont_diff_map.iterated_fderivₗ i f = f.iterated_fderiv i := rfl

private noncomputable def tmp_topology₀ (i : ℕ) : 
  topological_space (B^n⟮E, F; 𝕜⟯) :=
topological_space.induced (bounded_cont_diff_map.iterated_fderivₗ i) infer_instance

private noncomputable def tmp_uniform_space₀ (i : ℕ) : 
  uniform_space (B^n⟮E, F; 𝕜⟯) :=
uniform_space.comap (bounded_cont_diff_map.iterated_fderivₗ i) infer_instance -- no defeq problem here

private noncomputable def tmp_topology₁ (i : ℕ) : 
  topological_space (B^n⟮E, F; 𝕜⟯) :=
⨅ (hi : (i : with_top ℕ) ≤ n), tmp_topology₀ i

private noncomputable def tmp_uniform_space₁ (i : ℕ) : 
  uniform_space (B^n⟮E, F; 𝕜⟯) :=
@uniform_space.replace_topology _ (tmp_topology₁ i) 
  (⨅ (hi : (i : with_top ℕ) ≤ n), tmp_uniform_space₀ i) 
  (by rw to_topological_space_infi; refl)

protected noncomputable def topology : topological_space (B^n⟮E, F; 𝕜⟯) := 
  ⨅ (i : ℕ) (hi : (i : with_top ℕ) ≤ n), (tmp_topology₀ i)

protected noncomputable def uniform_space : uniform_space (B^n⟮E, F; 𝕜⟯) := 
@uniform_space.replace_topology _ bounded_cont_diff_map.topology 
  (⨅ (i : ℕ), (tmp_uniform_space₁ i)) (by rw [to_topological_space_infi]; refl )

protected lemma topology_eq_directed : (bounded_cont_diff_map.topology : topological_space (B^n⟮E, F; 𝕜⟯)) = 
  ⨅ (i : ℕ) (hi : ↑i ≤ n) (j : ℕ) (hj : (j : with_top ℕ) ≤ ↑i), (tmp_topology₀ j) :=
le_antisymm 
  (le_infi₂ $ λ i hi, le_infi₂ $ λ j hj, binfi_le' j $ hj.trans hi)
  (le_infi₂ $ λ i hi, infi_le_of_le i $ infi_le_of_le hi $ binfi_le' i le_rfl) 

--protected lemma topology_eq_directed' : (bounded_cont_diff_map.topology : topological_space (B^n⟮E, F; 𝕜⟯)) = 
--  ⨅ (i : ℕ) (hi : ↑i ≤ n), (finset.univ : finset (fin $ i+1)).inf (λ j, tmp_topology₀ j $ j.2.trans hi) :=
--le_antisymm 
--  (le_infi₂ $ λ i hi, le_infi₂ $ λ j hj, binfi_le' j $ hj.trans hi)
--  (le_infi₂ $ λ i hi, infi_le_of_le i $ infi_le_of_le hi $ binfi_le' i le_rfl) 

--protected def seminorm_family : seminorm_family 𝕜 (B^n⟮E, F; 𝕜⟯) {i : ℕ // ↑i ≤ n} :=
--  λ i, norm_seminorm 𝕜 (E → )

private lemma has_basis_zero₀ (i : ℕ) (hi : (i : with_top ℕ) ≤ n) : 
  (@nhds B^n⟮E, F; 𝕜⟯ (tmp_topology₀ i) 0).has_basis (λ ε : ℝ, 0 < ε)
  (λ ε, bounded_cont_diff_map.iterated_fderiv i ⁻¹' metric.ball 0 ε) :=
begin
  rw nhds_induced,
  refine (has_basis.comap _ (metric.nhds_basis_ball)).to_has_basis _ _;
  rintros ε hε;
  refine ⟨ε, hε, _⟩;
  rw [linear_map.map_zero];
  refl
end

private lemma has_basis_zero₁ (i : ℕ) : 
  (@nhds B^n⟮E, F; 𝕜⟯ (tmp_topology₁ i) 0).has_basis (λ ε : ℝ, 0 < ε)
  (λ ε, ⋂ (hi : ↑i ≤ n), bounded_cont_diff_map.iterated_fderiv i ⁻¹' metric.ball 0 ε) :=
begin
  rw [nhds_infi, has_basis_iff],
  by_cases hi : (i : with_top ℕ) ≤ n,
  { simp [hi, (has_basis_zero₀ i hi).mem_iff] },
  { have : ∃ ε : ℝ, 0 < ε := ⟨1, zero_lt_one⟩,
    intros t, 
    simp [hi, univ_subset_iff, this] }
end

attribute [instance] bounded_cont_diff_map.topology
attribute [instance] bounded_cont_diff_map.uniform_space

protected lemma has_basis_zero : (𝓝 0 : filter $ B^n⟮E, F; 𝕜⟯).has_basis 
  (λ Nε : ℕ × ℝ, 0 < Nε.2) (λ Nε, ⋂ (i : ℕ) (hiN : i ≤ Nε.1) (hi : ↑i ≤ n), 
    bounded_cont_diff_map.iterated_fderiv i ⁻¹' metric.ball 0 Nε.2) :=
begin
  rw nhds_infi,
  convert foo _ has_basis_zero₁,
  intros i ε δ h, 
  exact Inter_mono (λ hi, preimage_mono $ metric.ball_subset_ball h)
end

protected noncomputable def iterated_fderivL (i : ℕ) : 
  (B^n⟮E, F; 𝕜⟯) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
{ to_linear_map := bounded_cont_diff_map.iterated_fderivₗ i,
  cont := 
  begin
    by_cases hi : ↑i ≤ n,
    { exact continuous_infi_dom (@continuous_infi_dom _ _ _ _ 
        (λ _, tmp_topology₀ i) _ hi continuous_induced_dom) },
    { refine continuous_of_const (λ f g, _),
      ext x : 1,
      change f.iterated_fderiv i x = g.iterated_fderiv i x,
      rw ← lt_iff_not_ge at hi,
      rw [bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi,
          bounded_cont_diff_map.iterated_fderiv_apply_of_gt hi] }
  end }

--continuous_infi_dom 
--  (@continuous_infi_dom _ _ _ _ (λ _, tmp_topology₀ i) _ hi continuous_induced_dom)

@[simp] protected lemma iterated_fderivL_apply {i : ℕ}
  (f : B^n⟮E, F; 𝕜⟯) : 
  bounded_cont_diff_map.iterated_fderivL i f = f.iterated_fderiv i := rfl

lemma continuous_iff {X : Type*} [topological_space X] (φ : X → B^n⟮E, F; 𝕜⟯) : 
  continuous φ ↔ ∀ (i : ℕ) (hi : ↑i ≤ n), continuous 
    ((bounded_cont_diff_map.iterated_fderiv i) ∘ φ) :=
⟨ λ hφ i hi, (bounded_cont_diff_map.iterated_fderivL i).continuous.comp hφ, 
  λ h, continuous_infi_rng (λ i, continuous_infi_rng $ λ hi, continuous_induced_rng (h i hi)) ⟩

protected lemma continuous_of_commutes {𝕜' E' F' : Type*} [normed_group E'] [normed_group F'] 
  [nondiscrete_normed_field 𝕜'] [normed_space 𝕜' E'] [normed_space 𝕜' F'] 
  (φ : B^n⟮E, F; 𝕜⟯ → B^n⟮E', F'; 𝕜'⟯) 
  (ψ : Π (i : ℕ), (E →ᵇ (E [×i]→L[𝕜] F)) → E' →ᵇ (E' [×i]→L[𝕜'] F'))
  (hcont : ∀ (i : ℕ) (hi : ↑i ≤ n), continuous $ ψ i)
  (hcomm : ∀ (i : ℕ) (hi : ↑i ≤ n), 
    bounded_cont_diff_map.iterated_fderiv i ∘ φ = ψ i ∘ bounded_cont_diff_map.iterated_fderiv i) :
  continuous φ :=
begin
  rw continuous_iff,
  intros i hi,
  rw hcomm i hi,
  exact (hcont i hi).comp (bounded_cont_diff_map.iterated_fderivL i).continuous
end

instance : topological_add_group (B^n⟮E, F; 𝕜⟯) :=
topological_add_group_infi 
  (λ i, topological_add_group_infi $ λ hi, topological_add_group_induced _)

instance : has_continuous_smul 𝕜 (B^n⟮E, F; 𝕜⟯) :=
has_continuous_smul_infi
  (λ i, has_continuous_smul_infi $ λ hi, has_continuous_smul_induced _)

variables (𝕜 E F n)

private noncomputable def to_bounded_continuous_function_aux : 
  (B^n⟮E, F; 𝕜⟯) →L[𝕜] (E →ᵇ F) :=
((continuous_multilinear_curry_fin0 𝕜 E F).to_continuous_linear_equiv
  .comp_left_continuous_bounded E).to_continuous_linear_map ∘L
bounded_cont_diff_map.iterated_fderivL 0

private lemma to_bounded_continuous_function_aux_spec (f : B^n⟮E, F; 𝕜⟯) (x : E) :
  to_bounded_continuous_function_aux 𝕜 E F n f x = f x := 
begin
  change f.iterated_fderiv 0 x 0 = f x,
  rw bounded_cont_diff_map.iterated_fderiv_apply_of_le (zero_le _),
  refl
end

def to_bounded_continuous_function (f : B^n⟮E, F; 𝕜⟯) : E →ᵇ F :=
{ to_fun := f,
  map_bounded' := 
  begin
    rcases (to_bounded_continuous_function_aux 𝕜 E F n f).bounded with ⟨C, hC⟩,
    refine ⟨C, λ x y, _⟩,
    specialize hC x y,
    rw [to_bounded_continuous_function_aux_spec, to_bounded_continuous_function_aux_spec] at hC,
    exact hC
  end,
  continuous_to_fun := 
  begin
    convert (to_bounded_continuous_function_aux 𝕜 E F n f).continuous using 1,
    ext x,
    rw to_bounded_continuous_function_aux_spec
  end }

def to_bounded_continuous_functionₗ : (B^n⟮E, F; 𝕜⟯) →ₗ[𝕜] (E →ᵇ F) :=
{ to_fun := to_bounded_continuous_function 𝕜 E F n,
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl }

noncomputable! def to_bounded_continuous_functionL : 
  (B^n⟮E, F; 𝕜⟯) →L[𝕜] (E →ᵇ F) :=
{ to_linear_map := to_bounded_continuous_functionₗ 𝕜 E F n,
  cont := 
  begin
    convert (to_bounded_continuous_function_aux 𝕜 E F n).continuous using 1,
    ext f x,
    rw to_bounded_continuous_function_aux_spec,
    refl
  end }

lemma to_bounded_continuous_functionL_eq_iterated_fderivL_zero :
  bounded_cont_diff_map.to_bounded_continuous_functionL 𝕜 E F n =
  ((continuous_multilinear_curry_fin0 𝕜 E F).to_continuous_linear_equiv
    .comp_left_continuous_bounded E).to_continuous_linear_map ∘L
  bounded_cont_diff_map.iterated_fderivL 0 := 
begin
  ext f x,
  change f x = _,
  rw ← to_bounded_continuous_function_aux_spec,
  refl
end

lemma to_bounded_continuous_function_injective : 
  injective (to_bounded_continuous_functionL 𝕜 E F n) :=
begin
  intros f g hfg,
  ext x,
  change to_bounded_continuous_functionL 𝕜 E F n f x = _,
  rw hfg,
  refl
end

variables {n}

protected def of_le {k : with_top ℕ} (hkn : k ≤ n) (f : B^n⟮E, F; 𝕜⟯) :
  B^k⟮E, F; 𝕜⟯ :=
⟨f, f.cont_diff.of_le hkn, λ i hi, f.bounded (hi.trans hkn)⟩

protected def of_leₗ {k : with_top ℕ} (hkn : k ≤ n) :
  B^n⟮E, F; 𝕜⟯ →ₗ[𝕜] B^k⟮E, F; 𝕜⟯ :=
{ to_fun := bounded_cont_diff_map.of_le 𝕜 E F hkn,
  map_add' := λ f g, by ext; refl,
  map_smul' := λ c f, by ext; refl }

protected lemma iterated_fderiv_of_le {k : with_top ℕ} (hkn : k ≤ n) 
  {i : ℕ} (hi : ↑i ≤ k) (f : B^n⟮E, F; 𝕜⟯) : 
  (f.of_le 𝕜 E F hkn).iterated_fderiv i = f.iterated_fderiv i :=
begin
  ext x,
  rw [bounded_cont_diff_map.iterated_fderiv_apply_of_le hi,
      bounded_cont_diff_map.iterated_fderiv_apply_of_le (hi.trans hkn)],
  refl
end

-- TODO : why do I need the `!` ?
protected noncomputable! def of_leL {k : with_top ℕ} (hkn : k ≤ n) :
  B^n⟮E, F; 𝕜⟯ →L[𝕜] B^k⟮E, F; 𝕜⟯ :=
{ to_linear_map := bounded_cont_diff_map.of_leₗ 𝕜 E F hkn,
  cont := 
  begin
    refine continuous_infi_rng (λ i, continuous_infi_rng $ λ hi, continuous_induced_rng _),
    convert (bounded_cont_diff_map.iterated_fderivL i).continuous using 1,
    ext f : 1,
    exact f.iterated_fderiv_of_le 𝕜 E F hkn hi
  end }

--protected lemma topology_eq_infi_induced_of_le :
--  bounded_cont_diff_map.topology = ⨅ (i : ℕ) (hi : ↑i ≤ n), bounded_cont_diff_map.topology.induced 
--    (bounded_cont_diff_map.of_leL 𝕜 E F hi) :=
--begin
--  simp_rw [bounded_cont_diff_map.topology, induced_infi, tmp_topology₀],
--  
--end

section zero

private lemma uniform_space_eq_comap : bounded_cont_diff_map.uniform_space = 
  uniform_space.comap (to_bounded_continuous_functionL 𝕜 E F 0) infer_instance := 
begin
  suffices : (bounded_cont_diff_map.uniform_space : uniform_space $ B^0⟮E, F; 𝕜⟯) = 
    uniform_space.comap (bounded_cont_diff_map.iterated_fderivₗ 0) infer_instance,
  { rw [this, to_bounded_continuous_functionL_eq_iterated_fderivL_zero, 
        continuous_linear_map.coe_comp'],
    conv_rhs {rw [uniform_space.comap_comap]},
    refine congr_arg _ _,
    ext s,
    change s ∈ uniformity _ ↔ s ∈  uniformity _,
    rw ← ((continuous_multilinear_curry_fin0 𝕜 E F).to_continuous_linear_equiv
      .comp_left_continuous_bounded E).uniform_embedding.to_uniform_inducing.comap_uniformity,
    refl },
  ext s : 1,
  change (⨅ _ _, _) = _,
  rw infi_range,
  change (⨅ _ _, _) = _,
  simp_rw infi_range,
  refine le_antisymm (binfi_le' 0 le_rfl) (le_infi $ λ i, le_infi $ λ hi, _),
  convert le_refl _,
  rw ← nat.le_zero_iff, exact_mod_cast hi
end

noncomputable instance : metric_space (B^0⟮E, F; 𝕜⟯) :=
(metric_space.induced (to_bounded_continuous_function 𝕜 E F 0) 
  (to_bounded_continuous_function_injective 𝕜 E F 0) infer_instance).replace_uniformity
(by rw uniform_space_eq_comap)

noncomputable instance : normed_group (B^0⟮E, F; 𝕜⟯) :=
{ to_metric_space := infer_instance,
  ..normed_group.induced (to_bounded_continuous_functionₗ 𝕜 E F 0).to_add_monoid_hom 
  (to_bounded_continuous_function_injective 𝕜 E F 0) }

@[simp] lemma norm_def {f : B^0⟮E, F; 𝕜⟯} : ∥f∥ = ∥to_bounded_continuous_functionL 𝕜 E F 0 f∥ := rfl

noncomputable! instance : normed_space 𝕜 (B^0⟮E, F; 𝕜⟯) :=
{ norm_smul_le := λ c f, 
  begin
    rw [norm_def, norm_def, continuous_linear_map.map_smul],
    exact normed_space.norm_smul_le _ _
  end }

end zero

section infinity

variables {𝕜 E F}

protected lemma differentiable (f : B^⊤⟮E, F; 𝕜⟯) : differentiable 𝕜 f := 
f.cont_diff.differentiable le_top 

protected noncomputable def fderiv (f : B^⊤⟮E, F; 𝕜⟯) : B^⊤⟮E, E →L[𝕜] F; 𝕜⟯ := 
⟨fderiv 𝕜 f, (cont_diff_top_iff_fderiv.mp f.cont_diff).2, 
  begin
    intros i _,
    rcases f.bounded (le_top : ↑(i+1) ≤ _) with ⟨C, hC⟩,
    use C,
    intros x,
    specialize hC x,
    rwa [iterated_fderiv_succ_eq_comp_right, linear_isometry_equiv.norm_map] at hC
  end⟩

@[simp] protected lemma fderiv_apply (f : B^⊤⟮E, F; 𝕜⟯) : 
  f.fderiv x = fderiv 𝕜 f x := rfl

protected noncomputable def fderivₗ : B^⊤⟮E, F; 𝕜⟯ →ₗ[𝕜] B^⊤⟮E, E →L[𝕜] F; 𝕜⟯ := 
{ to_fun := bounded_cont_diff_map.fderiv,
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

@[simp] protected lemma fderivₗ_apply (f : B^⊤⟮E, F; 𝕜⟯) : 
  ⇑(bounded_cont_diff_map.fderivₗ f) = fderiv 𝕜 f := rfl

noncomputable def fderivL : B^⊤⟮E, F; 𝕜⟯ →L[𝕜] B^⊤⟮E, E →L[𝕜] F; 𝕜⟯ := 
{ to_linear_map := bounded_cont_diff_map.fderivₗ,
  cont := 
  begin
    rw bounded_cont_diff_map.continuous_iff,
    intros i hi,
    set! φ := 
      (continuous_linear_map.comp_left_continuous_bounded E 
        (continuous_multilinear_curry_right_equiv' 𝕜 i E F).symm
          .to_continuous_linear_equiv.to_continuous_linear_map).comp 
      (bounded_cont_diff_map.iterated_fderivL (i+1))
      with hφ,
    have : bounded_cont_diff_map.iterated_fderiv i ∘ bounded_cont_diff_map.fderivₗ.to_fun = φ,
    { rw hφ,
      ext f H k x, 
      simp [iterated_fderiv_succ_apply_right] }, -- slooooooooooow
    rw this,
    exact φ.continuous
  end }

end infinity

end any_field

section real

variables {E F G : Type*} [normed_group E] [normed_group F] [normed_group G] 
  [normed_space ℝ E] [normed_space ℝ F] [normed_space ℝ G]
  {n : with_top ℕ} {n' : ℕ} {f g : B^n⟮E, F; ℝ⟯} {x : E}

instance : locally_convex_space ℝ (B^n⟮E, F; ℝ⟯) := sorry

end real

--section real
--
--open_locale pointwise
--
--variables {E F G : Type*} [normed_group E] [normed_group F] [normed_group G] 
--  [normed_space ℝ E] [normed_space ℝ F] [normed_space ℝ G]
--  {n : with_top ℕ} {f g : B^n⟮E, F; ℝ⟯} {x : E}
--
----protected lemma has_basis_zero_homotethy : (𝓝 0 : filter $ B^n⟮E, F; ℝ⟯).has_basis 
----  (λ Nε : ℕ × ℝ, 0 < Nε.2) (λ Nε, Nε.2 • {f | ∀ (i : ℕ) (hiN : i ≤ Nε.1) 
----    (hi : (i : with_top ℕ) ≤ n) , ∥f.iterated_fderiv hi∥ < 1}) :=
----begin
----  refine bounded_cont_diff_map.has_basis_zero.to_has_basis _ _,
----  { rintros ⟨N, ε⟩ hε,
----    refine ⟨⟨N, 1/ε⟩, one_div_pos.mpr hε, _⟩,
----    change _ • _ ⊆ _,
----    rw set_smul_subset_iff₀, }
----  
----end
--
--lemma goal (T : B^n⟮E, F; ℝ⟯ →ₗ[ℝ] G) : 
--  continuous T ↔ ∃ (p : ℕ), ∃ C > 0, ∀ f : B^n⟮E, F; ℝ⟯, 
--    ∥T f∥ ≤ C * (⨆ (i : ℕ) (hip : i ≤ p) (hin : ↑i ≤ n), ∥f.iterated_fderiv hin∥) :=
--begin
--  sorry
--end
--
--lemma continuous_iff_of_linear (T : B^n⟮E, F; ℝ⟯ →ₗ[ℝ] G) : 
--  continuous T ↔ ∃ (p : ℕ), ∃ C > 0, ∀ f : B^n⟮E, F; ℝ⟯, 
--    ∥T f∥ ≤ C * (⨆ (i ≤ p) (hin : ↑i ≤ n) (x : E), ∥iterated_fderiv ℝ i f x∥) :=
--begin
--  sorry
--end
--
--lemma bar (T : B^n⟮E, F; ℝ⟯ →ₗ[ℝ] G) : 
--  continuous_at T 0 ↔ ∃ (p : ℕ), ∃ C > 0, ∀ f : B^n⟮E, F; ℝ⟯, 
--    ∥T f∥ ≤ C * (⨆ (i : ℕ) (hip : i ≤ p) (hin : ↑i ≤ n), ∥f.iterated_fderiv hin∥) :=
--begin
--  rw [continuous_at, map_zero, 
--      bounded_cont_diff_map.has_basis_zero.tendsto_iff metric.nhds_basis_ball],
--  split,
--  { intro H,
--    rcases H 1 zero_lt_one with ⟨⟨p, ε⟩, hε, H'⟩,
--    refine ⟨p, ε⁻¹, inv_pos.mpr hε, λ f, _⟩,
--    sorry },
--  { rintros ⟨p, C, hC, H⟩ ε hε,
--    sorry }
--end
--
--end real
--

end bounded_cont_diff_map