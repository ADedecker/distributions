import analysis.calculus.times_cont_diff
import topology.continuous_function.bounded

open set
open_locale bounded_continuous_function

section prelim

lemma iterated_fderiv_add {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf ng : with_top ℕ} {i : ℕ} {f g : E → F} (hf : times_cont_diff 𝕜 nf f)
  (hg : times_cont_diff 𝕜 ng g) (hif : (i : with_top ℕ) ≤ nf) 
  (hig : (i : with_top ℕ) ≤ ng) : 
iterated_fderiv 𝕜 i (f + g) = (iterated_fderiv 𝕜 i f) + (iterated_fderiv 𝕜 i g) :=
begin
  sorry
end

lemma iterated_fderiv_smul {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf : with_top ℕ} {i : ℕ} {a : 𝕜} {f : E → F} (hf : times_cont_diff 𝕜 nf f)
  (hif : (i : with_top ℕ) ≤ nf) : 
iterated_fderiv 𝕜 i (a • f) = a • (iterated_fderiv 𝕜 i f) :=
begin
  sorry
end

lemma iterated_fderiv_neg {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  {nf : with_top ℕ} {i : ℕ} {f : E → F} (hf : times_cont_diff 𝕜 nf f)
  (hif : (i : with_top ℕ) ≤ nf) : 
iterated_fderiv 𝕜 i (-f) = -(iterated_fderiv 𝕜 i f) :=
begin
  sorry
end

end prelim

private def bounded_times_cont_diff_map_submodule (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  (n : with_top ℕ) : submodule 𝕜 (E → F) :=
{ carrier := {f | times_cont_diff 𝕜 n f ∧ ∀ (i : ℕ), ↑i ≤ n → 
                  ∃ C, ∀ x, ∥iterated_fderiv 𝕜 i f x∥ ≤ C },
  zero_mem' := ⟨times_cont_diff_zero_fun, λ i hi, ⟨0, λ x, 
    by rw [pi.zero_def, iterated_fderiv_within_zero_fun, pi.zero_apply, norm_zero]⟩⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, λ i hi, 
    let ⟨Cf, hCf⟩ := hf.2 i hi, ⟨Cg, hCg⟩ := hg.2 i hi in ⟨Cf + Cg, λ x, 
    by {rw [iterated_fderiv_add hf.1 hg.1 hi hi], exact norm_add_le_of_le (hCf x) (hCg x)}⟩⟩,
  smul_mem' := λ c f hf, ⟨times_cont_diff_const.smul hf.1, λ i hi, 
    let ⟨C, hC⟩ := hf.2 i hi in ⟨∥c∥ * C, λ x, 
    by {rw [iterated_fderiv_smul hf.1 hi, pi.smul_apply, norm_smul],
        exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _) }⟩⟩ }

def bounded_times_cont_diff_map (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  (n : with_top ℕ) := ↥(bounded_times_cont_diff_map_submodule 𝕜 E F n)

localized "notation `B^`n`⟮`E`,`F`;`𝕜`⟯` := bounded_times_cont_diff_map 𝕜 E F n" in 
  bounded_times_cont_diff_map

namespace bounded_times_cont_diff_map

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

lemma times_cont_diff (f : B^n⟮E, F; 𝕜⟯) :
  times_cont_diff 𝕜 n f :=
f.2.1

@[simp] lemma coe_zero : ((0 : B^n⟮E, F; 𝕜⟯) : E → F) = 0 := rfl
lemma zero_apply : (0 : B^n⟮E, F; 𝕜⟯) x = 0 := rfl

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl
lemma add_apply : (f + g) x = f x + g x := rfl

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

protected noncomputable def iterated_fderiv {i : ℕ} (hi : (i : with_top ℕ) ≤ n) 
  (f : B^n⟮E, F; 𝕜⟯) : 
  E →ᵇ (E [×i]→L[𝕜] F) :=
{ to_fun := iterated_fderiv 𝕜 i f,
  continuous_to_fun := 
  begin
    have := f.times_cont_diff,
    rw times_cont_diff_iff_continuous_differentiable at this,
    exact this.1 i hi
  end,
  bounded' := 
  begin
    rcases f.bounded hi with ⟨C, hC⟩,
    use C + C,
    intros x y,
    simp [dist_eq_norm, norm_sub_le_of_le (hC x) (hC y)]
  end }

@[simp] protected lemma iterated_fderiv_add {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  (f + g).iterated_fderiv hi = f.iterated_fderiv hi + g.iterated_fderiv hi :=
begin
  ext x : 1,
  change iterated_fderiv 𝕜 i (f + g) x = iterated_fderiv 𝕜 i f x + iterated_fderiv 𝕜 i g x,
  rw iterated_fderiv_add f.times_cont_diff g.times_cont_diff hi hi,
  refl
end

@[simp] protected lemma iterated_fderiv_smul {i : ℕ} (hi : (i : with_top ℕ) ≤ n) {r : 𝕜} :
  (r • f).iterated_fderiv hi = r • f.iterated_fderiv hi :=
begin
  ext x : 1,
  change iterated_fderiv 𝕜 i (r • f) x = r • iterated_fderiv 𝕜 i f x,
  rw iterated_fderiv_smul f.times_cont_diff hi,
  refl
end

protected noncomputable def iterated_fderivₗ {i : ℕ} (hi : (i : with_top ℕ) ≤ n) :
  B^n⟮E, F; 𝕜⟯ →ₗ[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
{ to_fun := λ f, f.iterated_fderiv hi,
  map_add' := λ f g, bounded_times_cont_diff_map.iterated_fderiv_add hi,
  map_smul' :=λ r f, bounded_times_cont_diff_map.iterated_fderiv_smul hi }

noncomputable instance : topological_space (B^n⟮E, F; 𝕜⟯) := 
  ⨅ (i : ℕ) (hi : (i : with_top ℕ) ≤ n), topological_space.induced 
  (bounded_times_cont_diff_map.iterated_fderivₗ hi) infer_instance

protected noncomputable def iterated_fderivL {i : ℕ} (hi : (i : with_top ℕ) ≤ n) : 
  (B^n⟮E, F; 𝕜⟯) →L[𝕜] (E →ᵇ (E [×i]→L[𝕜] F)) :=
{ to_linear_map := bounded_times_cont_diff_map.iterated_fderivₗ hi,
  cont := continuous_infi_dom (continuous_infi_dom continuous_induced_dom) }

end bounded_times_cont_diff_map