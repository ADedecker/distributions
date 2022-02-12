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

structure bounded_times_cont_diff_map (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] 
  (n : with_top ℕ) :=
(to_fun : E → F)
(times_cont_diff' : times_cont_diff 𝕜 n to_fun)
(bounded' : ∀ (i : ℕ), (i : with_top ℕ) ≤ n → 
  ∃ C, ∀ x, ∥iterated_fderiv 𝕜 i to_fun x∥ ≤ C)

localized "notation `B^`n`⟮`E`,`F`;`𝕜`⟯` := bounded_times_cont_diff_map 𝕜 E F n" in 
  bounded_times_cont_diff_map

namespace bounded_times_cont_diff_map

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {n : with_top ℕ} {f g : B^n⟮E, F; 𝕜⟯} {x : E}

instance : has_coe_to_fun (B^n⟮E, F; 𝕜⟯) (λ _, E → F) :=  ⟨λ f, f.to_fun⟩

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
by { cases f, cases g, congr, ext, exact H x, }

lemma bounded (f : B^n⟮E, F; 𝕜⟯) {i : ℕ} (hi : (i : with_top ℕ) ≤ n) : 
  ∃ C, ∀ x, ∥iterated_fderiv 𝕜 i f x∥ ≤ C :=
f.bounded' i hi

lemma times_cont_diff (f : B^n⟮E, F; 𝕜⟯) :
  times_cont_diff 𝕜 n f :=
f.times_cont_diff'

instance : has_zero (B^n⟮E, F; 𝕜⟯) := 
{ zero := 
  { to_fun := 0,
    times_cont_diff' := times_cont_diff_zero_fun,
    bounded' := 
    begin
      intros i hi,
      use 0,
      intros x,
      rw [pi.zero_def, iterated_fderiv_within_zero_fun, pi.zero_apply, norm_zero]
    end } }

@[simp] lemma coe_zero : ((0 : B^n⟮E, F; 𝕜⟯) : E → F) = 0 := rfl
lemma zero_apply : (0 : B^n⟮E, F; 𝕜⟯) x = 0 := rfl

instance : has_add (B^n⟮E, F; 𝕜⟯) :=
{ add := λ a b,
  { to_fun := a + b,
    times_cont_diff' := a.times_cont_diff.add b.times_cont_diff,
    bounded' := 
    begin
      intros i hi,
      rcases a.bounded hi with ⟨Ca, hCa⟩,
      rcases b.bounded hi with ⟨Cb, hCb⟩,
      use Ca + Cb,
      intros x,
      rw iterated_fderiv_add a.times_cont_diff b.times_cont_diff hi hi,
      exact norm_add_le_of_le (hCa x) (hCb x)
    end } }

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl
lemma add_apply : (f + g) x = f x + g x := rfl

instance : has_neg (B^n⟮E, F; 𝕜⟯) := 
{ neg := λ a,
  { to_fun := -a,
    times_cont_diff' := a.times_cont_diff.neg,
    bounded' := 
    begin
      intros i hi,
      rcases a.bounded hi with ⟨C, hC⟩,
      use C,
      intros x,
      rw [iterated_fderiv_neg a.times_cont_diff hi, pi.neg_apply, norm_neg],
      exact hC x
    end } }

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

instance : add_comm_group (B^n⟮E, F; 𝕜⟯) :=
{ zero_add := λ a, by {ext, rw [add_apply, zero_apply, zero_add] },
  add_zero := λ a, by {ext, rw [add_apply, zero_apply, add_zero] },
  add_assoc := λ a b c, by {ext, rw [add_apply, add_apply, add_apply, add_apply, add_assoc] },
  add_comm := λ a b, by {ext, rw [add_apply, add_apply, add_comm] },
  add_left_neg := λ a, by {ext, rw [add_apply, neg_apply, add_left_neg, zero_apply] },
  ..bounded_times_cont_diff_map.has_neg,
  ..bounded_times_cont_diff_map.has_zero,
  ..bounded_times_cont_diff_map.has_add }

instance : has_scalar 𝕜 (B^n⟮E, F; 𝕜⟯) :=
{ smul := λ x a, 
  { to_fun := x • a,
    times_cont_diff' := times_cont_diff_const.smul a.times_cont_diff,
    bounded' := 
    begin
      intros i hi,
      rcases a.bounded hi with ⟨C, hC⟩,
      use ∥x∥ * C,
      intros y,
      rw [iterated_fderiv_smul a.times_cont_diff hi, pi.smul_apply, norm_smul],
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _) 
    end } }

instance : module 𝕜 (B^n⟮E, F; 𝕜⟯) :=
{ smul     := (•),
  smul_add := λ c f g, ext $ λ x, smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul c₁ c₂ (f x),
  one_smul := λ f, ext $ λ x, one_smul 𝕜 (f x),
  smul_zero := λ c, ext $ λ x, smul_zero c,
  zero_smul := λ f, ext $ λ x, zero_smul 𝕜 (f x),
  ..bounded_continuous_function.add_comm_monoid }

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