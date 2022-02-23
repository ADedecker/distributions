import topology.algebra.module.locally_convex

open filter
open_locale pointwise topological_space

def has_homothetic_basis {ι E : Sort*} [topological_space E] [has_scalar ℝ E] (l : filter E) 
  (p : ι → Prop) (s : ι → set E) : Prop :=
has_basis l (λ iε : ι × ℝ, p iε.1 ∧ 0 < iε.2) (λ iε, iε.2 • s iε.1)

lemma ball_eq_smul_ball {E : Sort*} [semi_normed_group E] [normed_space ℝ E] {ε : ℝ} (hε : 0 < ε) :
  metric.ball (0 : E) ε = ε • metric.ball (0 : E) 1 :=
begin
  ext x,
  split;
  intros hx,
  { refine ⟨ε⁻¹ • x, _, _⟩,
    { rw mem_ball_zero_iff at *,
      rw norm_smul_of_nonneg (inv_nonneg.mpr hε.le),
      rwa [← mul_lt_mul_left (inv_pos.mpr hε), inv_mul_cancel hε.ne.symm] at hx },
    { rw [smul_smul, mul_inv_cancel hε.ne.symm, one_smul] } },
  { rcases hx with ⟨y, hy, rfl⟩,
    rw mem_ball_zero_iff at *,
    rw [norm_smul_of_nonneg hε.le],
    rwa [← mul_lt_mul_left hε, mul_one] at hy }
end

lemma normed_space.has_homothetic_basis_zero {ι E : Sort*} [semi_normed_group E] 
  [normed_space ℝ E] :
  has_homothetic_basis (𝓝 0 : filter E) (λ (i : unit), true) (λ _, metric.ball (0 : E) 1) :=
metric.nhds_basis_ball.to_has_basis 
  (λ ε hε, ⟨⟨(), ε⟩, ⟨true.intro, hε⟩, by simp [ball_eq_smul_ball hε]⟩) 
  (λ iε hiε, ⟨iε.2, hiε.2, by simp [ball_eq_smul_ball hiε.2]⟩)

