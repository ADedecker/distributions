import spaces.bounded_times_cont_diff_map

open topological_space
open_locale bounded_times_cont_diff_map

private def times_cont_diff_map_supported_in_submodule (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (K : set E)
  (n : with_top ℕ) : submodule 𝕜 (E → F) :=
{ carrier := {f | times_cont_diff 𝕜 n f ∧ ∀ x ∉ K, f x = 0},
  zero_mem' := ⟨times_cont_diff_zero_fun, λ x hx, rfl⟩,
  add_mem' := λ f g hf hg, ⟨hf.1.add hg.1, λ x hx, 
    by rw [pi.add_apply, hf.2 x hx, hg.2 x hx, add_zero]⟩,
  smul_mem' := λ c f hf, ⟨times_cont_diff_const.smul hf.1, λ x hx,
    by rw [pi.smul_apply, hf.2 x hx, smul_zero]⟩ }

def times_cont_diff_map_supported_in (𝕜 E F : Type*) [nondiscrete_normed_field 𝕜] 
  [normed_group E] [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] (K : set E)
  (n : with_top ℕ) := ↥(times_cont_diff_map_supported_in_submodule 𝕜 E F K n)

namespace times_cont_diff_map_supported_in

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 F] {K : set E} {n : with_top ℕ} 
  {f g : times_cont_diff_map_supported_in 𝕜 E F K n} {x : E}

instance : add_comm_group (times_cont_diff_map_supported_in 𝕜 E F K n) := submodule.add_comm_group _
instance : module 𝕜 (times_cont_diff_map_supported_in 𝕜 E F K n) := submodule.module _

instance : has_coe_to_fun (times_cont_diff_map_supported_in 𝕜 E F K n) (λ _, E → F) := ⟨λ f, f.1⟩

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
by {ext, exact H x}

lemma times_cont_diff (f : times_cont_diff_map_supported_in 𝕜 E F K n) :
  times_cont_diff 𝕜 n f :=
f.2.1

lemma supported_in (f : times_cont_diff_map_supported_in 𝕜 E F K n) : 
  ∀ x ∉ K, f x = 0 :=
f.2.2

def to_bounded_times_cont_diff_map (hK : is_closed K) (f : times_cont_diff_map_supported_in 𝕜 E F K n) : 
  B^n⟮E,F;𝕜⟯ :=
⟨f, f.times_cont_diff, sorry⟩

def to_bounded_times_cont_diff_mapₗ (hK : is_closed K) : 
  times_cont_diff_map_supported_in 𝕜 E F K n →ₗ[𝕜] (B^n⟮E,F;𝕜⟯) :=
{ to_fun := to_bounded_times_cont_diff_map,
  map_add' := λ f g, 
  begin
    ext, simp,
  end }

end times_cont_diff_map_supported_in