import topology.compacts

open topological_space

namespace compacts

variables {α : Type*} [topological_space α]

instance : has_coe (compacts α) (set α) := { coe := subtype.val }

lemma val_eq_coe (U : compacts α) : U.1 = ↑U := rfl

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
lemma coe_mk {α : Type*} [topological_space α] {U : set α} {hU : is_compact U} :
  ↑(⟨U, hU⟩ : compacts α) = U := rfl

instance : has_subset (compacts α) :=
{ subset := λ U V, (U : set α) ⊆ V }

instance : has_mem α (compacts α) :=
{ mem := λ a U, a ∈ (U : set α) }

@[simp] lemma subset_coe {U V : compacts α} : ((U : set α) ⊆ (V : set α)) = (U ⊆ V) := rfl

@[simp] lemma mem_coe {x : α} {U : compacts α} : (x ∈ (U : set α)) = (x ∈ U) := rfl

@[ext] lemma ext {U V : compacts α} (h : (U : set α) = V) : U = V := subtype.ext_iff.mpr h

@[ext] lemma ext_iff {U V : compacts α} : (U : set α) = V ↔ U = V :=
⟨compacts.ext, congr_arg coe⟩

end compacts