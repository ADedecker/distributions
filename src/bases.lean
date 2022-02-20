import order.filter.bases
import data.nat.interval
import data.nat.lattice

open set function

namespace filter

#check filter.has_basis_infi
#check binfi_le
#check infi_le'

theorem infi_le'' {ι : Sort*} {α : Type*} [complete_semilattice_Inf α] (s : ι → α) (i : ι) : infi s ≤ s i :=
Inf_le ⟨i, rfl⟩

theorem infi_le_of_le' {ι : Sort*} {α : Type*} [complete_semilattice_Inf α] {s : ι → α} {a : α} (i : ι) 
  (h : s i ≤ a) : infi s ≤ a :=
le_trans (infi_le'' _ i) h

theorem binfi_le' {ι : Sort*} {α : Type*} [complete_semilattice_Inf α] {p : ι → Prop} {f : Π i (hi : p i), α} 
  (i : ι) (hi : p i) : (⨅ i hi, f i hi) ≤ f i hi :=
infi_le_of_le' i (infi_le'' (f i) hi)

lemma has_basis_infi_of_monotone {ι ι' α : Sort*} [complete_semilattice_Inf ι'] {f : ι → filter α}
  {p : ι' → Prop} {s : ι → ι' → set α} (hbasis : ∀ i, (f i).has_basis p (s i)) 
  (hmono : ∀ i, monotone (s i)) (hstable : ∀ I' : set ι', (∀ i' ∈ I', p i') → p (Inf I')):
  (⨅ i, f i).has_basis (λ Ii' : set ι × ι', Ii'.fst.finite ∧ p Ii'.2) 
    (λ Ii', ⋂ i ∈ Ii'.1, s i Ii'.2) :=
begin
  refine (has_basis_infi hbasis).to_has_basis _ _,
  { rintros ⟨I, f⟩ ⟨hI, hf⟩,
    refine ⟨⟨I, ⨅ i ∈ I, f i⟩, 
      ⟨hI, hstable _ $ forall_range_iff.mpr $ λ i, hstable _ (forall_range_iff.mpr $ hf i)⟩, _⟩,
    rw [subset_Inter₂_iff],
    intros i hi,
    exact Inter_subset_of_subset i (Inter_subset_of_subset hi $ hmono i $ binfi_le' i hi) },
  { rintros ⟨I, i'⟩ ⟨hI, hi'⟩,
    refine ⟨⟨I, const ι i'⟩, ⟨hI, λ _ _, hi'⟩, _⟩,
    rw [subset_Inter₂_iff],
    intros i hi,
    exact Inter_subset_of_subset i (Inter_subset_of_subset hi $ by refl) }
end

lemma has_basis_infi_nat_of_monotone {ι' α : Sort*} [complete_semilattice_Inf ι'] {f : ℕ → filter α}
  {p : ι' → Prop} {s : ℕ → ι' → set α} (hbasis : ∀ n, (f n).has_basis p (s n)) 
  (hmono : ∀ n, monotone (s n)) (hstable : ∀ I' : set ι', (∀ i' ∈ I', p i') → p (Inf I')):
  (⨅ i, f i).has_basis (λ ni' : ℕ × ι', p ni'.2) 
    (λ ni', ⋂ i ≤ ni'.1, s i ni'.2) :=
begin
  refine (has_basis_infi_of_monotone hbasis hmono hstable).to_has_basis _ _,
  { rintros ⟨S, i'⟩ ⟨hS, hp⟩,
    refine ⟨⟨Sup S, i'⟩, ⟨hp, _⟩⟩,
    rw [subset_Inter₂_iff],
    intros i hi,
    exact Inter_subset_of_subset i 
      (Inter_subset_of_subset (le_cSup hS.bdd_above hi) $ subset_refl _) },
  { rintros ⟨n, i'⟩ hi',
    exact ⟨⟨Iic n, i'⟩, ⟨finite_Iic _, hi'⟩, subset_refl _⟩ },
end

end filter