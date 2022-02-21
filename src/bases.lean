import order.filter.bases
import data.nat.interval
import data.nat.lattice
import data.real.basic

open set function

namespace filter

theorem infi_le'' {ι : Sort*} {α : Type*} [complete_semilattice_Inf α] (s : ι → α) (i : ι) : infi s ≤ s i :=
Inf_le ⟨i, rfl⟩

theorem infi_le_of_le' {ι : Sort*} {α : Type*} [complete_semilattice_Inf α] {s : ι → α} {a : α} (i : ι) 
  (h : s i ≤ a) : infi s ≤ a :=
le_trans (infi_le'' _ i) h

theorem binfi_le' {ι : Sort*} {α : Type*} [complete_semilattice_Inf α] {p : ι → Prop} {f : Π i (hi : p i), α} 
  (i : ι) (hi : p i) : (⨅ i hi, f i hi) ≤ f i hi :=
infi_le_of_le' i (infi_le'' (f i) hi)

lemma has_basis_infi' {ι : Type*} {α : Type*} {ι' : ι → Type*} {l : ι → filter α}
  {p : Π i, ι' i → Prop} {s : Π i, ι' i → set α} (hl : ∀ i, (l i).has_basis (p i) (s i)) :
  (⨅ i, l i).has_basis (λ If : finset ι × Π i, ι' i, ∀ i ∈ If.1, p i (If.2 i))
    (λ If : finset ι × Π i, ι' i, ⋂ i ∈ If.1, s i (If.2 i)) :=
begin
  refine (has_basis_infi hl).to_has_basis _ _,
  { rintros ⟨I, f⟩ ⟨hI, hf⟩,
    refine ⟨⟨hI.to_finset, f⟩, ⟨_, _⟩⟩;
    simp only [finite.mem_to_finset, subset_Inter₂_iff],
    { exact hf },
    { rintros i hi,
      exact Inter_subset_of_subset i (Inter_subset _ hi) } },
  { rintros ⟨I, f⟩ hf,
    exact ⟨⟨I, f⟩, ⟨⟨I.finite_to_set, hf⟩, subset_refl _⟩⟩ }
end

lemma foo {α : Type*} {l : ℕ → filter α} {s : ℕ → ℝ → set α} (hs : ∀ n, monotone (s n))
  (hbasis : ∀ n, (l n).has_basis (λ ε : ℝ, 0 < ε) (s n)) : (⨅ n, l n).has_basis 
  (λ Nε : ℕ × ℝ, 0 < Nε.2) (λ Nε, ⋂ (n : ℕ) (hnN : n ≤ Nε.1), s n Nε.2) :=
begin
  refine (has_basis_infi hbasis).to_has_basis _ _,
  { rintros ⟨I, ε⟩ ⟨hI, hε⟩,
    refine ⟨⟨Sup I, Inf (insert 1 $ ε '' I)⟩, ⟨_, _⟩⟩,
    { rw ((hI.image _).insert _).lt_cInf_iff (insert_nonempty _ _),
      simpa using hε },
    { intros f hf,
      rw mem_Inter₂ at hf,
      exact mem_bInter (λ i hi, hs _ (cInf_le ((hI.image _).insert _).bdd_below 
        (or.inr $ mem_image_of_mem _ hi)) (hf i $ le_cSup hI.bdd_above hi)) } },
  { rintros ⟨N, ε⟩ hε,
    exact ⟨⟨Iic N, const ℕ ε⟩, ⟨finite_Iic _, λ _ _, hε⟩, λ f, id⟩ }
end

end filter