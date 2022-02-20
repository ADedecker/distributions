import order.filter.bases
import data.nat.interval
import data.nat.lattice
import data.real.basic

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

#check has_basis_infi

--lemma has_basis_infi_Prop {α : Type*} {ι : Prop} {ι' : ι → Type*} {l : ι → filter α}
--  {p : Π i, ι' i → Prop} {s : Π i, ι' i → set α} (hl : ∀ i, (l i).has_basis (p i) (s i)) :
--  (⨅ i, l i).has_basis (λ f : Π i, ι' i, ∀ i, p i (f i))
--    (λ f : Π i, ι' i, ⋂ i, s i (f i)) :=
--⟨begin
--  by_cases i : ι,
--  { simp_rw [eq_true_intro i, infi_true],
--    simp,
--    sorry },
--  { simp_rw [eq_false_intro i],
--    simp,
--    sorry }
--end

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

--lemma has_basis_infi'' {ι : Type*} {α : Type*} {ι' : ι → Type*} [decidable_eq ι] [hn : nonempty ι] 
--  {l : ι → filter α} {p : Π i, ι' i → Prop} {s : Π i, ι' i → set α} 
--  (hl : ∀ i, (l i).has_basis (p i) (s i)) :
--  (⨅ i, l i).has_basis (λ If : finset ι × Π i, ι' i, If.1.nonempty ∧ ∀ i ∈ If.1, p i (If.2 i))
--    (λ If : finset ι × Π i, ι' i, ⋂ i ∈ If.1, s i (If.2 i)) :=
--begin
--  let u := hn.some,
--  refine (has_basis_infi' hl).to_has_basis _ _,
--  { rintros ⟨I, f⟩ hf,
--    refine ⟨⟨insert u I, f⟩, ⟨finset.insert_nonempty _ _, _⟩, _⟩, },
--  { sorry }
--end

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

--lemma has_basis_infi_of_monotone' {ι ι' α : Sort*} [semilattice_inf ι'] {f : ι → filter α}
--  {p : ι' → Prop} {s : ι → ι' → set α} (hbasis : ∀ i, (f i).has_basis p (s i)) 
--  (hmono : ∀ i, monotone (s i)) 
--  (hstable : ∀ (I' : finset ι') (h : I'.nonempty), (∀ i' ∈ I', p i') → p (I'.inf' h id)):
--  (⨅ i, f i).has_basis (λ Ii' : finset ι × ι', p Ii'.2) 
--    (λ Ii', ⋂ i ∈ Ii'.1, s i Ii'.2) :=
--begin
--  refine (has_basis_infi' hbasis).to_has_basis _ _,
--  { rintros ⟨I, f⟩ hf,
--    by_cases h : I.nonempty,
--    { refine ⟨⟨I, I.inf' h f⟩, _⟩,
--      rw [subset_Inter₂_iff],
--      intros i hi,
--      exact Inter_subset_of_subset i (Inter_subset_of_subset hi $ hmono i $ binfi_le' i hi) },
--    sorry, },
--  { rintros ⟨I, i'⟩ ⟨hI, hi'⟩,
--    refine ⟨⟨I, const ι i'⟩, ⟨hI, λ _ _, hi'⟩, _⟩,
--    rw [subset_Inter₂_iff],
--    intros i hi,
--    exact Inter_subset_of_subset i (Inter_subset_of_subset hi $ by refl) }
--end

--lemma has_basis_infi_of_monotone {ι ι' α : Sort*} [complete_semilattice_Inf ι'] {f : ι → filter α}
--  {p : ι' → Prop} {s : ι → ι' → set α} (hbasis : ∀ i, (f i).has_basis p (s i)) 
--  (hmono : ∀ i, monotone (s i)) (hstable : ∀ I' : set ι', (∀ i' ∈ I', p i') → p (Inf I')):
--  (⨅ i, f i).has_basis (λ Ii' : set ι × ι', Ii'.fst.finite ∧ p Ii'.2) 
--    (λ Ii', ⋂ i ∈ Ii'.1, s i Ii'.2) :=
--begin
--  refine (has_basis_infi hbasis).to_has_basis _ _,
--  { rintros ⟨I, f⟩ ⟨hI, hf⟩,
--    refine ⟨⟨I, ⨅ i ∈ I, f i⟩, 
--      ⟨hI, hstable _ $ forall_range_iff.mpr $ λ i, hstable _ (forall_range_iff.mpr $ hf i)⟩, _⟩,
--    rw [subset_Inter₂_iff],
--    intros i hi,
--    exact Inter_subset_of_subset i (Inter_subset_of_subset hi $ hmono i $ binfi_le' i hi) },
--  { rintros ⟨I, i'⟩ ⟨hI, hi'⟩,
--    refine ⟨⟨I, const ι i'⟩, ⟨hI, λ _ _, hi'⟩, _⟩,
--    rw [subset_Inter₂_iff],
--    intros i hi,
--    exact Inter_subset_of_subset i (Inter_subset_of_subset hi $ by refl) }
--end
--
--lemma has_basis_infi_nat_of_monotone {ι' α : Sort*} [complete_semilattice_Inf ι'] {f : ℕ → filter α}
--  {p : ι' → Prop} {s : ℕ → ι' → set α} (hbasis : ∀ n, (f n).has_basis p (s n)) 
--  (hmono : ∀ n, monotone (s n)) (hstable : ∀ I' : set ι', (∀ i' ∈ I', p i') → p (Inf I')):
--  (⨅ i, f i).has_basis (λ ni' : ℕ × ι', p ni'.2) 
--    (λ ni', ⋂ i ≤ ni'.1, s i ni'.2) :=
--begin
--  refine (has_basis_infi_of_monotone hbasis hmono hstable).to_has_basis _ _,
--  { rintros ⟨S, i'⟩ ⟨hS, hp⟩,
--    refine ⟨⟨Sup S, i'⟩, ⟨hp, _⟩⟩,
--    rw [subset_Inter₂_iff],
--    intros i hi,
--    exact Inter_subset_of_subset i 
--      (Inter_subset_of_subset (le_cSup hS.bdd_above hi) $ subset_refl _) },
--  { rintros ⟨n, i'⟩ hi',
--    exact ⟨⟨Iic n, i'⟩, ⟨finite_Iic _, hi'⟩, subset_refl _⟩ },
--end

--lemma has_basis_metric_infi {ι α : Sort*} {ds : ι → pseudo_metric_space α} {x : α} : 
--  (@nhds α (⨅ (i : ι), (ds i).to_uniform_space.to_topological_space) x).has_basis
--  (λ Iε : set ι × ℝ, Iε.1.finite ∧ 0 < Iε.2) (λ Iε, ⋂ i ∈ Iε.1, @metric.ball α (ds i) x Iε.2) :=
--begin
--  rw nhds_infi,
--  refine (has_basis_infi $ λ i, @metric.nhds_basis_ball α (ds i) x).to_has_basis _ _,
--  sorry,
--end
--
--lemma has_basis_metric_induced {α β : Sort*} [d : pseudo_metric_space β] (f : α → β) {x : α} : 
--  (@nhds α (d.induced f).to_uniform_space.to_topological_space x).has_basis
--  (λ ε : ℝ, 0 < ε) (λ ε, f ⁻¹' (metric.ball (f x) ε)) :=
--begin
--  sorry,
--end

end filter