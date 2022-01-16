import topology.algebra.module.basic

section lattice_ops 

section mul

variables {ι X : Type*} [has_mul X] {ts : set (topological_space X)} 
  [h : Π t ∈ ts, @has_continuous_mul X t _] {ts' : ι → topological_space X}
  [h' : Π i, @has_continuous_mul X (ts' i) _]

@[to_additive, priority 100] instance has_continuous_mul_Inf : @has_continuous_mul X (Inf ts) _ :=
{ continuous_mul := continuous_Inf_rng (λ t ht, continuous_Inf_dom₂ ht ht 
  (@has_continuous_mul.continuous_mul X t _ (h t ht))) }

include h'

@[to_additive, priority 100] instance has_continuous_mul_infi : @has_continuous_mul X (⨅ i, ts' i) _ :=
by {rw ← Inf_range, exact @has_continuous_mul_Inf _ _ _ (set.forall_range_iff.mpr h')}

omit h'

end mul

section topological_group

variables {ι G : Type*} [group G] {ts : set (topological_space G)} 
  [h : Π t ∈ ts, @topological_group G t _] {ts' : ι → topological_space G}
  [h' : Π i, @topological_group G (ts' i) _]

@[to_additive, priority 100] instance topological_group_Inf : @topological_group G (Inf ts) _ :=
{ continuous_inv := continuous_Inf_rng (λ t ht, continuous_Inf_dom ht
    (@topological_group.continuous_inv G t _ (h t ht))),
  continuous_mul := @has_continuous_mul.continuous_mul G (Inf ts) _ 
    (@has_continuous_mul_Inf _ _ _ 
      (λ t ht, @topological_group.to_has_continuous_mul G t _ (h t ht))) }

include h'

@[to_additive, priority 100] instance topological_group_infi : @topological_group G (⨅ i, ts' i) _ :=
by {rw ← Inf_range, exact @topological_group_Inf G _ (set.range ts') (set.forall_range_iff.mpr h')}

omit h'

end topological_group

section smul

variables {ι K E : Type*} [u : topological_space K] [has_scalar K E] 
  {ts : set (topological_space E)} [h : Π t ∈ ts, @has_continuous_smul K E _ _ t]
  {ts' : ι → topological_space E} [h' : Π i, @has_continuous_smul K E _ _ (ts' i)]

include h

@[to_additive, priority 100] instance has_continuous_smul_Inf : @has_continuous_smul K E _ u (Inf ts) :=
{ continuous_smul := 
  begin
    rw ← @Inf_singleton _ _ u,
    exact continuous_Inf_rng (λ t ht, continuous_Inf_dom₂ (eq.refl u) ht 
      (@has_continuous_smul.continuous_smul _ _ _ u t (h t ht)))
  end }

omit h

include h'

@[to_additive, priority 100] instance has_continuous_smul_infi : @has_continuous_smul K E _ u (⨅ i, ts' i) :=
by {rw ← Inf_range, 
    exact @has_continuous_smul_Inf K E _ _ (set.range ts') (set.forall_range_iff.mpr h')}

omit h'

end smul

end lattice_ops