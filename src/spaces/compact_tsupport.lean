import topology.compacts
import ..tsupport

structure compact_tsupport_continuous_map (α β : Type*) [topological_space α] 
  [topological_space β] [add_monoid β] extends C(α, β) :=
(compact_tsupport : is_compact $ tsupport to_fun)

notation `Cc(` α `, ` β `)` := continuous_map α β

namespace compact_tsupport_continuous_map

def to_bounded (α β : Type*) [topological_space α]
  [metric_space β] [add_monoid β] (f : Cc(α, β)) : α →ᵇ β