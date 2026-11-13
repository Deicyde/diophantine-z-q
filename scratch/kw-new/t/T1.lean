import ZInQKernel.Contrib.TauCeti.Backport.Topology.Algebra.ContinuousMonoidHom.Basic
#check @ContinuousMonoidHom.subgroupComap
#print axioms ContinuousMonoidHom.subgroupComap
example {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] (ψ : H →ₜ* G) (U : Subgroup G) := ψ.subgroupComap U
