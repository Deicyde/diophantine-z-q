import ZInQKernel.Contrib.SkolemNoether.Basic
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.Descent.B1Quat

/-!
# Connecting the full Skolem–Noether proof to the actual descent consumers

These closed theorems use the existing predicates and quaternion algebra without
changing their definitions. They discharge the Skolem–Noether input of B1 only;
they do not construct the abelian surface or close the whole H assembly.
-/

namespace ZInQ.Contrib.SkolemNoether

/-- The full theorem inhabits the existing pkg-I6 leaf exactly. -/
theorem pkgI6SkolemNoether : PkgI6.SkolemNoether := t13

/-- The existing automorphism-case descent predicate follows from full T13. -/
theorem descentLeafSkolemNoether : GlueDescent.LeafSkolemNoether := by
  intro K _ A _ _ _ _ _ φ
  exact exists_unit_conj_of_algEquiv K φ

/-- B1 for the actual discriminant-six quaternion algebra, with no leaf hypothesis. -/
theorem B6_inner_closed (φ : GlueDescent.B6 ≃ₐ[ℚ] GlueDescent.B6) :
    ∃ u : GlueDescent.B6ˣ, ∀ a : GlueDescent.B6, φ a = u * a * (u⁻¹ : GlueDescent.B6ˣ) :=
  GlueDescent.B6_inner descentLeafSkolemNoether φ

end ZInQ.Contrib.SkolemNoether
