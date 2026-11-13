import ZInQKernel.Contrib.BrauerT14T15.LocalT15
import ZInQKernel.Contrib.BrauerT14T15.Real

/-!
# Leaf T15 (I6.2c′, `PkgI6.LocalH2CardC`), proved

`PkgI6.LocalH2CardC` (`ZInQKernel/HDecomp/Conductor/I6Base.lean`) asks that `H²(G_{ℚ_p}, ℤ/2)`
for every prime `p`, and `H²(G_ℝ, ℤ/2)`, have exactly two classes, on continuous inhomogeneous
cochains (`PkgI6.H2TwoClasses`).

* finite places: `h2TwoClasses_padic` (`LocalT15.lean`), from Tau Ceti's local invariant
  `Br ℚ_p ≃+ ℚ/ℤ` and the degree-two Kummer bridge on cochains (`Kummer2.lean`);
* the real place: `Real.h2TwoClasses_real` (`Real.lean`), `G_ℝ` having order two.
-/

namespace ZInQ.Contrib.BrauerT14T15

/-- **Leaf T15 (`PkgI6.LocalH2CardC`), proved.** -/
theorem localH2CardC : PkgI6.LocalH2CardC :=
  ⟨fun p _ => h2TwoClasses_padic p, Real.h2TwoClasses_real⟩

end ZInQ.Contrib.BrauerT14T15
