import ZInQKernel.Model.Descent.Kummer
import ZInQKernel.Model.Descent.Factor
import ZInQKernel.Model.Descent.FirstImage
import ZInQKernel.Model.Descent.SecondImage
import ZInQKernel.Model.Descent.Index
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Model.Descent.PointCounts
import ZInQKernel.Model.Descent.Residue
import ZInQKernel.Model.Descent.KernelReduction
import ZInQKernel.Model.Descent.Reduction
import ZInQKernel.Model.Descent.OddTorsion
import ZInQKernel.Model.Descent.Torsion
import ZInQKernel.Model.Descent.RankOne
import ZInQKernel.Model.Descent.OddIndex

/-!
# Descent, torsion and rank of `E(K₀)`

Blueprint chapter `model/`, section `descent/` (except the coordinate change and the
certificate for `R`, which are in `ZInQKernel/Model/Field/CurveC.lean`).

* `Descent/Kummer.lean`: the Kummer map, the two-isogeny and the rescaling for
  `y² = x³ + b x` over any field; the homomorphism property, the kernel theorem and
  `λ ∘ φ ∘ φ = [2]`.
* `Descent/Factor.lean`: unique factorization in `ℤ[√2]` and valuations on the curves.
* `Descent/FirstImage.lean`, `Descent/SecondImage.lean`: the two descent images.
* `Descent/Index.lean`: `[E(K₀) : 2E(K₀)] = 8`.
* `Descent/MordellWeil.lean`: `E(K₀)` is finitely generated (`mordellWeilE : MordellWeilE`).
* `Descent/PointCounts.lean`: `#Ẽ(𝔽₁₇) = 20`, `#Ẽ(𝔽₂₃) = 24`.
* `Descent/Residue.lean`, `Descent/KernelReduction.lean`, `Descent/Reduction.lean`: reduction
  modulo a prime of degree one is a homomorphism, injective on prime-to-`p` torsion.
* `Descent/OddTorsion.lean`: no odd torsion (reduction modulo `(17, s - 6)` and `(23, s - 5)`).
* `Descent/Torsion.lean`: the torsion of `E(K₀)` and `C(K₀)` is the two-torsion.
* `Descent/RankOne.lean`: `C(K₀) = ℤ S ⊕ C(K₀)[2]`.
* `Descent/OddIndex.lean`: `R = [m] S + T` forces `m` odd.
-/
