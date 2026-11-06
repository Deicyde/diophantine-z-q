import ZInQKernel.Model.Descent.Kummer
import ZInQKernel.Model.Descent.Factor
import ZInQKernel.Model.Descent.FirstImage
import ZInQKernel.Model.Descent.SecondImage
import ZInQKernel.Model.Descent.Index
import ZInQKernel.Model.Descent.MordellWeil

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
-/
