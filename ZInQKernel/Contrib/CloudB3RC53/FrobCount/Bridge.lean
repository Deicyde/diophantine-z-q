import ZInQKernel.Contrib.CloudB3RC53.FrobCount.CentralCount

/-!
# The central Frobenius determinants: bridge from the count version

`PairedFunctional/CentralDeterminants.lean` states the conclusion
`det(Φ − 1) ≠ 0 ∧ det(Φ − r) ≠ 0` for `Φ ∈ M₂(ℤ)` with `det Φ = r`, under `2 ≤ r` and the Hasse
hypothesis `(tr Φ)² ≤ 4r` (`CentralFrobeniusDeterminantsNonzero`). This file gives the same
conclusion, `CentralFrobeniusDeterminantsAt Φ r`, from the point-count version of
`CentralCount.lean`, with no Hasse hypothesis and no lower bound on `r`, so that consumers can
switch:

* `centralFrobeniusDeterminantsAt_of_count` (PROVED): if `det Φ = r`, `r = |k|` for a finite field
  `k`, and `tr Φ = ±(r + 1 − |W(k)|)` for a Weierstrass curve `W` over `k`, then
  `CentralFrobeniusDeterminantsAt Φ r`.
* `centralFrobeniusDeterminantsAt_of_hasse` (PROVED): the old conclusion, in the same form, from
  the old hypotheses (`centralFrobeniusDeterminantsNonzero_proof`), for comparison.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.FrobCount

open Matrix WeierstrassCurve.Affine
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (CentralFrobeniusDeterminantsNonzero
  centralFrobeniusDeterminantsNonzero_proof)

/-- The conclusion of `PairedFunctional.CentralFrobeniusDeterminantsNonzero` at one `(Φ, r)`. -/
def CentralFrobeniusDeterminantsAt (Φ : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ) : Prop :=
  (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 ∧
    (Φ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0

/-- **The old conclusion from point counts** (no Hasse hypothesis). PROVED. -/
theorem centralFrobeniusDeterminantsAt_of_count (Φ : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ)
    (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve.Affine F) (hdet : Φ.det = r)
    (hr : r = Fintype.card F)
    (htr : Φ.trace = r + 1 - Nat.card (Point W) ∨ Φ.trace = -(r + 1 - Nat.card (Point W))) :
    CentralFrobeniusDeterminantsAt Φ r := by
  subst hr
  exact centralFrobeniusDeterminantsNonzeroCount_proof F W Φ hdet htr

/-- The old conclusion from the old (Hasse) hypotheses, in the same form. PROVED. -/
theorem centralFrobeniusDeterminantsAt_of_hasse (Φ : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ)
    (hdet : Φ.det = r) (hr : 2 ≤ r) (hHasse : Φ.trace ^ 2 ≤ 4 * r) :
    CentralFrobeniusDeterminantsAt Φ r :=
  centralFrobeniusDeterminantsNonzero_proof Φ r hdet hr hHasse

/-- **Non-vacuity**: the bridge applies to the companion matrix of `x² − a_r x + q` for every
Weierstrass curve over every finite field. -/
theorem centralFrobeniusDeterminantsAt_example (F : Type) [Field F] [Fintype F]
    (W : WeierstrassCurve.Affine F) :
    CentralFrobeniusDeterminantsAt
      !![0, -(Fintype.card F : ℤ); 1, (Fintype.card F : ℤ) + 1 - Nat.card (Point W)]
      (Fintype.card F) :=
  centralFrobeniusDeterminantsAt_of_count _ _ F W (centralFrobeniusCount_example W).1 rfl
    (Or.inl (centralFrobeniusCount_example W).2)

end ZInQ.Contrib.CloudB3RC53.FrobCount
