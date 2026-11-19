import ZInQKernel.Contrib.CloudB3RC53.Duality.CupPairing
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Descent
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant

/-!
# Duality area: the local Kummer condition is its exact annihilator

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, tex L3413–3468. For the actual
local twist `B = E^{(h)}` over `F = K_v` the lemma asserts that the Kummer image is its exact
local annihilator (tex L3423), and proves it (tex L3439–3443):

> The local finite dualities [Milne, I.2.3, I.3.2–I.3.5] make the Kummer map adjoint to
> `H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image
> is its exact annihilator.

Genuine objects:
* `localWeilCup`: the cup product `H¹(F, B[m]) × H¹(F, B[m]) → H²(F, μ_m)` through the Weil
  pairing (`CupPairing.lean`, `WeierstrassCurve.torsionCoeffWeilPairing`);
* `localTatePairing`: its composite with `H²(F, μ_m) → H²(F, (Fˢ)ˣ) = Br F` and the local
  invariant `inv_F : Br F ≃ ℚ/ℤ` — the local duality pairing on `H¹(F, B[m])` of Milne I.2.3
  (with `B[m]` self-dual through `e_m`);
* `WeierstrassCurve.kummerMap`: the genuine Kummer map `B(F) → H¹(F, B[m])`, and
  `kummerProj`: `H¹(F, B[m]) → H¹(F, B)`, whose kernel is the Kummer image
  (`WeierstrassCurve.range_kummerMap`).

* `MilneLocalTateDualityKummer` (PRINT; locators checked against the ADT PDF (I.2.3 p. 28;
  I.3.2 p. 41, diagram pp. 41–43; I.3.4 p. 43; I.3.5 p. 44); Milne, *Arithmetic Duality Theorems*,
  I.3.2–I.3.5, as cited at tex L3439–3441): Tate's local duality pairing
  `B(F) × H¹(F, B) → ℚ/ℤ` is nondegenerate on `H¹(F, B)`, and the Kummer map is adjoint to
  `H¹(F, B[m]) → H¹(F, B)` for it and the local duality pairing on `H¹(F, B[m])`. The library
  has no Tate pairing `B(F) × H¹(F, B) → ℚ/ℤ`, so it enters as data: the print says one exists
  with the printed properties (its sign convention absorbed in it). The type allows every
  nonarchimedean local field; Milne's I.3 is stated for `p`-adic fields, and the version in that
  scope (`[CharZero F]`) is `MilneLocalTateDualityKummerCharZero` in `LocalKummerChar0.lean`, with
  the lemma `KummerAnnihilatorNodeCharZero` and the bridge `kummerAnnihilatorNodeCharZero_of_print`.
* `KummerAnnihilatorNode` (PROVED, `kummerAnnihilatorNode_proof`): from the print, the Kummer
  image equals its annihilator under `localTatePairing`.

**ELLIOT** (tex L3443–3450, the integral chain statement): the derived-category step ("the
restricted cup map `M[-1] ⊗^L M[-1] → ℤ₂[-2]` has homotopy class determined by
`Hom(M ⊗ M, ℤ₂)`") needs the derived category of `ℤ₂`-modules, which is not developed in the
library. The elementary steps — finite isotropy kills a `ℤ₂`-valued bilinear map
(`bilinear_eq_zero_of_forall_dvd`) and torsion maps trivially to `ℤ₂`
(`addMonoidHom_eq_zero_of_isTorsion`) — are PROVED here.
-/

set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

section Pairing

variable {F : Type} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : F))

/-- The cup product `H¹(F, B[m]) × H¹(F, B[m]) → H²(F, μ_m)` through the Weil pairing `e_m`. -/
noncomputable def localWeilCup :
    H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+
      H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+
        H2 (AbsoluteGaloisGroup F) (KummerCoeff F m) :=
  cupH (W.torsionCoeffWeilPairing m hm)
    (fun σ P Q => W.torsionCoeffWeilPairing_smul m hm σ P Q)

/-- The map `H²(F, μ_m) → H²(F, (Fˢ)ˣ) = Br F`. -/
noncomputable def kummerToBr : H2 (AbsoluteGaloisGroup F) (KummerCoeff F m) →+ Br F :=
  (unitsRepH2Equiv F).toAddMonoidHom.comp
    (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F m) (kummerCoeffInclHom F m)
      continuous_of_discreteTopology)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **The local duality pairing on `H¹(F, B[m])`** (Milne I.2.3 with `B[m]` self-dual through
the Weil pairing): `⟨x, y⟩ = inv_F (x ∪_{e_m} y)`. -/
noncomputable def localTatePairing :
    H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+
      H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+ AddCircle (1 : ℚ) :=
  (AddMonoidHom.compHom ((invMap F).toAddMonoidHom.comp (kummerToBr m))).comp
    (localWeilCup W m hm)

end Pairing

section Kummer

variable {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : F))

/-- The map `H¹(F, B[m]) → H¹(F, B)` induced by `B[m] ⊂ B`. -/
noncomputable def kummerProj :
    H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+ H1 (AbsoluteGaloisGroup F) W.PointCoeff :=
  explicitCoeff1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) (W.torsionCoeffIncl m)
    continuous_of_discreteTopology

theorem kummerProj_kummerMap (P : W.toAffine.Point) :
    kummerProj W m (W.kummerMap m hm P) = 0 := by
  have h : W.kummerMap m hm P ∈ (W.kummerMap m hm).range := ⟨P, rfl⟩
  rw [W.range_kummerMap m hm] at h
  exact h

/-- **Abstract annihilator lemma** (tex L3439–3443). If a biadditive `pair` on `H¹(F, B[m])`
satisfies `pair (δ P) y = tate P (π y)` for a pairing `tate` that is nondegenerate on the image
of `π` in its second variable, then the Kummer image is its own annihilator. -/
theorem mem_range_kummerMap_iff {A : Type*} [AddCommGroup A]
    (pair : H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+
      H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m) →+ A)
    (tate : W.toAffine.Point →+ H1 (AbsoluteGaloisGroup F) W.PointCoeff →+ A)
    (hadj : ∀ P y, pair (W.kummerMap m hm P) y = tate P (kummerProj W m y))
    (hperf : ∀ y, (∀ P, tate P (kummerProj W m y) = 0) → kummerProj W m y = 0)
    (y : H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff m)) :
    y ∈ (W.kummerMap m hm).range ↔ ∀ x ∈ (W.kummerMap m hm).range, pair x y = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩ x ⟨P, rfl⟩
    rw [hadj, kummerProj_kummerMap W m hm, map_zero]
  · intro h
    rw [W.range_kummerMap m hm]
    exact hperf y fun P => (hadj P y) ▸ h _ ⟨P, rfl⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **PRINT** (locators checked against the ADT PDF (I.2.3 p. 28; I.3.2 p. 41, diagram pp. 41–43;
I.3.4 p. 43; I.3.5 p. 44); Milne, *Arithmetic Duality Theorems*, I.3.2–I.3.5, as cited at tex
L3439–3441): for an elliptic curve `B` over a nonarchimedean local field `F` and `m` invertible
in `F`, Tate's local duality pairing `B(F) × H¹(F, B) → ℚ/ℤ` is nondegenerate on `H¹(F, B)`
(Milne I.3.4; used on `H¹(F, B)[m]`), and the Kummer map is adjoint to `H¹(F, B[m]) → H¹(F, B)`
for it and the local duality pairing `localTatePairing` on `H¹(F, B[m])` (Milne I.2.3, I.3.2,
I.3.5; up to the sign absorbed in the Tate pairing). Milne states I.3 for `p`-adic fields; the
quantified version in that scope is `MilneLocalTateDualityKummerCharZero`
(`LocalKummerChar0.lean`). -/
structure MilneLocalTateDualityKummer : Prop where
  out : ∃ tate : W.toAffine.Point →+ H1 (AbsoluteGaloisGroup F) W.PointCoeff →+
      AddCircle (1 : ℚ),
    (∀ P y, localTatePairing W m hm (W.kummerMap m hm P) y = tate P (kummerProj W m y)) ∧
    (∀ y : H1 (AbsoluteGaloisGroup F) W.PointCoeff, m • y = 0 → (∀ P, tate P y = 0) → y = 0)

end Kummer

/-- **The Kummer image is its exact local annihilator** (Lemma `ex:arith-local-kummer`, tex
L3423, L3439–3443). For an elliptic curve `B` over a nonarchimedean local field `F` (here the
actual local twist `E^{(h)}` over `K_v`) and `m` invertible in `F` (`m = 2^a`), given the printed
local Tate duality `MilneLocalTateDualityKummer`, a class `y ∈ H¹(F, B[m])` lies in the Kummer
image iff it is orthogonal to the Kummer image under the local duality pairing
`⟨x, y⟩ = inv_F (x ∪_{e_m} y)`. -/
def KummerAnnihilatorNode : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ)
    (hm : IsUnit (m : F)), MilneLocalTateDualityKummer B m hm →
    ∀ y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff m),
      y ∈ (B.kummerMap m hm).range ↔
        ∀ x ∈ (B.kummerMap m hm).range, localTatePairing B m hm x y = 0

theorem kummerAnnihilatorNode_proof : KummerAnnihilatorNode := by
  intro F _ _ _ _ _ B _ m hm hMilne y
  obtain ⟨tate, hadj, hperf⟩ := hMilne.out
  refine mem_range_kummerMap_iff B m hm (localTatePairing B m hm) tate hadj
    (fun y hy => hperf _ ?_ hy) y
  rw [← map_nsmul]
  have hkill : ∀ P : B.TorsionCoeff m, m • P = 0 := fun P =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp P.2)
  rw [nsmul_H1_eq_zero hkill y, map_zero]

/-! ### The integral isotropy step (tex L3443–3448), elementary part -/

/-- A `ℤ₂`-valued biadditive map all of whose values are divisible by every power of two is
zero ("finite isotropy makes every value divisible by every power of two, hence zero"). -/
theorem bilinear_eq_zero_of_forall_dvd {M : Type*} [AddCommGroup M]
    (β : M →+ M →+ ℤ_[2]) (h : ∀ (a : ℕ) x y, (2 : ℤ_[2]) ^ a ∣ β x y) : β = 0 := by
  refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun y => ?_
  rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
  by_contra hne
  have hd := h ((β x y).valuation + 1) x y
  rw [← Ideal.mem_span_singleton] at hd
  have hd' : β x y ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ ((β x y).valuation + 1)} := by
    exact_mod_cast hd
  rw [PadicInt.mem_span_pow_iff_le_valuation _ hne] at hd'
  omega

/-- An additive map from a torsion group to `ℤ₂` is zero (the torsion of `M = B(F)^∧₂` does not
contribute to `Hom(M ⊗ M, ℤ₂)`). -/
theorem addMonoidHom_eq_zero_of_isTorsion {T : Type*} [AddCommGroup T]
    (hT : IsAddTorsion T) (f : T →+ ℤ_[2]) : f = 0 := by
  ext t
  obtain ⟨n, hn, hnt⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).1 (hT t)
  have h : (n : ℤ_[2]) * f t = 0 := by rw [← nsmul_eq_mul, ← map_nsmul, hnt, map_zero]
  have hn' : (n : ℤ_[2]) ≠ 0 := by exact_mod_cast hn.ne'
  simpa [hn'] using h

end ZInQ.Contrib.CloudB3RC53.Duality
