import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.Contrib.OneProof.SmoothRegular.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.NumberField.CMField

/-!
# smooth-regular, scratch: nonsingular forms of `WeierstrassAbVar` and `CMAbVarExists`

These two existence-form leaves live on other task branches (not on base e22df37c):
* `HcmPrinted.WeierstrassAbVar` (origin/wip/hcm-g1 f4f7d8db, `ZInQKernel/Contrib/OneProof/ShimuraMainCMPrinted.lean`
  l. 556-576; also origin/wip/hcm-printed);
* `MainCMPolar.CMAbVarExists` (origin/wip/cm-primitive 646e706c, `ZInQKernel/Contrib/OneProof/MainCMPolar.lean`
  l. 499-522).
Their statements and the definitions they use that are not on the base (`lat1`, `cmVec`, `cmLat`, `IsOLattice`,
`IsRiemannDatum`) are copied verbatim below (namespaces kept as sections here); `CPts`, `IsUniformization`,
`cEvalAt` are the base's `ZInQ.LeafPush2` definitions, which the branch files also use.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt)
open ZInQ.Contrib.SmoothRegular

namespace HcmPrinted

/-- `Λ ⊂ ℂ` as a lattice in `ℂ¹ = Fin 1 → ℂ`. -/
def lat1 (P : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  P.lattice.comap (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 1 => ℂ) 0)

/-- verbatim copy (origin/wip/hcm-g1) -/
def WeierstrassAbVar : Prop :=
  ∀ P : PeriodPair, ∃ (A : PkgI3.AbVar ℂ) (θ : (Fin 1 → ℂ) → CPts A (RingHom.id ℂ))
    (U : A.X.left.Opens) (x y : Γ(A.X.left, U)),
    A.dim = ((1 : ℕ) : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (lat1 P) θ ∧
    ∀ z : Fin 1 → ℂ, (⊤ ≤ (θ z).left ⁻¹ᵁ U ↔ z 0 ∉ P.lattice) ∧
      (z 0 ∉ P.lattice → cEvalAt (θ z) U x = P.weierstrassP (z 0) ∧
        cEvalAt (θ z) U y = P.derivWeierstrassP (z 0))

/-- **LEAF (textbook) `WeierstrassAbVar`, nonsingular form.** For every lattice `Λ` there is a proper, geometrically
integral group scheme `X/ℂ` that is nonsingular (its local rings at closed points are regular), with the
uniformization and Weierstrass coordinates of `WeierstrassAbVar` for the abelian variety it is
(`abVarOfNonsingular`; only `X` and its group law are data). Print: `E_Λ : y²z = 4x³ − g₂xz² − g₃z³` is a nonsingular
projective cubic (Silverman III.1.4 with `Δ ≠ 0`, VI.3.6), an elliptic curve with its group law (III.2-3), and
`z ↦ [℘(z), ℘'(z), 1]` is a complex analytic isomorphism `ℂ/Λ ≅ E_Λ(ℂ)` (VI.3.6(b)). Numbers UNVERIFIED. -/
def WeierstrassAbVarNonsingular : Prop :=
  ∀ P : PeriodPair, ∃ (X : Over (Spec (CommRingCat.of ℂ))) (_ : GrpObj X) (_ : IsProper X.hom)
    (_ : GeometricallyIntegral X.hom) (hX : Nonsingular X.hom),
    ∃ (θ : (Fin 1 → ℂ) → CPts (abVarOfNonsingular X hX) (RingHom.id ℂ))
    (U : (abVarOfNonsingular X hX).X.left.Opens) (x y : Γ((abVarOfNonsingular X hX).X.left, U)),
    (abVarOfNonsingular X hX).dim = ((1 : ℕ) : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (lat1 P) θ ∧
    ∀ z : Fin 1 → ℂ, (⊤ ≤ (θ z).left ⁻¹ᵁ U ↔ z 0 ∉ P.lattice) ∧
      (z 0 ∉ P.lattice → cEvalAt (θ z) U x = P.weierstrassP (z 0) ∧
        cEvalAt (θ z) U y = P.derivWeierstrassP (z 0))

theorem weierstrassAbVar_of_nonsingular (h : WeierstrassAbVarNonsingular) : WeierstrassAbVar := by
  intro P
  obtain ⟨X, _, _, _, hX, H⟩ := h P
  exact ⟨abVarOfNonsingular X hX, H⟩

theorem weierstrassAbVarNonsingular_of_weierstrassAbVar (h : WeierstrassAbVar) :
    WeierstrassAbVarNonsingular := fun P ↦
  (exists_abVar_iff_nonsingular (K := ℂ) _).1 (h P)

end HcmPrinted

namespace MainCMPolar

section Defs

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

/-- verbatim copy (QMRecPrinted.cmVec) -/
def cmVec (Φ : Fin g → E →+* ℂ) : E →+ (Fin g → ℂ) where
  toFun x i := Φ i x
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

/-- verbatim copy (QMRecPrinted.cmLat) -/
def cmLat (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) : Submodule ℤ (Fin g → ℂ) :=
  (𝔞.map (cmVec Φ)).toIntSubmodule

/-- verbatim copy -/
def IsOLattice (𝔞 : AddSubgroup E) : Prop :=
  (∀ o : 𝓞 E, ∀ x ∈ 𝔞, (o : E) * x ∈ 𝔞) ∧
  (∃ c : ℕ, 0 < c ∧ ∀ o : 𝓞 E, (c : E) * o ∈ 𝔞) ∧
  (∃ d : ℕ, 0 < d ∧ ∀ x ∈ 𝔞, IsIntegral ℤ ((d : E) * x))

variable [IsCMField E]

/-- verbatim copy -/
def IsRiemannDatum {g : ℕ} (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) (ζ : E) : Prop :=
  IsCMField.complexConj E ζ = -ζ ∧ (∀ i, 0 < (Φ i ζ).im) ∧
  ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (ζ * x * IsCMField.complexConj E y) = n

end Defs

/-- verbatim copy (origin/wip/cm-primitive) -/
def CMAbVarExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ 𝔟 : AddSubgroup E, IsOLattice 𝔟 → (∃ ζ : E, IsRiemannDatum Φ 𝔟 ζ) →
  ∃ (B : PkgI3.AbVar ℂ) (θ : (Fin g → ℂ) → CPts B (RingHom.id ℂ)),
    B.dim = (g : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔟) θ

/-- **LEAF `CMAbVarExists`, nonsingular form.** As `CMAbVarExists`, with the abelian variety given as a proper,
geometrically integral group scheme `X/ℂ` that is nonsingular (regular local rings at closed points). Print:
Shimura 1998 §6.2 Thm 4 / Shimura–Taniyama 1961 §6.2 Thm 4 (an abelian variety `A` with `ℂ^g/Φ(𝔞) ≅ A(ℂ)`), and
Riemann's theorem (Mumford, *Abelian varieties*, §3: a complex torus with a Riemann form is a complete nonsingular
projective variety, with §4 for the group variety); numbers UNVERIFIED. -/
def CMAbVarExistsNonsingular : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ 𝔟 : AddSubgroup E, IsOLattice 𝔟 → (∃ ζ : E, IsRiemannDatum Φ 𝔟 ζ) →
  ∃ (X : Over (Spec (CommRingCat.of ℂ))) (_ : GrpObj X) (_ : IsProper X.hom)
    (_ : GeometricallyIntegral X.hom) (hX : Nonsingular X.hom),
  ∃ θ : (Fin g → ℂ) → CPts (abVarOfNonsingular X hX) (RingHom.id ℂ),
    (abVarOfNonsingular X hX).dim = (g : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔟) θ

theorem cmAbVarExists_of_nonsingular (h : CMAbVarExistsNonsingular) : CMAbVarExists := by
  intro E _ _ _ g Φ hd hi 𝔟 hO hζ
  obtain ⟨X, _, _, _, hX, H⟩ := h E g Φ hd hi 𝔟 hO hζ
  exact ⟨abVarOfNonsingular X hX, H⟩

theorem cmAbVarExistsNonsingular_of_cmAbVarExists (h : CMAbVarExists) : CMAbVarExistsNonsingular := by
  intro E _ _ _ g Φ hd hi 𝔟 hO hζ
  exact (exists_abVar_iff_nonsingular (K := ℂ) _).1 (h E g Φ hd hi 𝔟 hO hζ)

end MainCMPolar

#print axioms HcmPrinted.weierstrassAbVar_of_nonsingular
#print axioms HcmPrinted.weierstrassAbVarNonsingular_of_weierstrassAbVar
#print axioms MainCMPolar.cmAbVarExists_of_nonsingular
#print axioms MainCMPolar.cmAbVarExistsNonsingular_of_cmAbVarExists
