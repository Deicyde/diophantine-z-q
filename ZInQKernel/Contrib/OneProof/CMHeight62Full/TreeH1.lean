import ZInQKernel.Contrib.OneProof.JDescent3FunctionField
import ZInQKernel.Contrib.OneProof.JDescent4Genus
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.ModelOrigin
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.OneProof.CMHeight62Full.HodgeLineGlue
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# cmHeight62 (finite place), tree wiring: the generic stalk is a discrete valuation ring (H1)

* **Abstract core.** If the image of a domain `S` in its fraction field `F` is the valuation ring
  of a place `P` of `F/k`, then `S ≅ 𝒪_P` (`ringEquivIntegersOfRangeEq`), so `S` is a discrete
  valuation ring, and so is every ring isomorphic to `S`.
* **The identity place of `E_L`.** `identityPlace L hdim` is the place of
  `abVar_identityPoleSpaces` for the base change `E_L` (of dimension one by
  `PkgI3.AbVar.dim_baseChange`): degree one, valuation ring the image of the stalk at the
  identity, and `dim L(nP) = n` for `n ≥ 1`.
* **H1.** `genStalk_isDiscreteValuationRing`: for a group model `𝒢` of a dimension-one `E`, the
  generic stalk `𝒪_{𝒢,ξ}` is a domain and a discrete valuation ring. It is isomorphic to the stalk
  of `E_L` at the identity (`originStalkEquiv`), whose image in `K(E_L)` is `𝒪_P`.
* As a consequence, `exists_hodgeLine_of_dim_one`: at every finite place the Hodge lattice of
  `𝒢` lies on a line `𝒪_v · θ` with `θ ≠ 0`, with no instance hypothesis left.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.DefFaltings
open HDec.CMBranch.CMjBridges (AbVarFunctionField abVarIdentity abVar_identityPoleSpaces)
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv)

/-! ## Abstract core: a domain whose image is the valuation ring of a place -/

section H1Core

variable {k F S : Type*} [Field k] [Field F] [Algebra k F] [CommRing S] [Algebra S F]
  [IsFractionRing S F]

/-- If the image of a domain `S` in its fraction field `F` is the valuation ring of a place `P`,
then `S ≅ 𝒪_P`, through the algebra map. -/
def ringEquivIntegersOfRangeEq (P : TauCeti.Place k F)
    (hP : (algebraMap S F).range = P.integers.toSubring) : S ≃+* P.integers :=
  RingEquiv.ofBijective
    ((algebraMap S F).codRestrict P.integers.toSubring (fun a => hP ▸ ⟨a, rfl⟩))
    ⟨fun _ _ hab => IsFractionRing.injective S F (congrArg Subtype.val hab),
      fun ⟨a, ha⟩ => by
        obtain ⟨b, hb⟩ : a ∈ (algebraMap S F).range := hP.symm ▸ ha
        exact ⟨b, Subtype.ext hb⟩⟩

theorem coe_ringEquivIntegersOfRangeEq (P : TauCeti.Place k F)
    (hP : (algebraMap S F).range = P.integers.toSubring) (a : S) :
    ((ringEquivIntegersOfRangeEq P hP a : P.integers) : F) = algebraMap S F a :=
  rfl

/-- Such a domain is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_range_eq [IsDomain S] (P : TauCeti.Place k F)
    (hP : (algebraMap S F).range = P.integers.toSubring) : IsDiscreteValuationRing S :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (ringEquivIntegersOfRangeEq P hP).symm

/-- A ring isomorphic to such a domain is a domain and a discrete valuation ring. -/
theorem exists_isDomain_isDVR_of_ringEquiv [IsDomain S] {B : Type*} [CommRing B] (e : B ≃+* S)
    (P : TauCeti.Place k F) (hP : (algebraMap S F).range = P.integers.toSubring) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  have hB : IsDomain B := MulEquiv.isDomain S e.toMulEquiv
  have := isDiscreteValuationRing_of_range_eq P hP
  exact ⟨hB, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm⟩

end H1Core

/-! ## The identity place of `E_L` and H1 -/

section Tree

attribute [local instance] HDec.CMBranch.CMjBridges.abVar_isIntegral
  HDec.CMBranch.CMjBridges.abVarFunctionFieldAlgebra

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField L] in
/-- The base change `E_L` has dimension one. -/
theorem dim_baseChange_eq_one (hdim : E.dim = 1) : (E.baseChange L).dim = 1 :=
  (PkgI3.AbVar.dim_baseChange E L).trans hdim

variable (L) in
/-- The identity place of `E_L`: the place of `abVar_identityPoleSpaces` for `E_L`. -/
def identityPlace (hdim : E.dim = 1) : TauCeti.Place L (AbVarFunctionField (E.baseChange L)) :=
  (abVar_identityPoleSpaces (E.baseChange L) (dim_baseChange_eq_one hdim)).choose

/-- The identity place has degree one, its valuation ring is the image of the stalk of `E_L` at
the identity, and `dim L(nP) = n` for `n ≥ 1`. -/
theorem identityPlace_spec (hdim : E.dim = 1) :
    (identityPlace L hdim).degree = 1 ∧
      (algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L))).range =
          (identityPlace L hdim).integers.toSubring ∧
      (∀ n : ℕ, 1 ≤ n →
        TauCeti.Divisor.dim (Finsupp.single (identityPlace L hdim) (n : ℤ) :
          TauCeti.Divisor L (AbVarFunctionField (E.baseChange L))) = n) := by
  obtain ⟨h1, h2, h3, -⟩ :=
    (abVar_identityPoleSpaces (E.baseChange L) (dim_baseChange_eq_one hdim)).choose_spec
  exact ⟨h1, h2, h3⟩

/-- `𝒪_{𝒢,ξ} ≅ 𝒪_{E_L,0}`, the target read at `abVarIdentity` (the same point as
`identityPoint`, definitionally). -/
def originEquiv (𝒢 : GroupModel E L) :
    𝒢.genStalk ≃+* (E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)) :=
  originStalkEquiv 𝒢

/-- **H1. The generic stalk `𝒪_{𝒢,ξ}` is a discrete valuation ring.** -/
theorem genStalk_isDiscreteValuationRing (𝒢 : GroupModel E L) (hdim : E.dim = 1) :
    ∃ _ : IsDomain 𝒢.genStalk, IsDiscreteValuationRing 𝒢.genStalk :=
  exists_isDomain_isDVR_of_ringEquiv (originEquiv 𝒢) (identityPlace L hdim)
    (identityPlace_spec hdim).2.1

/-- **The Hodge line at every finite place**, from H1 and the N5-bridge/N13 glue: the Hodge
lattice of `𝒢` lies on a line `𝒪_v · θ` with `θ ≠ 0`. -/
theorem exists_hodgeLine_of_dim_one (𝒢 : GroupModel E L) (hdim : E.dim = 1)
    (v : HeightOneSpectrum (𝓞 L)) :
    ∃ θ : 𝒢.hodgeSpace 1, θ ≠ 0 ∧
      ∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ := by
  obtain ⟨_, _⟩ := genStalk_isDiscreteValuationRing 𝒢 hdim
  exact exists_hodgeLine 𝒢 v

end Tree

end ZInQ.Contrib.CMHeight62Full
