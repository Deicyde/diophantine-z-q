import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.HeckeBridge
import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.RC53Assist.TateReduction.Comparison
import ZInQKernel.Contrib.RC53Assist.DetDegree.Reduction
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.BaseChange
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.PrintedInputs
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.BrauerNesbitt
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.FrobeniusLocal

/-!
# Exact newform consequence and the actual Tate representations

This module preserves the component results and the printed-corollary assembly
of the unchanged proposition `LiCarayolNewformOfModular`. That assembly uses
coefficient-field descent, the joint Shimura–Carayol Euler-factor reading, and
Faltings's local-factor rigidity; the two local-factor interfaces are labeled
GLUE below.

The earlier invariant-space representation route is not part of the Lean
declarations in this edition. Its historical statements and the multiplicative-
reduction obstruction are recorded in
`docs/research/g0-representation-route-invariants.md`. The corrected route on
inertia coinvariants is in `GlobalTrace/CoinvariantReadings.lean` and
`GlobalTrace/CoinvariantAssembly.lean`. The definition `localTatePolynomial`
is retained with its normalization warning. The printed-corollary assembly
does not use it.
-/


/-!
# The actual Tate representations used in G0

The integral representation acts on the inverse limit of the elliptic curve's
prime-power torsion over the algebraic closure of the rationals. Its rational
and extended representations are scalar extensions of precisely that action.
No independently supplied representation stands in for the Tate module.

References: Silverman, The Arithmetic of Elliptic Curves, III.7 and VII.7;
Faltings 1983, Satz 3, for the semisimplicity input used in the later assembly.
The local good-reduction trace dictionary is proved from the existing
Tate-reduction and determinant-degree comparison theorems.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion

open Module NumberField IsDedekindDomain
open scoped TensorProduct

/-- **DEFINITION**, the integral Tate module over the actual algebraic closure
of the rationals. Locator: Silverman III.7; `TauCeti.TateModule`. -/
abbrev integralTate (E : WeierstrassCurve ℚ) (ℓ : ℕ) : Type :=
  TauCeti.TateModule ℓ (E.baseChange GlueC10.Qbar).toAffine.Point

/-- **DEFINITION**, the actual coordinatewise Galois action on every torsion
level, passed to the inverse limit. Locator: the proved
`WeierstrassCurve.tateModuleGaloisRepresentation` in `TateModule/Galois.lean`. -/
def integralTateRep (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation ℤ_[ℓ] GlueC10.GQ (integralTate E ℓ) := by
  classical
  exact E.tateModuleGaloisRepresentation ℓ

/-- **DEFINITION WITH PROVED EXISTENCE**, an integral Tate basis. Locator:
Silverman III.7.1 and the proved `nonempty_linearEquiv_tateModule`. -/
def integralTateBasis (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : Basis (Fin 2) ℤ_[ℓ] (integralTate E ℓ) := by
  classical
  have hℓ : (ℓ : GlueC10.Qbar) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  exact Basis.ofEquivFun
    (Classical.choice ((E.baseChange GlueC10.Qbar).nonempty_linearEquiv_tateModule hℓ))

/-- **DEFINITION**, the rational Tate module `ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(E)`.
Locator: Faltings 1983, §5, Satz 3. -/
abbrev rationalTate (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] integralTate E ℓ

/-- **DEFINITION**, rationalization of the actual integral Galois action.
Locator: Faltings 1983, §5; `Representation.baseChange`. -/
def rationalTateRep (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation ℚ_[ℓ] GlueC10.GQ (rationalTate E ℓ) :=
  Representation.baseChange ℚ_[ℓ] (integralTateRep E ℓ)

/-- **DEFINITION WITH PROVED BASIS**, the scalar extension of the integral
Tate basis. Locator: Mathlib `Module.Basis.baseChange`. -/
def rationalTateBasis (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : Basis (Fin 2) ℚ_[ℓ] (rationalTate E ℓ) :=
  Algebra.TensorProduct.basis ℚ_[ℓ] (integralTateBasis E ℓ)

/-- **PROVED INSTANCE**, finite-dimensionality of the actual rational Tate
module, from its displayed two-element basis. Locator: `rationalTateBasis`. -/
instance rationalTateFinite (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : FiniteDimensional ℚ_[ℓ] (rationalTate E ℓ) :=
  Module.Finite.of_basis (rationalTateBasis E ℓ)

/-- **PROVED**, the rank of the rational Tate module is two, independently
of the newform representation. Locator: `rationalTateBasis`. -/
theorem rationalTate_finrank (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : Module.finrank ℚ_[ℓ] (rationalTate E ℓ) = 2 := by
  rw [Module.finrank_eq_card_basis (rationalTateBasis E ℓ), Fintype.card_fin]

/-- **DEFINITION**, the actual rational Tate module after scalar extension
into a common coefficient field. Locator: `rationalTate` and scalar extension. -/
abbrev extendedTate (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [Field K] [Algebra ℚ_[ℓ] K] : Type :=
  K ⊗[ℚ_[ℓ]] rationalTate E ℓ

/-- **DEFINITION**, the actual Tate representation in the common field.
Locator: `rationalTateRep` and `Representation.baseChange`. -/
def extendedTateRep (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [Field K] [Algebra ℚ_[ℓ] K] :
    Representation K GlueC10.GQ (extendedTate E ℓ K) :=
  Representation.baseChange K (rationalTateRep E ℓ)

/-- **DEFINITION WITH PROVED BASIS**, the two-element basis after extension
to the common coefficient field. Locator: `rationalTateBasis`. -/
def extendedTateBasis (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [Field K] [Algebra ℚ_[ℓ] K] :
    Basis (Fin 2) K (extendedTate E ℓ K) :=
  Algebra.TensorProduct.basis K (rationalTateBasis E ℓ)

/-- **PROVED INSTANCE**, finite-dimensionality after extension into the
common field. Locator: `extendedTateBasis`. -/
instance extendedTateFinite (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] :
    FiniteDimensional K (extendedTate E ℓ K) :=
  Module.Finite.of_basis (extendedTateBasis E ℓ K)

/-- **PROVED**, the common-field Tate representation still has dimension two.
Locator: `extendedTateBasis`. -/
theorem extendedTate_finrank (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] :
    Module.finrank K (extendedTate E ℓ K) = 2 := by
  rw [Module.finrank_eq_card_basis (extendedTateBasis E ℓ K), Fintype.card_fin]

/-- **PROVED**, continuity of coordinates in any integral Tate basis.
Locators: the continuous scalar action on `TauCeti.TateModule` and the
compact-to-Hausdorff inverse theorem. No topology is assigned by fiat to
make the chosen basis continuous. -/
theorem continuous_integralTateBasis_equivFun (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : Continuous (integralTateBasis E ℓ).equivFun := by
  classical
  let e := (integralTateBasis E ℓ).equivFun
  have hrep : ∀ x : Fin 2 → ℤ_[ℓ],
      e.symm x = ∑ i : Fin 2, x i • e.symm (Pi.single i 1) := by
    intro x
    apply e.injective
    ext j
    fin_cases j <;> simp [map_smul]
  have heinv : Continuous e.symm :=
    (continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)).congr
      (fun x => (hrep x).symm)
  change Continuous e
  have heinv' : Continuous e.symm.toEquiv := heinv
  exact heinv'.continuous_symm_of_equiv_compact_to_t2

/-- **PROVED**, a continuous action with continuous basis coordinates has
continuous matrices. Locator: Mathlib `continuous_matrix` and
`LinearMap.toMatrix_apply`. -/
theorem continuous_matrix_of_continuous_action {R G V ι : Type*}
    [CommRing R] [TopologicalSpace R] [Monoid G] [TopologicalSpace G]
    [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R V)
    (hb : Continuous b.equivFun) (ρ : Representation R G V)
    (hρ : Continuous fun q : G × V => ρ q.1 q.2) :
    Continuous fun g : G => LinearMap.toMatrix b b (ρ g) := by
  apply continuous_matrix
  intro i j
  have ha : Continuous fun g : G => ρ g (b j) :=
    hρ.comp (continuous_id.prodMk continuous_const)
  have hc := (continuous_apply i).comp (hb.comp ha)
  simpa only [LinearMap.toMatrix_apply, Basis.equivFun_apply, Function.comp_def] using hc

/-- **PROVED**, matrix continuity of the actual integral Tate representation.
Locators: `continuous_tateModuleGaloisRepresentation_apply` and
`continuous_integralTateBasis_equivFun`. -/
theorem continuous_integralTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous fun g : GlueC10.GQ => LinearMap.toMatrix
      (integralTateBasis E ℓ) (integralTateBasis E ℓ) (integralTateRep E ℓ g) := by
  classical
  apply continuous_matrix_of_continuous_action (integralTateBasis E ℓ)
    (continuous_integralTateBasis_equivFun E ℓ) (integralTateRep E ℓ)
  have h := E.continuous_tateModuleGaloisRepresentation_apply (K := GlueC10.Qbar) ℓ
  simpa only [integralTateRep] using h

/-- **PROVED**, scalar extension reads every Tate matrix through the
coefficient embedding. Locator: Mathlib `LinearMap.toMatrix_baseChange`. -/
theorem rationalTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (g : GlueC10.GQ) :
    LinearMap.toMatrix (rationalTateBasis E ℓ) (rationalTateBasis E ℓ)
      (rationalTateRep E ℓ g) =
        (LinearMap.toMatrix (integralTateBasis E ℓ) (integralTateBasis E ℓ)
          (integralTateRep E ℓ g)).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
  simpa only [rationalTateBasis, rationalTateRep, Representation.baseChange_apply] using
    LinearMap.toMatrix_baseChange ℚ_[ℓ] (integralTateRep E ℓ g)
      (integralTateBasis E ℓ) (integralTateBasis E ℓ)

/-- **PROVED**, continuity after rationalization. Locators:
`rationalTateRep_matrix`, the continuous inclusion `ℤ_ℓ → ℚ_ℓ`. -/
theorem continuous_rationalTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous fun g : GlueC10.GQ => LinearMap.toMatrix
      (rationalTateBasis E ℓ) (rationalTateBasis E ℓ) (rationalTateRep E ℓ g) := by
  simp_rw [rationalTateRep_matrix]
  exact (continuous_integralTateRep_matrix E ℓ).matrix_map
    (show Continuous (algebraMap ℤ_[ℓ] ℚ_[ℓ]) from continuous_subtype_val)

/-- **PROVED**, the same coefficientwise scalar-extension identity for the
common coefficient field. Locator: Mathlib `LinearMap.toMatrix_baseChange`. -/
theorem extendedTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K]
    (g : GlueC10.GQ) :
    LinearMap.toMatrix (extendedTateBasis E ℓ K) (extendedTateBasis E ℓ K)
      (extendedTateRep E ℓ K g) =
        (LinearMap.toMatrix (rationalTateBasis E ℓ) (rationalTateBasis E ℓ)
          (rationalTateRep E ℓ g)).map (algebraMap ℚ_[ℓ] K) := by
  simpa only [extendedTateBasis, extendedTateRep, Representation.baseChange_apply] using
    LinearMap.toMatrix_baseChange K (rationalTateRep E ℓ g)
      (rationalTateBasis E ℓ) (rationalTateBasis E ℓ)

/-- **PROVED**, matrix continuity in any common topological coefficient
field with continuous structural embedding. Locators:
`continuous_rationalTateRep_matrix`, `extendedTateRep_matrix`. -/
theorem continuous_extendedTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K]
    [TopologicalSpace K] (hK : Continuous (algebraMap ℚ_[ℓ] K)) :
    Continuous fun g : GlueC10.GQ => LinearMap.toMatrix
      (extendedTateBasis E ℓ K) (extendedTateBasis E ℓ K) (extendedTateRep E ℓ K g) := by
  simp_rw [extendedTateRep_matrix]
  exact (continuous_rationalTateRep_matrix E ℓ).matrix_map hK

/-- **PROVED**, the good-reduction trace dictionary on the exact local Tate
module and arithmetic Frobenius appearing in the existing interface.
Locator: Silverman V.2.3, VII.7.1; the proved Tate-reduction comparison and
`DetDegree.frobeniusTateDetFormOne_proved`. This reproduces the proof of
`FrobeniusTraceDictionary/Proved.lean` through its compiled dependencies. -/
theorem goodReductionFrobeniusTraceDictionaryQ_proved :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionFrobeniusTraceDictionaryQ :=
  ZInQ.Contrib.RC53Assist.TateReduction.goodReductionFrobeniusTraceDictionaryQ_of_tateDetFormOne
    ZInQ.Contrib.RC53Assist.DetDegree.frobeniusTateDetFormOne_proved

end ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion


/-!
# Valuation places of arithmetic Frobenius

This is the proved localization construction from
`Contrib/Chebotarev/FrobeniusDenseOfExists.lean`, with the finite Frobenius
and integral-closure objects supplied by the compiled identical definitions
in `HDecomp/C10/C10.lean`. It provides actual valuation subrings of the
algebraic closure and genuine arithmetic Frobenius, not arbitrary subgroups.
No arithmetic input is assumed.
-/

noncomputable section
set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic

open NumberField
open scoped Pointwise
open GlueC10 (Zbar toZbar toZbar_coe)


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
abbrev Qbar := AlgebraicClosure ℚ


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U



variable (P : Ideal Zbar) [hP : P.IsPrime]


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
def LocMem (x : Qbar) : Prop := ∃ a s : Zbar, s ∉ P ∧ x * (s : Qbar) = a

/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
theorem one_notMem : (1 : Zbar) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top

omit hP in
/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
theorem natCast_mem (p : ℕ) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) : (p : Zbar) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ Zbar (p : ℤ) ∈ P := h1
  simpa using h2

omit hP in

/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
theorem exists_frac_or_inv (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hQ0 : Q ≠ ⊥) (x : K) (hx0 : x ≠ 0) :
    ∃ r s : 𝓞 K, s ∉ Q ∧ (x * (s : K) = r ∨ x⁻¹ * (s : K) = r) := by
  let Aₘ := Localization.AtPrime Q
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hQ0 Aₘ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : (b : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply hx0
    rw [← hab]
    change (a : K) / (b : K) = 0
    rw [h, zero_div]
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap (𝓞 K) Aₘ a) (algebraMap (𝓞 K) Aₘ b)
  obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
  have hinj := IsLocalization.injective Aₘ Q.primeCompl_le_nonZeroDivisors
  refine ⟨r, s, hs, ?_⟩
  rcases hc with hc | hc
  · right
    have e : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (a : K) * (r : K) = (b : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change ((a : K) / (b : K))⁻¹ * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm
  · left
    have e : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (b : K) * (r : K) = (a : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change (a : K) / (b : K) * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm


/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
theorem locMem_or_inv (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (x : Qbar) : LocMem P x ∨ LocMem P x⁻¹ := by
  by_cases hx0 : x = 0
  · left
    exact ⟨0, 1, one_notMem P, by simp [hx0]⟩
  have hxi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  let E := IntermediateField.adjoin ℚ ({x} : Set Qbar)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxi
  have : NumberField E := ⟨⟩
  let Q := P.comap (toZbar E)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hpQ : ((p : ℤ) : 𝓞 E) ∈ Q := by
    change toZbar E ((p : ℤ) : 𝓞 E) ∈ P
    simpa using natCast_mem P p hPp
  have hQ0 : Q ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpQ
    exact (by exact_mod_cast hp.ne_zero : ((p : ℤ) : 𝓞 E) ≠ 0) hpQ
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨r, s, hs, h | h⟩ := exists_frac_or_inv E Q hQ0 x' hx'0
  · left
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this
  · right
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this


/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
def zbarLoc (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    ValuationSubring Qbar where
  carrier := {x | LocMem P x}
  mul_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (y * (t : Qbar)) * ha + (a : Qbar) * hb
  one_mem' := ⟨1, 1, one_notMem P, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * t + b * s, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (t : Qbar) * ha + (s : Qbar) * hb
  zero_mem' := ⟨0, 1, one_notMem P, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, ha⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast
    linear_combination -ha
  mem_or_inv_mem' := locMem_or_inv P p hp hPp

/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
theorem mem_zbarLoc {p : ℕ} {hp : p.Prime} {hPp : P.under ℤ = Ideal.span {(p : ℤ)}} {x : Qbar} :
    x ∈ zbarLoc P p hp hPp ↔ LocMem P x := Iff.rfl




/-- **DEFINITION**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
def gZ (g : GQ) (z : Zbar) : Zbar :=
  ⟨g z, (z.2 : IsIntegral ℤ (z : Qbar)).map ((g : Qbar →ₐ[ℚ] Qbar).restrictScalars ℤ)⟩

/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
@[simp] theorem gZ_coe (g : GQ) (z : Zbar) : ((gZ g z : Zbar) : Qbar) = g z := rfl

/-- **PROVED**, the localization and arithmetic-Frobenius reading
from `Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
section on localization of the integral closure. -/
theorem liesOver_and_isArithFrob (h : GQ) (p : ℕ) (hp : p.Prime)
    (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    LiesOver (zbarLoc P p hp hPp) p ∧ IsArithFrob h (zbarLoc P p hp hPp) p := by
  have hcong : ∀ z : Zbar, gZ h z - z ^ p ∈ P := fun z => hh z _ (by push_cast; rfl)
  have hmemP : ∀ z : Zbar, gZ h z ∈ P ↔ z ∈ P := by
    intro z
    constructor
    · intro hz
      have : z ^ p ∈ P := by
        have := P.sub_mem hz (hcong z)
        rwa [sub_sub_cancel] at this
      exact hP.mem_of_pow_mem p this
    · intro hz
      have := P.add_mem (hcong z) (P.pow_mem_of_mem hz p hp.pos)
      rwa [sub_add_cancel] at this
  have hpP := natCast_mem P p hPp
  refine ⟨?_, ?_, ?_⟩
  · -- `p` is a nonunit
    rw [LiesOver, ValuationSubring.mem_nonunits_iff_or]
    right
    rintro ⟨a, s, hs, ha⟩
    apply hs
    have : s = (p : Zbar) * a := by
      apply Subtype.ext
      push_cast
      rw [← ha, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero), one_mul]
    rw [this]
    exact P.mul_mem_right _ hpP
  · -- `h` stabilizes the place
    refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · rintro ⟨a, s, hs, ha⟩
      refine ⟨gZ h a, gZ h s, fun h' => hs ((hmemP s).1 h'), ?_⟩
      have := congrArg h ha
      rw [map_mul] at this
      simpa [AlgEquiv.aut_inv] using this
    · rintro ⟨a, s, hs, ha⟩
      have hts : gZ h (gZ h⁻¹ s) = s := by
        apply Subtype.ext
        simp [AlgEquiv.aut_inv]
      refine ⟨gZ h⁻¹ a, gZ h⁻¹ s, fun h' => hs (hts ▸ (hmemP _).2 h'), ?_⟩
      have := congrArg (fun y => (h⁻¹ : GQ) y) ha
      simp only [map_mul] at this
      simpa using this
  · -- the Frobenius congruence on the place
    rintro x ⟨a, s, hs, ha⟩
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases hd : h x - x ^ p = 0
    · exact Or.inl hd
    right
    rintro ⟨a', s', hs', hd'⟩
    let n : Zbar := gZ h a * s ^ p - a ^ p * gZ h s
    have hn : n ∈ P := by
      have : n = (gZ h a - a ^ p) * s ^ p - a ^ p * (gZ h s - s ^ p) := by ring
      rw [this]
      exact P.sub_mem (P.mul_mem_right _ (hcong a)) (P.mul_mem_left _ (hcong s))
    have e1 : h x * h (s : Qbar) = h (a : Qbar) := by rw [← map_mul, ha]
    have e2 : x ^ p * (s : Qbar) ^ p = (a : Qbar) ^ p := by rw [← mul_pow, ha]
    have e3 : (h x - x ^ p) * (h (s : Qbar) * (s : Qbar) ^ p) = (n : Qbar) := by
      simp only [n]
      push_cast
      simp only [gZ_coe]
      linear_combination ((s : Qbar) ^ p) * e1 - (h (s : Qbar)) * e2
    have e4 : (s' : Qbar) = (h x - x ^ p) * (a' : Qbar) := by
      rw [← hd', ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    have e5 : s' * (gZ h s * s ^ p) = a' * n := by
      apply Subtype.ext
      push_cast
      simp only [gZ_coe]
      rw [e4, ← e3]
      ring
    have hmem : s' * (gZ h s * s ^ p) ∈ P := e5 ▸ P.mul_mem_left _ hn
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hs' h1
    rcases hP.mem_or_mem h1 with h2 | h2
    · exact hs ((hmemP s).1 h2)
    · exact hs (hP.mem_of_pow_mem p h2)


/-- **PROVED**, by localizing the actual prime of the integral closure
in `GlueC10.IsFrobAt`. Locator: `liesOver_and_isArithFrob` above. -/
theorem place_of_isFrobAt (g : GQ) (p : ℕ) (hp : p.Prime)
    (h : GlueC10.IsFrobAt g p) :
    ∃ v : ValuationSubring Qbar, LiesOver v p ∧ IsArithFrob g v p := by
  obtain ⟨P, hP, hPp, hh⟩ := h
  have : P.IsPrime := hP
  exact ⟨zbarLoc P p hp hPp, liesOver_and_isArithFrob P g p hp hPp hh⟩

/-- **PROVED**, Frobenius at a specified rational prime. Locators:
`GlueC10.frobExistsAt_of_finite`, the finite-layer existence theorem,
and lying-over for the integral closure of the integers. -/
theorem exists_place_and_frobenius (p : ℕ) (hp : p.Prime) :
    ∃ (v : ValuationSubring Qbar) (g : GQ),
      LiesOver v p ∧ IsArithFrob g v p ∧ GlueC10.IsFrobAt g p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have : I.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, -, hP, hPI⟩ := Ideal.exists_ideal_over_prime_of_isIntegral I
    (⊥ : Ideal Zbar) (by
      intro x hx
      have hx' : algebraMap ℤ Zbar x = 0 := hx
      have hxQ := congrArg (fun z : Zbar => (z : Qbar)) hx'
      change (x : Qbar) = 0 at hxQ
      have hx0 : x = 0 := by exact_mod_cast hxQ
      rw [hx0]
      exact I.zero_mem)
  have : P.IsPrime := hP
  obtain ⟨g, hg⟩ := (GlueC10.frobExistsAt_of_finite GlueC10.frobExistsFinite) p P hPI
  obtain ⟨v, hv, hf⟩ := place_of_isFrobAt g p hp ⟨P, hP, hPI, hg⟩
  exact ⟨v, g, hv, hf, P, hP, hPI, hg⟩

end ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic


/-!
# G0 by coefficient-field descent and the local-factor readings

The additional source used for descent is manuscript-cited Shimura 1973,
Theorem 1, p. 526: its conjugate eigenforms at all embeddings of the coefficient
field. Li 1975, Theorem 5, p. 298, and the proved old/new decomposition show
that a newform agreeing with an elliptic curve at almost all primes has
rational coefficients at every index, including the bad indices.

Carayol 1986, the Corollaire of §0.8, p. 411, then applies with precisely its
rational-newform premise. Its associated elliptic curve has the newform's
Euler factors. Faltings 1983, §5, Korollar 2, iii ⇒ iv, p. 361, transfers
those factors to the original elliptic curve. The final coefficient assembly
is proved. No input asserts existence of a newform for the original curve.

The two local-factor interfaces are GLUE readings of the printed results in
the existing minimal Weierstrass polynomial language. Their Tate and scheme
translations remain explicit; the newform-of-a-modular-curve conclusion is
proved conditionally from the displayed interfaces, not called a print.
-/

noncomputable section
set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformPeriods
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **DEFINITION**, the actual coefficient field generated by all Fourier
coefficients. Locator: Shimura 1973, Theorem 1, p. 526, field `K`. -/
def coefficientField {M : ℕ} [NeZero M] (F : Newform M 2) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n)

/-- **PROVED**, generator membership in the actual coefficient field.
Locator: Mathlib `IntermediateField.subset_adjoin`. -/
theorem coeff_mem {M : ℕ} [NeZero M] (F : Newform M 2) (n : ℕ) :
    (qExpansion 1 F.toCuspForm).coeff n ∈ coefficientField F :=
  IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩

/-- **PRINT SPECIALIZATION**, manuscript bibitem `shimura-factors`, Shimura
1973, Theorem 1 and its setting, pp. 525–526: the coefficient field is finite,
and every complex embedding gives a normalized full eigenform at the same
level, with the embedded coefficients. The original form here is a genuine
weight-two trivial-character newform. This does not assert that any elliptic
curve has a newform. The number-field and subgroup readings are the usual
readings of the printed `K` and `S₂(Γ₀(M))`.

Verbatim printed text, with mathematics transcribed in plain text / Unicode.
The running heads identify printed pp. 525 and 526 as PDF pages 3 and 4.
The definitions of `D_B` and `Y_B` begin on p. 524 and continue on p. 525;
that preceding paragraph is included to make the definitions complete.

Definitions (p. 524, continued on p. 525):

Let us start with some definitions and notational convention. For an
abelian variety B defined over C, we denote by D_B, or D(B), the vector space
over C of all holomorphic 1-forms on B, and by Y_B, or Y(B), the tangent
space of B at the origin. Then D_B is dual to Y_B, so that we have a C-
bilinear pairing

( , )_B: D_B × Y_B → C.

If α is a homomorphism of B to another abelian variety B′, one can naturally
define two maps

dα: Y_B → Y_{B′},
δα: D_{B′} → D_B,

which satisfy

(1.1) (δαu, v)_B = (u, dαv)_{B′} (u ∈ D_{B′}, v ∈ Y_B).

By a quotient of B by an abelian subvariety, say C, of B, we understand
a couple (A, ν) formed by an abelian variety A which canonically represents
B/C and a natural map ν: B → A with C = Ker(ν) (cf. Chow [3]). We see
easily that

(1.2) Y_C = {v ∈ Y_B | (u, v)_B = 0 for all u ∈ δν(D_A)}.

Let Γ be a group of level N, and J the jacobian variety of ℌ*/Γ. Let
ψ: ℌ* → J be the map obtained by composing the natural map ℌ* → ℌ*/Γ with
a canonical map of ℌ*/Γ into J. Then there is an isomorphism μ: S₂(Γ) → D_J
defined by δψ(μ(f)) = f(z)dz for f ∈ S₂(Γ), where δψ is the “pull back” asso-
ciated with ψ, and z is a standard variable on ℌ.
Let Γ′ be a group of level M, and let

Γ̃ = {α ∈ R · GL₂(Q) | det(α) > 0}.

Define, for α ∈ Γ̃, an algebraic correspondence X(Γ′αΓ) on ℌ*/Γ × ℌ*/Γ′ as
in [11, § 7.2]. (Briefly, it is the locus of z × α(z) modulo Γ × Γ′.) Let J′ and
μ′ denote the corresponding geometric objects defined with Γ′ in place of Γ.
One can attach to X(Γ′αΓ) a homomorphism of J into J′ as in Weil [15, § VI],
which we denote by {Γ′αΓ}. Now the commutative diagrams (7.2.2) and
(7.2.6) of [11] imply

(1.3) μ ∘ [Γ′αΓ]₂ = δ{Γ′αΓ} ∘ μ′,

where [Γ′αΓ]_k is the map S_k(Γ′) → S_k(Γ) defined in [11, § 3.4]. Then, from
(1.1) and (1.3), we obtain

(1.4) (μ′(f), d{Γ′αΓ}v)_{J′} = (μ(f | [Γ′αΓ]₂), v)_J (f ∈ S₂(Γ′), v ∈ Y_J).

For a positive integer n, let q be the largest divisor of n prime to N, and
put n = mq. Then we define T_n and ξ_n by T_n = T_m T_q, ξ_n = ξ_m ξ_q, T_m = [ΓαΓ]₂,
ξ_m = {ΓαΓ} with α = [1 0; 0 m], and T_q = ∑_β [ΓβΓ]₂, ξ_q = ∑_β {ΓβΓ}, where ∑_β
is extended over all distinct ΓβΓ with det(β) = q, β ≡ [1 0; 0 q] (mod N). Then
μ ∘ T_n = δξ_n ∘ μ.

Setting and Theorem 1 (p. 526):

As shown in [11, § 7.3], there is a “standard model” of ℌ*/Γ defined
over Q (see also § 4 below), so that J can naturally be defined over Q. Let
f(z) = ∑_{n=1}^∞ a_n e^{2πinz}, with a₁ = 1, be an element of S₂(Γ), that is a common eigen-
function of T_n for all n (i. e., f | T_n = a_n f). Fix f, and let K be the subfield
of C generated over Q by the complex numbers a_n for all n. (Of course K
depends on f.) Then we have
THEOREM 1. There exists a triple (A, ν, θ) formed by the objects satisfying
the following conditions:
(i) (A, ν) is a quotient of J by an abelian subvariety rational over Q.
(ii) θ is an isomorphism of K into End(A) ⊗ Q such that ν ∘ ξ_n = θ(a_n) ∘ ν
for all n. (This implies especially θ(1) = id_A.)
(iii) dim(A) = [K: Q].
Moreover, let I denote the set of all isomorphisms of K into C. Then, for every
σ ∈ I, there exists an element f_σ of S₂(Γ) such that f_σ | T_n = a_n^σ f for all n, and
f_σ(z) = ∑_{n=1}^∞ a_n^σ e^{2πinz}. With these f_σ, one has
(iv) δν(D_A) = μ(∑_{σ∈I} Cf_σ).
Under the conditions (i, ii), the triple (A, ν, θ) is unique up to isomorphisms
over Q. Furthermore, the one-dimensional part of the zeta function of A over
Q coincides, up to finitely many Euler factors for bad primes, with ∏_{σ∈I}(∑_{n=1}^∞ a_n^σ n^{−s}),
provided that Γ = Γ₀(N), or ∑_{σ∈I} Cf_σ is stable under the map h(z) ↦ h(−1/Nz)/z².

The printed `f` after `a_n^σ` is retained verbatim in this transcription; the Lean statement reads
it as `f_σ`, as in the proof on p. 527. No unreadable mathematical symbol remains in this
transcription.
-/
def Shimura1973ConjugateEigenforms : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2), F.χ = 1 →
    FiniteDimensional ℚ (coefficientField F) ∧
      ∀ σ : coefficientField F →ₐ[ℚ] ℂ,
        ∃ g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2,
          IsNormalizedFullEigenformGamma0 M g ∧
          ∀ n : ℕ, (qExpansion 1 g).coeff n = σ ⟨(qExpansion 1 F.toCuspForm).coeff n,
            coeff_mem F n⟩

/-- **PROVED**, from the genuine full eigenform and the divisor-level
old/new decomposition. Locators: `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`,
Li 1975, §2 p. 294 and Theorem 3, p. 295. -/
theorem fullEigenform_divisor_newform {M : ℕ} [NeZero M]
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : IsNormalizedFullEigenformGamma0 M g) :
    ∃ (e : Eigenform M 2), e.χ = 1 ∧ (∀ τ, e.toCuspForm τ = g τ) ∧
      (qExpansion 1 e.toCuspForm).coeff 1 = 1 ∧
      ∃ (L : ℕ) (_ : NeZero L) (hLM : L ∣ M) (G : Newform L 2), G.χ = 1 ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpM : Nat.Coprime p M),
          G.eigenvalue ⟨p, hp.pos⟩ (hpM.coprime_dvd_right hLM) = e.eigenvalue ⟨p, hp.pos⟩ := by
  obtain ⟨hg₁, e, heχ, heg⟩ := hg
  have heg' : ⇑e.toCuspForm = ⇑g := funext heg
  have he₁ : (qExpansion 1 e.toCuspForm).coeff 1 = 1 := by rw [heg']; exact hg₁
  have hmem : e.toCuspForm ∈ cuspFormCharSpace (N := M) 2 (1 : (ZMod M)ˣ →* ℂˣ) :=
    heχ ▸ e.mem_charSpace
  obtain ⟨L, hL0, hLM, G, hGχ, hG⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      hmem e.ne_zero (fun p hp _ => e.heckeTCuspNat_eq_eigenvalue_smul hp)
  have hχ : G.χ = 1 := by
    apply MonoidHom.ext
    intro u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hLM u
    have h := congrArg (fun c : (ZMod M)ˣ →* ℂˣ => c v) hGχ
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  exact ⟨e, heχ, heg, he₁, L, hL0, hLM, G, hχ, hG⟩

/-- **PROVED FROM THE TWO PRINTED INPUTS**, Shimura 1973, Theorem 1, p. 526,
and Li 1975, Theorem 5, p. 298, with all old/new and Hecke steps proved.
Every coefficient-field embedding fixes every coefficient of a newform
whose prime coefficients agree with those of the actual elliptic curve
outside a finite set. Nothing at bad primes is assumed. -/
theorem embedding_fixes_coefficients (hS : Shimura1973ConjugateEigenforms)
    (hL : Li1975StrongMultiplicityOneWeightTwo) (E : WeierstrassCurve ℚ)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (S : Finset ℕ)
    (hF : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ))
    (σ : coefficientField F →ₐ[ℚ] ℂ) (n : ℕ) :
    σ ⟨(qExpansion 1 F.toCuspForm).coeff n, coeff_mem F n⟩ =
      (qExpansion 1 F.toCuspForm).coeff n := by
  classical
  obtain ⟨g, hg, hgcoef⟩ := (hS M F hχ).2 σ
  obtain ⟨e, heχ, heg, he₁, L, hL0, hLM, G, hGχ, hG⟩ := fullEigenform_divisor_newform g hg
  have heg' : ⇑e.toCuspForm = ⇑g := funext heg
  have hσp : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 g).coeff p = (E.LFunction p : ℂ) := by
    intro p hp hpS
    rw [hgcoef p]
    have hc : (⟨(qExpansion 1 F.toCuspForm).coeff p, coeff_mem F p⟩ : coefficientField F) =
        (E.LFunction p : coefficientField F) := Subtype.ext (hF p hp hpS)
    rw [hc, map_intCast]
  have hLG : ∀ (p : ℕ) (hp : p.Prime) (hpM : Nat.Coprime p M),
      (qExpansion 1 G.toCuspForm).coeff p = (qExpansion 1 g).coeff p := by
    intro p hp hpM
    have hc := G.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue G.isNorm
      ⟨p, hp.pos⟩ (hpM.coprime_dvd_right hLM)
    have hec := e.qExpansion_coeff_eq_eigenvalue he₁ ⟨p, hp.pos⟩
    simp only [PNat.mk_coe] at hc hec
    rw [hc, hG p hp hpM, ← hec, heg']
  obtain ⟨hML, hFG⟩ := hL M L F G hχ hGχ ⟨S ∪ M.primeFactors, fun p hp hpS => by
    have hpS' : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpM : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr (fun hd =>
      hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne M⟩)))
    exact (hF p hp hpS').trans ((hLG p hp hpM).trans (hσp p hp hpS')).symm⟩
  subst L
  have hGF : G = F := Newform.ext (CuspForm.ext fun τ => (hFG τ).symm)
  subst G
  have hmem : e.toCuspForm ∈ cuspFormCharSpace (N := M) 2 F.χ :=
    hχ ▸ (heχ ▸ e.mem_charSpace)
  have heF := F.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul
    hmem (fun p hp hpM => by
      rw [e.heckeTCuspNat_eq_eigenvalue_smul hp, ← hG p hp hpM])
  rw [he₁, one_smul] at heF
  rw [← hgcoef n, ← heg', heF]

/-- **PROVED**, descent from equality at all coefficient-field embeddings.
Locators: Mathlib `IntermediateField.adjoin_algHom_ext`, `AlgHom.card`,
and the rank-one vector-space criterion. Only the two displayed printed
inputs are used; rationality at the bad primes is a conclusion. -/
theorem coefficients_rational_of_almost_all_primes (hS : Shimura1973ConjugateEigenforms)
    (hL : Li1975StrongMultiplicityOneWeightTwo) (E : WeierstrassCurve ℚ)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (S : Finset ℕ)
    (hF : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ)) :
    ∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ) := by
  classical
  have : FiniteDimensional ℚ (coefficientField F) := (hS M F hχ).1
  have hsame : ∀ σ : coefficientField F →ₐ[ℚ] ℂ, σ = (coefficientField F).val := by
    intro σ
    apply IntermediateField.adjoin_algHom_ext ℚ
    rintro _ ⟨n, rfl⟩
    exact embedding_fixes_coefficients hS hL E F hχ S hF σ n
  have : Unique (coefficientField F →ₐ[ℚ] ℂ) :=
    { default := (coefficientField F).val, uniq := hsame }
  have hdim : Module.finrank ℚ (coefficientField F) = 1 := by
    rw [← AlgHom.card ℚ (coefficientField F) ℂ]
    exact Fintype.card_unique
  intro n
  obtain ⟨b, hb⟩ := (finrank_eq_one_iff_of_nonzero' (1 : coefficientField F) one_ne_zero).mp
    hdim ⟨(qExpansion 1 F.toCuspForm).coeff n, coeff_mem F n⟩
  refine ⟨b, ?_⟩
  have h := congrArg (fun c : coefficientField F => (c : ℂ)) hb
  simpa using h.symm

/-- **PROVED**, the actual coefficient field is the rational subfield.
Locators: `coefficients_rational_of_almost_all_primes`, Mathlib
`IntermediateField.adjoin_le_iff` and `IntermediateField.mem_bot`.
This justifies the common completion `ℚ_ℓ` in the representation assembly,
rather than assigning a rational coefficient field by fiat. -/
theorem coefficientField_eq_bot_of_almost_all_primes
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (E : WeierstrassCurve ℚ) {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (S : Finset ℕ) (hF : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ)) :
    coefficientField F = ⊥ := by
  have hrat := coefficients_rational_of_almost_all_primes hS hL E F hχ S hF
  apply bot_unique
  rw [coefficientField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨n, rfl⟩
  obtain ⟨b, hb⟩ := hrat n
  exact IntermediateField.mem_bot.mpr ⟨b, hb.symm⟩

/-- **GLUE**: joint reading of Shimura 1973, Thm 1, and Carayol 1986, §0.8 Corollaire (a
statement joining two sources is a reading, not a print).
The rational coefficient field in Shimura's theorem gives the associated
one-dimensional quotient; Carayol's Corollaire, p. 411, identifies its local
Euler factors with those of the rational newform. The associated-curve,
Weierstrass and local-polynomial dictionaries are joint readings, not the
verbatim printed implication. This reverse construction starts with a
rational genuine newform, not with the input elliptic curve of G0. -/
def Carayol1986RationalNewformEulerFactors : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1),
    (∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) →
      ∃ A : WeierstrassCurve ℚ, A.IsElliptic ∧
        ∀ (p : ℕ) (hp : p.Prime),
          (localPolynomialQ A (primeIdealQ p hp)).map (Int.castRingHom ℂ) =
            newformEulerPolynomial F hχ p

/-- **GLUE**: local-factor reading of Faltings 1983, §5, Korollar 2 (iii ⇒ iv); GLUE unless
restated as the printed implication with the local-factor step proved.
Equal local Euler factors almost everywhere imply equal local Euler factors
everywhere, for two actual elliptic curves. The normalized factor is read
as the reciprocal of the existing minimal Weierstrass local polynomial.
This local-factor dictionary is not supplied as a proof of the printed
implication's translation into the present Weierstrass polynomial interface. -/
def Faltings1983EulerFactorRigidityQ : Prop :=
  ∀ E A : WeierstrassCurve ℚ, E.IsElliptic → A.IsElliptic →
    LocalPolynomialsAgreeAlmostEverywhere E A →
      ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        localPolynomialQ E v = localPolynomialQ A v

/-- **PROVED**, the exact G0 consequence from the two PRINT inputs and the two
GLUE local-factor readings displayed above.
Locators: Shimura 1973, Theorem 1, p. 526; Li 1975, Theorem 5, p. 298;
Carayol 1986, §0.8 Corollaire, p. 411; Faltings 1983, §5, Korollar 2,
iii ⇒ iv, p. 361. Divisor-level extraction, coefficient-field descent,
local polynomial comparison and every positive-index coefficient are proved.
No hypothesis equivalent to `LiCarayolNewformOfModular` is used. -/
theorem liCarayolNewformOfModular_of_printed_corollaries
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular := by
  intro E hE N hN f hf
  obtain ⟨M, hM0, F, hMN, hχ, S, hFp⟩ :=
    exists_newform_almost_all_prime_coeff E hE N hN f hf
  have hrat := coefficients_rational_of_almost_all_primes hS hL E F hχ S hFp
  obtain ⟨A, hA, hAP⟩ := hC M F hχ hrat
  have hEA : PrimeCoefficientsAgreeAlmostEverywhere E A := by
    refine ⟨S, fun p hp hpS => ?_⟩
    have hpow := newform_prime_pow_coeff_of_local_polynomial A F hχ p hp (hAP p hp) 1
    simp only [pow_one] at hpow
    have hprime : (E.LFunction p : ℂ) = (A.LFunction p : ℂ) :=
      (hFp p hp hpS).symm.trans hpow
    exact_mod_cast hprime
  have hPol := hF E A hE hA
    ((localPolynomials_cofinite_iff_primeCoefficients E A hE hA).mpr hEA)
  have hFpow : ∀ (p : ℕ), p.Prime → ∀ r : ℕ,
      (qExpansion 1 F.toCuspForm).coeff (p ^ r) = (E.LFunction (p ^ r) : ℂ) := by
    intro p hp r
    apply newform_prime_pow_coeff_of_local_polynomial E F hχ p hp
    rw [hPol (primeIdealQ p hp)]
    exact hAP p hp
  refine ⟨M, hM0, F, hMN, hχ, fun n hn => ?_⟩
  have hall : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (E.LFunction n : ℂ) := by
    intro n
    induction n using Nat.recOnPrimeCoprime with
    | zero =>
      rw [CuspFormClass.qExpansion_coeff_zero F.toCuspForm one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map M)]
      simp
    | prime_pow p r hp => exact hFpow p hp r
    | coprime m n _ _ hmn hm hn =>
      change newformCoefficients F (m * n) = _
      rw [(newformCoefficients_isMultiplicative F).2 hmn,
        newformCoefficients_apply, newformCoefficients_apply, hm, hn,
        (lFunction_isMultiplicative E).2 hmn, Int.cast_mul]
  exact hall n

/-- **PROVED**, the newform-periods G0 interface from the exact consequence
just established. Locator: `ModularWeil.newformOfModularCurveGlue_of_print`,
the proved subgroup and full-eigenform conversion in `ModularWeil/NewformGlue.lean`.
The premise of that conversion is a proved consequence here, not an assumed
copy of the target. -/
theorem newformOfModularCurveGlue_of_printed_corollaries
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    NewformOfModularCurveGlue :=
  ZInQ.Contrib.CloudB3RC53.ModularWeil.newformOfModularCurveGlue_of_print
    (liCarayolNewformOfModular_of_printed_corollaries hS hL hC hF)

end ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent


/-!
# Tate local definitions retained for G0

The integral and rational Tate representations above are the actual actions
on the elliptic curve's torsion. Their good-reduction trace and determinant
dictionary is proved locally here and globally in
`GlobalTrace/GoodReductionReading.lean`. Faltings 1983, §5, Satz 3, p. 360,
is retained as the explicit rational semisimplicity proposition.

For the extracted weight-two newform, rationality of every coefficient is
proved separately by `Descent.coefficients_rational_of_almost_all_primes`.
The rational newform polynomial below is only a definition of its classical
Euler polynomial. The realization and local comparison used by the corrected
representation route are stated in `GlobalTrace/CoinvariantReadings.lean`.

The definition `localTatePolynomial` reads arithmetic Frobenius on the
inertia invariants of the homological Tate representation. Its good-prime
reading is proved, but it is not the classical local factor at a prime of
multiplicative reduction. The excluded invariant-space statements are
recorded, as historical text only, in
`docs/research/g0-representation-route-invariants.md`.
-/

noncomputable section
set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion

open Module UpperHalfPlane HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **DEFINITION**, a genuine valuation place and arithmetic Frobenius.
Locator: `Completion.Arithmetic.IsArithFrob`, the proved integral-closure
localization construction. -/
structure LocalArithmeticFrobenius (p : ℕ) where
  /-- **DEFINITION**, the actual valuation subring. Locator: `ValuationSubring`. -/
  place : ValuationSubring GlueC10.Qbar
  /-- **DEFINITION**, the actual Galois element. Locator: `GlueC10.GQ`. -/
  element : GlueC10.GQ
  /-- **DEFINITION**, the place lies over the prime. Locator: `Arithmetic.LiesOver`. -/
  liesOver : Arithmetic.LiesOver place p
  /-- **DEFINITION**, the residue action. Locator: `Arithmetic.IsArithFrob`. -/
  isFrob : Arithmetic.IsArithFrob element place p
  /-- **DEFINITION**, integral-closure Frobenius. Locator: `GlueC10.IsFrobAt`. -/
  integralFrob : GlueC10.IsFrobAt element p

/-- **PROVED**, actual local arithmetic Frobenius exists at each rational
prime. Locator: `Arithmetic.exists_place_and_frobenius`. -/
theorem localArithmeticFrobenius_nonempty (p : ℕ) (hp : p.Prime) :
    Nonempty (LocalArithmeticFrobenius p) := by
  obtain ⟨v, g, hv, hg, hI⟩ := Arithmetic.exists_place_and_frobenius p hp
  exact ⟨⟨v, g, hv, hg, hI⟩⟩

/-- **DEFINITION**, the actual inertia subgroup in the global group, obtained
from the kernel of the residue-field action in the decomposition group.
Locator: Mathlib `ValuationSubring.inertiaSubgroup`. -/
def inertiaAt {p : ℕ} (D : LocalArithmeticFrobenius p) : Subgroup GlueC10.GQ :=
  (D.place.inertiaSubgroup ℚ).map (D.place.decompositionSubgroup ℚ).subtype

/-- **PROVED**, Frobenius normalizes this actual inertia subgroup.
Locator: normality of the kernel `ValuationSubring.inertiaSubgroup`. -/
theorem inertiaAt_normalized {p : ℕ} (D : LocalArithmeticFrobenius p) :
    ∀ i ∈ inertiaAt D, D.element⁻¹ * i * D.element ∈ inertiaAt D := by
  intro i hi
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hi
  let g : D.place.decompositionSubgroup ℚ := ⟨D.element, D.isFrob.1⟩
  have hn : (D.place.inertiaSubgroup ℚ).Normal := by
    unfold ValuationSubring.inertiaSubgroup
    infer_instance
  exact Subgroup.mem_map.mpr ⟨g⁻¹ * s * g, hn.conj_mem' s hs g, rfl⟩

/-- **DEFINITION**, the literal Frobenius polynomial on the actual
inertia-fixed space. Locator: `inertiaEulerPolynomial`, Carayol §0.5,
p. 410, with arithmetic and dual normalization displayed above.

**Warning: not the classical local factor at primes of multiplicative reduction.** The polynomial
uses the arithmetic Frobenius on the inertia invariants of the homological representation. For a
Tate curve the invariants are the line `ℚ_ℓ(1) ⊗ ε`, on which the arithmetic Frobenius acts by
`ε p`, so this side is `1 - ε p X`, while the classical factor is `1 - ε X` (for the curve 11a1 at
`p = 11`: `1 - 11 X` against `1 - X`). The correct reading uses the inertia coinvariants
(equivalently the dual representation with the inverse Frobenius). The printed-corollary route
`Descent.liCarayolNewformOfModular_of_printed_corollaries` does not use this definition. -/
def localTatePolynomial (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) : Polynomial ℚ_[ℓ] :=
  inertiaEulerPolynomial (rationalTateRep E ℓ) (inertiaAt D) D.element
    (inertiaAt_normalized D)

/-- **DEFINITION**, the classical weight-two Euler polynomial in the common
coefficient field. The sequence `b` is required to be the actual rational
Fourier coefficients when this polynomial is used. Locators: Li 1975,
Theorem 3(i), p. 295, and Carayol §0.5. -/
def rationalNewformPolynomial (M ℓ : ℕ) [Fact ℓ.Prime] (b : ℕ → ℚ) (p : ℕ) :
    Polynomial ℚ_[ℓ] :=
  1 - Polynomial.C (b p : ℚ_[ℓ]) * Polynomial.X +
    Polynomial.C (if Nat.Coprime p M then (p : ℚ_[ℓ]) else 0) * Polynomial.X ^ 2

/-- **PRINT SPECIALIZATION**, manuscript bibitem `faltings1983`,
Faltings 1983, §5, Satz 3, p. 360, page image checked: the actual rational
Tate module of an elliptic curve over the rationals is semisimple.
No scalar-extension semisimplicity is silently added to this statement.

Verbatim printed text (§5, p. 360): "§ 5. Endomorphismen. Sei K Zahlkörper, A/K eine abelsche
Varietät der Dimension g, l eine Primzahl, T_l = T_l(A) der Tate-Modul, auf dem π = Gal(K̄/K)
operiert. Satz 3. Die Operation von π auf T_l ⊗_{ℤ_l} ℚ_l ist halbeinfach." -/
def Faltings1983Satz3EllipticQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime],
    IsSemisimpleModule (MonoidAlgebra ℚ_[ℓ] GlueC10.GQ) (rationalTateRep E ℓ).asModule

/-- **GLOBALIZATION OF A PROVED DICTIONARY**, PROVED in `GlobalTrace/GoodReductionReading.lean` as
`globalGoodReductionTraceReading_proved` (that proof does not use the premise); first stated here as
GLUE. The global integral-closure Frobenius reading of the exact local dictionary. Locators:
Silverman VII.3.1, VII.7.1 and the completion restriction of the Tate action. The premise is the
existing local dictionary, proved above by `goodReductionFrobeniusTraceDictionaryQ_proved`, not an
unproved local formula. It is not called a statement of Carayol (A). -/
def GlobalGoodReductionTraceReading : Prop :=
  GoodReductionFrobeniusTraceDictionaryQ →
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
      (p : ℕ) (hp : p.Prime), p ≠ ℓ → GoodReductionAt E (primeIdealQ p hp) →
      (∀ D : LocalArithmeticFrobenius p, ∀ i ∈ inertiaAt D,
        rationalTateRep E ℓ i = 1) ∧
      ∀ g : GlueC10.GQ, GlueC10.IsFrobAt g p →
        LinearMap.trace ℚ_[ℓ] (rationalTate E ℓ) (rationalTateRep E ℓ g) =
            (E.LFunction p : ℚ_[ℓ]) ∧
          LinearMap.det (rationalTateRep E ℓ g) = (p : ℚ_[ℓ])

/-- **PROVED**, trivial actual inertia identifies the fixed-space
Frobenius polynomial with the full-space Frobenius polynomial. Locator:
`fixedInertia`, `inertiaFrobenius`, and conjugacy invariance of characteristic polynomials. -/
theorem inertiaEulerPolynomial_of_trivial_inertia {K G V : Type*}
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) (g : G)
    (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) (hI : ∀ i ∈ I, ρ i = 1) :
    inertiaEulerPolynomial ρ I g hg = (LinearMap.charpoly (ρ g)).reverse := by
  have hspace : fixedInertia ρ I = ⊤ := by
    apply Submodule.ext
    intro v
    simp only [Submodule.mem_top, iff_true]
    change ∀ i : I, ρ (i : G) v = v
    intro i
    rw [hI i.1 i.2, Module.End.one_apply]
  let e : fixedInertia ρ I ≃ₗ[K] V :=
    (LinearEquiv.ofEq (fixedInertia ρ I) ⊤ hspace).trans Submodule.topEquiv
  have he : ∀ v : fixedInertia ρ I, e v = (v : V) := fun v => by simp [e]
  have hes : ∀ v : V, ((e.symm v : fixedInertia ρ I) : V) = v := by
    intro v
    exact (he (e.symm v)).symm.trans (e.apply_symm_apply v)
  have hc : e.conj (inertiaFrobenius ρ I g hg) = ρ g := by
    ext v
    change e (inertiaFrobenius ρ I g hg (e.symm v)) = ρ g v
    rw [he]
    change ρ g ((e.symm v : fixedInertia ρ I) : V) = ρ g v
    rw [hes]
  have hchar := (e.charpoly_conj (inertiaFrobenius ρ I g hg)).symm.trans
    (congrArg LinearMap.charpoly hc)
  exact congrArg Polynomial.reverse hchar

/-- **PROVED**, the reversed characteristic polynomial on a displayed
rank-two module is its determinant Euler polynomial. Locators:
`Matrix.reverse_charpoly`, `determinantEuler_polynomial`. -/
theorem reversedCharpoly_rank_two {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (b : Basis (Fin 2) K V) (f : Module.End K V) :
    (LinearMap.charpoly f).reverse =
      1 - Polynomial.C (LinearMap.trace K V f) * Polynomial.X +
        Polynomial.C (LinearMap.det f) * Polynomial.X ^ 2 := by
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.reverse_charpoly, Matrix.charpolyRev,
    determinantEuler_polynomial, ← LinearMap.trace_eq_matrix_trace K b f, LinearMap.det_toMatrix]

/-- **PROVED FROM THE EXPLICIT GLOBAL READING**, the actual good local Tate
polynomial is the already proved minimal-reduction polynomial. Locators:
`goodReductionFrobeniusTraceDictionaryQ_proved`, the displayed global reading,
and `reversedCharpoly_rank_two`. No equality with a newform is assumed. -/
theorem localTatePolynomial_of_good (hG : GlobalGoodReductionTraceReading)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (hgood : GoodReductionAt E (primeIdealQ p hp))
    (D : LocalArithmeticFrobenius p) :
    localTatePolynomial E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) := by
  have h := hG goodReductionFrobeniusTraceDictionaryQ_proved E ℓ p hp hpℓ hgood
  have htd := h.2 D.element D.integralFrob
  rw [localTatePolynomial, inertiaEulerPolynomial_of_trivial_inertia
    (rationalTateRep E ℓ) (inertiaAt D) D.element (inertiaAt_normalized D) (h.1 D),
    reversedCharpoly_rank_two (rationalTateBasis E ℓ), htd.1, htd.2,
    localPolynomialQ_eq_of_good E (primeIdealQ p hp) hgood, primeIdealQ_absNorm]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_one,
    Int.coe_castRingHom, Int.cast_natCast]

/-- **PROVED**, returning a single local polynomial through the injective
rational and integer embeddings. Locator: the two coefficient maps and
`localPolynomialQ_shape`. This is a one-prime helper, not an input asserting
agreement at all primes for the original elliptic curve. -/
theorem complexPolynomial_of_adicPolynomial (E : WeierstrassCurve ℚ)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime)
    (hP : (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) =
      rationalNewformPolynomial M ℓ b p) :
    (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℂ) =
      newformEulerPolynomial F hχ p := by
  have hc₁ := congrArg (fun P : Polynomial ℚ_[ℓ] => P.coeff 1) hP
  have hc₂ := congrArg (fun P : Polynomial ℚ_[ℓ] => P.coeff 2) hP
  have h₁ : ((localPolynomialQ E (primeIdealQ p hp)).coeff 1 : ℚ_[ℓ]) = -(b p : ℚ_[ℓ]) := by
    simpa [rationalNewformPolynomial, Polynomial.coeff_one] using hc₁
  have h₂ : ((localPolynomialQ E (primeIdealQ p hp)).coeff 2 : ℚ_[ℓ]) =
      if Nat.Coprime p M then (p : ℚ_[ℓ]) else 0 := by
    simpa [rationalNewformPolynomial, Polynomial.coeff_one] using hc₂
  have hE : (E.LFunction p : ℚ_[ℓ]) = (b p : ℚ_[ℓ]) := by
    rw [lFunction_prime_eq_neg_localPolynomial_coeff E p hp, Int.cast_neg, h₁, neg_neg]
  have hEQ : (E.LFunction p : ℚ) = b p := by exact_mod_cast hE
  have hEC : (E.LFunction p : ℂ) = (b p : ℂ) := by exact_mod_cast hEQ
  have hquad : ((localPolynomialQ E (primeIdealQ p hp)).coeff 2 : ℂ) =
      if Nat.Coprime p M then (p : ℂ) else 0 := by
    by_cases hcop : Nat.Coprime p M
    · rw [ite_eq_left hcop] at h₂ ⊢
      have hi : (localPolynomialQ E (primeIdealQ p hp)).coeff 2 = (p : ℤ) := by exact_mod_cast h₂
      rw [hi, Int.cast_natCast]
    · rw [ite_eq_right hcop] at h₂ ⊢
      have hi : (localPolynomialQ E (primeIdealQ p hp)).coeff 2 = 0 := by exact_mod_cast h₂
      rw [hi, Int.cast_zero]
  rw [localPolynomialQ_shape E p hp]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_one,
    Int.coe_castRingHom]
  rw [hEC, hquad, newformEulerPolynomial, hb p]

/-- **PROVED**, a different auxiliary prime can always be chosen.
Locator: the definition `Nat.Prime`, with witnesses `2` and `3`. Using this
lemma in the assembly respects Carayol's condition `p ≠ ℓ` at every prime,
including both primes of auxiliary characteristic. -/
theorem exists_auxiliary_prime_ne (p : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ p ≠ ℓ := by
  by_cases hp : p = 2
  · exact ⟨3, by decide, by omega⟩
  · exact ⟨2, by decide, hp⟩

end ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
