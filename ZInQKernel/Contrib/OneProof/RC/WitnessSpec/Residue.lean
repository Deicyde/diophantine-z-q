import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! The chosen place of tex 8365–8369 supplies a common residue field for the
finite extensions used in tex 8392–8398. Quotient maps and their compatibility
are spelled out on-the-spot (c). -/

noncomputable section

open NumberField Polynomial
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ IsFrobAt)
open scoped NumberField

namespace ZInQ.Manuscript.RC.WitnessSpec

/-- Keep the prime ideal witnessing the Frobenius, rather than choosing another
prime above the same rational prime. -/
structure FrobeniusPlace (g : GQ) (p : ℕ) where
  prime : Ideal Zbar
  isPrime : prime.IsPrime
  under : prime.under ℤ = Ideal.span {(p : ℤ)}
  frob : ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ prime

/-- Retain a prime witnessing the existing absolute Frobenius condition. -/
def FrobeniusPlace.ofIsFrobAt {g : GQ} {p : ℕ} (h : IsFrobAt g p) :
    FrobeniusPlace g p :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2⟩

namespace FrobeniusPlace

attribute [local instance] Ideal.Quotient.field

variable {g : GQ} {p : ℕ} (v : FrobeniusPlace g p)

instance : v.prime.IsPrime := v.isPrime

instance [Fact p.Prime] : v.prime.IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_under v.prime
    (v.under.symm ▸ Int.ideal_span_isMaximal_of_prime p)

/-- Arithmetic Frobenius on the common residue coordinates is the p-th power. -/
theorem frob_on_integers (x : Zbar) :
    Ideal.Quotient.mk v.prime (galRestrictHom ℤ ℚ Qbar Zbar g.toAlgHom x) =
      (Ideal.Quotient.mk v.prime x) ^ p := by
  let q : Zbar →+* Zbar ⧸ v.prime := Ideal.Quotient.mk v.prime
  let z : Zbar := galRestrictHom ℤ ℚ Qbar Zbar g.toAlgHom x
  have hz : z - x ^ p ∈ v.prime := by
    apply v.frob
    change algebraMap Zbar Qbar (z - x ^ p) = _
    rw [map_sub, map_pow, algebraMap_galRestrictHom_apply]
    rfl
  change q z = q x ^ p
  exact (Ideal.Quotient.eq.mpr hz).trans (q.map_pow x p)

/-- The common residue quotient has the characteristic of the rational prime. -/
instance charP [Fact p.Prime] : CharP (Zbar ⧸ v.prime) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have hmem : (p : ℤ) ∈ v.prime.under ℤ := v.under.symm ▸ Ideal.subset_span rfl
    have hzero := (Ideal.Quotient.eq_zero_iff_mem (I := v.prime)).mpr hmem
    simpa only [map_natCast, map_intCast, Int.cast_natCast] using hzero)

/-- The absolute residue quotient is algebraically closed: lift a monic
polynomial and reduce an algebraic integer root. -/
theorem isAlgClosed_residue [Fact p.Prime] : IsAlgClosed (Zbar ⧸ v.prime) := by
  apply IsAlgClosed.of_exists_root
  intro f hmon hf
  let q := Ideal.Quotient.mk v.prime
  obtain ⟨F, hF, hdeg, hm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts f).mpr (Polynomial.map_surjective q Ideal.Quotient.mk_surjective f)) hmon
  have hd : F.degree ≠ 0 := by
    rw [hdeg, degree_eq_natDegree hmon.ne_zero]
    exact_mod_cast (Irreducible.natDegree_pos hf).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective Qbar
    (IsIntegralClosure.algebraMap_injective Zbar ℤ Qbar) F hd
  have hxint : IsIntegral ℤ x := isIntegral_trans x (IsIntegral.of_aeval_monic hm
    (fun h => hd (by rw [degree_eq_natDegree hm.ne_zero, h]; rfl))
    (by rw [hx]; exact isIntegral_zero))
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := Zbar) (B := Qbar)).mp hxint
  refine ⟨q y, ?_⟩
  have h0 : F.eval y = 0 := by
    apply IsIntegralClosure.algebraMap_injective Zbar ℤ Qbar
    rw [map_zero]
    rw [← hy, aeval_algebraMap_apply_eq_algebraMap_eval] at hx
    exact hx
  rw [← hF, eval_map_apply, h0, map_zero]

instance residueAlgebra [Fact p.Prime] : Algebra (ZMod p) (Zbar ⧸ v.prime) :=
  (ZMod.castHom (dvd_rfl : p ∣ p) (Zbar ⧸ v.prime)).toAlgebra

/-- The geometric residue field is algebraic over the prime field. -/
theorem isAlgebraic_residue [Fact p.Prime] :
    Algebra.IsAlgebraic (ZMod p) (Zbar ⧸ v.prime) := by
  constructor
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : IsIntegral ℤ y := Algebra.IsIntegral.isIntegral y
  have hx : IsIntegral ℤ (Ideal.Quotient.mk v.prime y) :=
    hy.map (Ideal.Quotient.mkₐ ℤ v.prime)
  let : IsScalarTower ℤ (ZMod p) (Zbar ⧸ v.prime) :=
    IsScalarTower.of_algebraMap_eq fun a => by simp only [eq_intCast, map_intCast]
  exact (hx.tower_top (A := ZMod p)).isAlgebraic

/-- Any finite set of reductions (the witness, a division point and the
level torsion coordinates) is contained in one finite subfield of the
common residue quotient. -/
theorem exists_commonFiniteResidue [Fact p.Prime] (s : Finset (Zbar ⧸ v.prime)) :
    ∃ k : IntermediateField (ZMod p) (Zbar ⧸ v.prime), Finite k ∧
      (s : Set (Zbar ⧸ v.prime)) ⊆ k := by
  let k := IntermediateField.adjoin (ZMod p) (s : Set (Zbar ⧸ v.prime))
  have ha := v.isAlgebraic_residue
  let : Finite (s : Set (Zbar ⧸ v.prime)) := s.finite_toSet.to_subtype
  let : FiniteDimensional (ZMod p) k :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (ha.1 x).isIntegral)
  let b := Module.finBasis (ZMod p) k
  exact ⟨k, Finite.of_injective b.repr b.repr.injective, IntermediateField.subset_adjoin _ _⟩

/-- The chosen square root specializes to a unit fixed by arithmetic Frobenius. -/
theorem split_root_residue [Fact p.Prime] {D : ℤ} (hD : ¬ (p : ℤ) ∣ D)
    (x : Zbar) (hx : x ^ 2 = (D : Zbar)) (hfix : g (x : Qbar) = (x : Qbar)) :
    (Ideal.Quotient.mk v.prime x) ≠ 0 ∧
      (Ideal.Quotient.mk v.prime x) ^ p = Ideal.Quotient.mk v.prime x := by
  let q := Ideal.Quotient.mk v.prime
  have hfix' : galRestrictHom ℤ ℚ Qbar Zbar g.toAlgHom x = x := by
    apply IsIntegralClosure.algebraMap_injective Zbar ℤ Qbar
    rw [algebraMap_galRestrictHom_apply]
    exact hfix
  have hf := v.frob_on_integers x
  rw [hfix'] at hf
  refine ⟨?_, hf.symm⟩
  intro hz
  have he : q (x ^ 2) = q (D : Zbar) := congrArg q hx
  rw [q.map_pow x 2] at he
  change q x = 0 at hz
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at he
  exact hD ((CharP.intCast_eq_zero_iff (Zbar ⧸ v.prime) p D).mp (by
    simpa only [map_intCast] using he.symm))

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The integers of an embedded field map into the absolute integers. -/
def integersMap (e : L →ₐ[ℚ] Qbar) : 𝓞 L →+* Zbar :=
  (galRestrict' ℤ (𝓞 L) Zbar e).toRingHom

/-- The prime in an embedded field is the contraction of the selected prime. -/
def restrictPrime (e : L →ₐ[ℚ] Qbar) : Ideal (𝓞 L) :=
  v.prime.comap (integersMap e)

instance (e : L →ₐ[ℚ] Qbar) : (v.restrictPrime e).IsPrime :=
  Ideal.IsPrime.comap _

/-- The restricted prime lies over the same rational prime. -/
theorem restrictPrime_under (e : L →ₐ[ℚ] Qbar) :
    (v.restrictPrime e).under ℤ = Ideal.span {(p : ℤ)} := by
  rw [← v.under]
  ext a
  simp only [restrictPrime, Ideal.under_def, Ideal.mem_comap, eq_intCast, map_intCast]

/-- Embed each contracted residue field in the common quotient. The definition
also works when an embedded field is not stable under the chosen element. -/
def residueMap (e : L →ₐ[ℚ] Qbar) : 𝓞 L ⧸ v.restrictPrime e →+* Zbar ⧸ v.prime :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk v.prime).comp (integersMap e)) fun _ hx =>
    Ideal.Quotient.eq_zero_iff_mem.mpr hx

/-- The common quotient map agrees with ordinary reduction on each embedded
ring of integers. -/
theorem residueMap_mk (e : L →ₐ[ℚ] Qbar) (x : 𝓞 L) :
    v.residueMap e (Ideal.Quotient.mk (v.restrictPrime e) x) =
      Ideal.Quotient.mk v.prime (integersMap e x) := rfl

instance restrictPrime_isMaximal [Fact p.Prime] (e : L →ₐ[ℚ] Qbar) :
    (v.restrictPrime e).IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_under (v.restrictPrime e)
    ((v.restrictPrime_under e).symm ▸ Int.ideal_span_isMaximal_of_prime p)

/-- Restrict the chosen Frobenius to an embedded field stable under it. -/
theorem restrict_frobenius [Algebra.IsAlgebraic ℚ L] [Fact p.Prime] (e : L →ₐ[ℚ] Qbar)
    (σ : L ≃ₐ[ℚ] L) (hσ : ∀ x, e (σ x) = g (e x)) :
    (galRestrictHom ℤ ℚ L (𝓞 L) σ.toAlgHom).IsArithFrobAt (v.restrictPrime e) := by
  intro x
  rw [v.restrictPrime_under e, ZInQ.Contrib.ChebFD.C10.card_quot p]
  change integersMap e ((galRestrictHom ℤ ℚ L (𝓞 L) σ.toAlgHom) x - x ^ p) ∈ v.prime
  refine v.frob (integersMap e x) _ ?_
  change algebraMap Zbar Qbar (integersMap e _) =
    g (algebraMap Zbar Qbar (integersMap e x)) - (algebraMap Zbar Qbar (integersMap e x)) ^ p
  simp only [integersMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    algebraMap_galRestrict'_apply, map_sub, map_pow, algebraMap_galRestrictHom_apply,
    AlgEquiv.coe_toAlgHom, hσ]

/-- A residue field with p² elements maps to the points fixed by the square of
p-power Frobenius on the common residue coordinates. -/
theorem residueMap_pow_sq [Fact p.Prime] (e : L →ₐ[ℚ] Qbar)
    (hcard : Nat.card (𝓞 L ⧸ v.restrictPrime e) = p ^ 2)
    (x : 𝓞 L ⧸ v.restrictPrime e) :
    (v.residueMap e x) ^ (p ^ 2) = v.residueMap e x := by
  let : Finite (𝓞 L ⧸ v.restrictPrime e) :=
    Nat.finite_of_card_ne_zero (hcard.symm ▸ pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  let := Fintype.ofFinite (𝓞 L ⧸ v.restrictPrime e)
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hcard] at h
  rw [← map_pow (v.residueMap e) x (p ^ 2), h]

#print axioms FrobeniusPlace.ofIsFrobAt
#print axioms frob_on_integers
#print axioms charP
#print axioms isAlgClosed_residue
#print axioms residueAlgebra
#print axioms isAlgebraic_residue
#print axioms exists_commonFiniteResidue
#print axioms split_root_residue
#print axioms integersMap
#print axioms restrictPrime
#print axioms restrictPrime_under
#print axioms residueMap
#print axioms residueMap_mk
#print axioms restrict_frobenius
#print axioms residueMap_pow_sq

end FrobeniusPlace

end ZInQ.Manuscript.RC.WitnessSpec
