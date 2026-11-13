import ZInQKernel.Contrib.UnramifiedCocycle.ActualEmbedding
import ZInQKernel.Contrib.UnramifiedCocycle.ResidueFrobenius

/-!
# The actual global integer ring inside a constructed local integer closure

The field map uses the exact embedding underlying `resp`.  Integrality is
transported from `ℤ` to `ℤ_p`, and the all-element equivariance equation uses
Mathlib's unchanged canonical integral-closure actions.  No separately chosen
localization or unidentified field equivalence is substituted.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2Q NumberField IsLocalRing
open ZInQ.Contrib.LocalSquareRoot
open scoped Pointwise

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

noncomputable abbrev LocalIntegerRing (p : Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (n : ℕ) [NeZero n] := integralClosure ℤ_[p] (localContainer p L n)

variable (p : Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] (n : ℕ) [NeZero n]

/-- The original global field mapped into the constructed finite local container. -/
noncomputable def globalLocalFieldHom : L →+* localContainer p L n where
  toFun x := ⟨localClosureEmbedding p (x : AlgebraicClosure ℚ),
    localClosureEmbedding_mem_container p L n x x.property⟩
  map_one' := Subtype.ext (map_one (localClosureEmbedding p))
  map_mul' x y := Subtype.ext (map_mul (localClosureEmbedding p)
    (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ))
  map_zero' := Subtype.ext (map_zero (localClosureEmbedding p))
  map_add' x y := Subtype.ext (map_add (localClosureEmbedding p)
    (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ))

/-- Its restriction to the original integer ring, still with the actual values. -/
noncomputable def globalIntegerFieldHom : 𝓞 L →+* localContainer p L n :=
  (globalLocalFieldHom p L n).comp (algebraMap (𝓞 L) L)

theorem globalIntegerFieldHom_integral (x : 𝓞 L) :
    IsIntegral ℤ_[p] (globalIntegerFieldHom p L n x) := by
  have h : IsIntegral ℤ (globalIntegerFieldHom p L n x) :=
    (NumberField.RingOfIntegers.isIntegral x).map (globalIntegerFieldHom p L n).toIntAlgHom
  exact h.tower_top

/-- The actual integer-ring embedding; its image lies in the local integral closure. -/
noncomputable def integerEmbedding : 𝓞 L →+* LocalIntegerRing p L n :=
  (globalIntegerFieldHom p L n).codRestrict
    (integralClosure ℤ_[p] (localContainer p L n)) (globalIntegerFieldHom_integral p L n)

section Galois
variable [IsGalois ℚ L]

/-- Exact compatibility on every global field element. -/
theorem globalLocalFieldHom_intertwines (g : GQp p) (x : L) :
    (localAct p g).restrictNormal (localContainer p L n) (globalLocalFieldHom p L n x) =
      globalLocalFieldHom p L n (localRestriction L p g x) := by
  apply Subtype.val_injective
  have h1 := AlgEquiv.restrictNormal_commutes (localAct p g) (localContainer p L n)
    (globalLocalFieldHom p L n x)
  have h2 := localClosureEmbedding_intertwines p g (x : AlgebraicClosure ℚ)
  have h3 := AlgEquiv.restrictNormal_commutes (act (resp p g)) L x
  exact h1.trans (h2.trans (congrArg (localClosureEmbedding p) h3.symm))

/-- Exact compatibility on ALL integer elements for the canonical two actions. -/
theorem integerEmbedding_intertwines (g : GQp p) (x : 𝓞 L) :
    (localAct p g).restrictNormal (localContainer p L n) • integerEmbedding p L n x =
      integerEmbedding p L n (localRestriction L p g • x) := by
  apply Subtype.val_injective
  change (localAct p g).restrictNormal (localContainer p L n)
      (globalLocalFieldHom p L n (x : L)) =
    globalLocalFieldHom p L n ((localRestriction L p g • x : 𝓞 L) : L)
  have hcoe : ((localRestriction L p g • x : 𝓞 L) : L) = localRestriction L p g (x : L) := rfl
  exact (globalLocalFieldHom_intertwines p L n g (x : L)).trans
    (congrArg (globalLocalFieldHom p L n) hcoe.symm)

end Galois

variable (Q : Ideal (LocalIntegerRing p L n)) [Q.IsMaximal]
  [Q.LiesOver (maximalIdeal ℤ_[p])]

/-- Reduction of the actual embedding at the specified local prime. -/
noncomputable def contractedResidueMap : 𝓞 L →+* (LocalIntegerRing p L n ⧸ Q) :=
  (Ideal.Quotient.mk Q).comp (integerEmbedding p L n)

/-- The actual contracted integer prime, not a substituted localization prime. -/
noncomputable def contractedPrime : Ideal (𝓞 L) :=
  RingHom.ker (contractedResidueMap p L n Q)

instance contractedPrime_isPrime : (contractedPrime p L n Q).IsPrime := by
  let : Field (LocalIntegerRing p L n ⧸ Q) := Ideal.Quotient.field Q
  exact RingHom.ker_isPrime (contractedResidueMap p L n Q)

theorem prime_mem_contractedPrime : ((p : ℤ) : 𝓞 L) ∈ contractedPrime p L n Q := by
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] :=
    ((Ideal.liesOver_iff Q (maximalIdeal ℤ_[p])).mp inferInstance).symm
  have hbase : (p : ℤ_[p]) ∈ Q.under ℤ_[p] := by
    rw [hunder, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have hQ : (p : LocalIntegerRing p L n) ∈ Q := by
    change algebraMap ℤ_[p] (LocalIntegerRing p L n) (p : ℤ_[p]) ∈ Q at hbase
    simpa only [map_natCast] using hbase
  change Ideal.Quotient.mk Q (integerEmbedding p L n ((p : ℤ) : 𝓞 L)) = 0
  have hmap : integerEmbedding p L n ((p : ℤ) : 𝓞 L) =
      ((p : ℤ) : LocalIntegerRing p L n) :=
    map_intCast (integerEmbedding p L n) (p : ℤ)
  have hQint : ((p : ℤ) : LocalIntegerRing p L n) ∈ Q := by
    simpa only [Int.cast_natCast] using hQ
  exact (congrArg (Ideal.Quotient.mk Q) hmap).trans
    (Ideal.Quotient.eq_zero_iff_mem.mpr hQint)

theorem contractedPrime_ne_bot : contractedPrime p L n Q ≠ ⊥ := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  intro hbot
  have h := prime_mem_contractedPrime p L n Q
  rw [hbot, Ideal.mem_bot] at h
  have hnat : ((p : ℕ) : 𝓞 L) = 0 := by
    simpa only [Int.cast_natCast] using h
  exact p.2.ne_zero (Nat.cast_eq_zero.mp hnat)

instance contractedPrime_isMaximal : (contractedPrime p L n Q).IsMaximal := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  exact Ideal.IsPrime.isMaximal inferInstance (contractedPrime_ne_bot p L n Q)

end ZInQ.Contrib.UnramifiedCocycle
