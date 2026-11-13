import ZInQKernel.Contrib.LocalSquareRoot.Cyclotomic
import ZInQKernel.Contrib.UnramifiedCocycle.FiniteQuotient

/-!
# Actual local Frobenius quotients from prime-to-p cyclotomic levels

This additive T31 module uses the unchanged finite Frobenius declarations of
`LocalSquareRoot` at PR46 revision `e0138213a452463b950166d51d2172bc48a95a19`.
It does not use a local-Kronecker-Weber proposition or a square-root criterion.
The cyclic coordinate is fixed by the explicit generator `p`, not by an
arbitrary cyclic-group isomorphism.  The local character is the original
cyclotomic character pulled through the actual baseline `resp`.

The original six UnramifiedCocycle modules and research note are unchanged.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2 GlueDescent.B2Q
open ZInQ.Contrib.LocalSquareRoot

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The prime-to-p level supplying residue Frobenius degree `n`. -/
def unramifiedLevel (p : Nat.Primes) (n : ℕ) : ℕ := (p : ℕ) ^ n - 1

theorem unramifiedLevel_pos (p : Nat.Primes) (n : ℕ) [NeZero n] :
    0 < unramifiedLevel p n := by
  have h := Nat.le_self_pow (NeZero.ne n) (p : ℕ)
  have hp := p.2.two_le
  unfold unramifiedLevel
  omega

instance neZero_unramifiedLevel (p : Nat.Primes) (n : ℕ) [NeZero n] :
    NeZero (unramifiedLevel p n) := ⟨(unramifiedLevel_pos p n).ne'⟩

/-- The specified arithmetic Frobenius generator in the root-action image. -/
noncomputable def frobeniusUnit (p : Nat.Primes) (n : ℕ) [NeZero n] :
    (ZMod (unramifiedLevel p n))ˣ :=
  ZMod.unitOfCoprime (p : ℕ) (GlueSqrtDisj.coprime_pow_sub_one p.2.two_le (NeZero.pos n))

theorem frobeniusUnit_order (p : Nat.Primes) (n : ℕ) [NeZero n] :
    orderOf (frobeniusUnit p n) = n :=
  GlueSqrtDisj.orderOf_unit_pow_sub_one p.2.two_le (NeZero.pos n)

noncomputable abbrev FrobeniusSubgroup (p : Nat.Primes) (n : ℕ) [NeZero n] :=
  Subgroup.zpowers (frobeniusUnit p n)

noncomputable def frobeniusGenerator (p : Nat.Primes) (n : ℕ) [NeZero n] :
    FrobeniusSubgroup p n := ⟨frobeniusUnit p n, ⟨1, by simp⟩⟩

theorem frobeniusGenerator_generates (p : Nat.Primes) (n : ℕ) [NeZero n] :
    ∀ x : FrobeniusSubgroup p n, x ∈ Subgroup.zpowers (frobeniusGenerator p n) := by
  intro x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, Subtype.ext ?_⟩
  simpa only [Subgroup.coe_zpow, frobeniusGenerator] using hk

theorem frobeniusSubgroup_card (p : Nat.Primes) (n : ℕ) [NeZero n] :
    Nat.card (FrobeniusSubgroup p n) = n := by
  rw [Nat.card_zpowers, frobeniusUnit_order]

/-- Explicit Frobenius coordinate: the residue class of `1` maps to `p`. -/
noncomputable def frobeniusPowerEquiv (p : Nat.Primes) (n : ℕ) [NeZero n] :
    CyclicGroup n ≃* FrobeniusSubgroup p n :=
  zmodMulEquivOfGenerator (frobeniusGenerator_generates p n) (frobeniusSubgroup_card p n)

theorem frobeniusPowerEquiv_apply_int (p : Nat.Primes) (n : ℕ) [NeZero n] (k : ℤ) :
    (frobeniusPowerEquiv p n (Multiplicative.ofAdd (k : ZMod n)) :
      (ZMod (unramifiedLevel p n))ˣ) = frobeniusUnit p n ^ k := by
  simp only [frobeniusPowerEquiv, zmodMulEquivOfGenerator_apply_ofAdd_intCast,
    Subgroup.coe_zpow, frobeniusGenerator]

/-- Root character on the actual local absolute Galois group and the actual `resp`. -/
noncomputable def localRootCharacter (p : Nat.Primes) (m : ℕ) [NeZero m] :
    GQp p →* (ZMod m)ˣ := (cyc m).comp (resp p)

theorem localRootCharacter_locallyConstant (p : Nat.Primes) (m : ℕ) [NeZero m] :
    IsLocallyConstant (localRootCharacter p m) :=
  (cyc_isLocallyConstant m).comp_continuous (resp_continuous p)

theorem finiteRootCharacter_range (p : Nat.Primes) (n : ℕ) [NeZero n] :
    (finiteCyc (p : ℕ) (unramifiedLevel p n)).range = FrobeniusSubgroup p n := by
  have hm : ¬ (p : ℕ) ∣ unramifiedLevel p n :=
    (Nat.Prime.coprime_iff_not_dvd p.2).mp
      (GlueSqrtDisj.coprime_pow_sub_one p.2.two_le (NeZero.pos n))
  exact GlueSqrtLocal.range_autToPow_eq_zpowers' (p : ℕ)
    (GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)) hm
    (IsCyclotomicExtension.zeta_spec (unramifiedLevel p n) ℚ_[p]
      (GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)))

/-- The finite local root action in explicit Frobenius coordinates. -/
noncomputable def finiteFrobeniusQuotient (p : Nat.Primes) (n : ℕ) [NeZero n] :
    Gal(GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)/ℚ_[p]) →* CyclicGroup n :=
  (frobeniusPowerEquiv p n).symm.toMonoidHom.comp
    ((finiteCyc (p : ℕ) (unramifiedLevel p n)).codRestrict (FrobeniusSubgroup p n)
      (fun g => by rw [← finiteRootCharacter_range p n]; exact ⟨g, rfl⟩))

/-- The actual finite-level quotient of `GQp`; no lift or quotient data are assumed. -/
noncomputable def localFrobeniusQuotient (p : Nat.Primes) (n : ℕ) [NeZero n] :
    GQp p →* CyclicGroup n :=
  (finiteFrobeniusQuotient p n).comp
    (AlgEquiv.restrictNormalHom (GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)))

theorem localFrobeniusQuotient_continuous (p : Nat.Primes) (n : ℕ) [NeZero n] :
    Continuous (localFrobeniusQuotient p n) := by
  have hfinite : Continuous (finiteFrobeniusQuotient p n) := continuous_of_discreteTopology
  exact hfinite.comp (InfiniteGalois.restrictNormalHom_continuous
    (GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)))

theorem localFrobeniusQuotient_locallyConstant (p : Nat.Primes) (n : ℕ) [NeZero n] :
    IsLocallyConstant (localFrobeniusQuotient p n) :=
  (IsLocallyConstant.of_discrete (finiteFrobeniusQuotient p n)).comp_continuous
    (InfiniteGalois.restrictNormalHom_continuous
      (GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n)))

/-- The constructed cyclic coordinate gives exactly the original root character. -/
theorem localFrobeniusQuotient_character (p : Nat.Primes) (n : ℕ) [NeZero n] (g : GQp p) :
    (frobeniusPowerEquiv p n (localFrobeniusQuotient p n g) :
      (ZMod (unramifiedLevel p n))ˣ) = localRootCharacter p (unramifiedLevel p n) g := by
  change ((frobeniusPowerEquiv p n)
    ((frobeniusPowerEquiv p n).symm
      ⟨finiteCyc (p : ℕ) (unramifiedLevel p n)
        (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) (unramifiedLevel p n))), _⟩) :
      (ZMod (unramifiedLevel p n))ˣ) = _
  rw [MulEquiv.apply_symm_apply]
  exact finiteCyc_restrict_eq_cyc p (unramifiedLevel p n) g

theorem finiteFrobeniusQuotient_surjective (p : Nat.Primes) (n : ℕ) [NeZero n] :
    Function.Surjective (finiteFrobeniusQuotient p n) := by
  intro x
  have hx : (frobeniusPowerEquiv p n x : (ZMod (unramifiedLevel p n))ˣ) ∈
      (finiteCyc (p : ℕ) (unramifiedLevel p n)).range := by
    rw [finiteRootCharacter_range p n]
    exact (frobeniusPowerEquiv p n x).property
  obtain ⟨g, hg⟩ := hx
  refine ⟨g, ?_⟩
  apply (frobeniusPowerEquiv p n).injective
  apply Subtype.val_injective
  change ((frobeniusPowerEquiv p n)
    ((frobeniusPowerEquiv p n).symm ⟨finiteCyc (p : ℕ) (unramifiedLevel p n) g, _⟩) :
      (ZMod (unramifiedLevel p n))ˣ) = _
  rw [MulEquiv.apply_symm_apply]
  exact hg

theorem localFrobeniusQuotient_surjective (p : Nat.Primes) (n : ℕ) [NeZero n] :
    Function.Surjective (localFrobeniusQuotient p n) :=
  (finiteFrobeniusQuotient_surjective p n).comp
    (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ_[p]))

/-- Divisibility for the actual doubled unramified cyclotomic level. -/
theorem unramifiedLevel_dvd_double (p : Nat.Primes) (n : ℕ) :
    unramifiedLevel p n ∣ unramifiedLevel p (2 * n) :=
  Nat.pow_sub_one_dvd_pow_sub_one (p : ℕ) (dvd_double n)

noncomputable def rootLevelReduction (p : Nat.Primes) (n : ℕ) [NeZero n] :
    (ZMod (unramifiedLevel p (2 * n)))ˣ →* (ZMod (unramifiedLevel p n))ˣ :=
  Units.map (ZMod.castHom (unramifiedLevel_dvd_double p n)
    (ZMod (unramifiedLevel p n))).toMonoidHom

theorem rootLevelReduction_frobeniusUnit (p : Nat.Primes) (n : ℕ) [NeZero n] :
    rootLevelReduction p n (frobeniusUnit p (2 * n)) = frobeniusUnit p n := by
  apply Units.ext
  change ZMod.castHom (unramifiedLevel_dvd_double p n) (ZMod (unramifiedLevel p n))
    (frobeniusUnit p (2 * n) : ZMod (unramifiedLevel p (2 * n))) =
      (frobeniusUnit p n : ZMod (unramifiedLevel p n))
  simp only [frobeniusUnit]
  exact map_natCast _ (p : ℕ)

/-- Cyclotomic reduction on the original global Galois group.  The proof checks
its action on a primitive smaller root; it does not assume compatibility. -/
theorem cyc_reduce {a b : ℕ} [NeZero a] [NeZero b] (hab : a ∣ b) (σ : GQ) :
    Units.map (ZMod.castHom hab (ZMod a)).toMonoidHom (cyc b σ) = cyc a σ := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) a
  let z : (AlgebraicClosure ℚ)ˣ := (hζ.isUnit (NeZero.ne a)).unit
  have hz : z ^ a = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, z, IsUnit.unit_spec]
      using hζ.pow_eq_one
  have hzb : z ∈ rootsOfUnity b (AlgebraicClosure ℚ) := by
    change z ^ b = 1
    obtain ⟨k, rfl⟩ := hab
    rw [pow_mul, hz, one_pow]
  have hbig := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) b) (toRingAut σ) hzb
  have hacts : act σ (z : AlgebraicClosure ℚ) = toRingAut σ (z : AlgebraicClosure ℚ) := rfl
  have hbig' := hacts.trans hbig
  have hs : act σ ζ = ζ ^ (cyc b σ : ZMod b).val := by
    simpa only [cyc, MonoidHom.comp_apply, z, IsUnit.unit_spec,
      Units.val_pow_eq_pow_val] using hbig'
  have hsmall := GlueSqrtLocal.autToPow_eq_of_apply hζ (act σ) (cyc b σ : ZMod b).val hs
  have hunit : cyc a σ = hζ.autToPow ℚ (act σ) := cyc_eq_autToPow hζ σ
  apply Units.ext
  change ZMod.castHom hab (ZMod a) (cyc b σ : ZMod b) = (cyc a σ : ZMod a)
  calc
    _ = ((cyc b σ : ZMod b).val : ZMod a) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    _ = (hζ.autToPow ℚ (act σ) : ZMod a) := hsmall.symm
    _ = (cyc a σ : ZMod a) := congrArg (fun u : (ZMod a)ˣ => (u : ZMod a)) hunit.symm

/-- The explicit Frobenius generators make the residue-coordinate reduction
agree with the actual root-character reduction. -/
theorem frobeniusPowerEquiv_reduction (p : Nat.Primes) (n : ℕ) [NeZero n]
    (x : CyclicGroup (2 * n)) :
    (frobeniusPowerEquiv p n (cyclicReduction n x) : (ZMod (unramifiedLevel p n))ˣ) =
      rootLevelReduction p n
        (frobeniusPowerEquiv p (2 * n) x : (ZMod (unramifiedLevel p (2 * n)))ˣ) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  have hx : x = Multiplicative.ofAdd (k : ZMod (2 * n)) := by
    apply Multiplicative.toAdd.injective
    exact hk.symm
  have hred : cyclicReduction n (Multiplicative.ofAdd (k : ZMod (2 * n))) =
      Multiplicative.ofAdd (k : ZMod n) := by
    change Multiplicative.ofAdd (ZMod.castHom (dvd_double n) (ZMod n) (k : ZMod (2 * n))) = _
    exact congrArg Multiplicative.ofAdd (map_intCast (ZMod.castHom (dvd_double n) (ZMod n)) k)
  rw [hx, hred, frobeniusPowerEquiv_apply_int, frobeniusPowerEquiv_apply_int,
    map_zpow, rootLevelReduction_frobeniusUnit]

/-- **Actual continuous doubled quotient lift**, for every prime and positive
`n`.  This proves the two local maps and their compatibility, not yet their
factorization of an arbitrary unramified number field's action. -/
theorem localFrobeniusQuotient_double_compatible (p : Nat.Primes) (n : ℕ) [NeZero n] :
    (cyclicReduction n).comp (localFrobeniusQuotient p (2 * n)) = localFrobeniusQuotient p n := by
  apply MonoidHom.ext
  intro g
  apply (frobeniusPowerEquiv p n).injective
  apply Subtype.val_injective
  change (frobeniusPowerEquiv p n (cyclicReduction n (localFrobeniusQuotient p (2 * n) g)) :
    (ZMod (unramifiedLevel p n))ˣ) = _
  rw [frobeniusPowerEquiv_reduction, localFrobeniusQuotient_character,
    localFrobeniusQuotient_character]
  exact cyc_reduce (unramifiedLevel_dvd_double p n) (resp p g)

end ZInQ.Contrib.UnramifiedCocycle
