/-! ## lt-goodred (integration copy): neron-lg's DVR classification (from parts/10_copies.lean) -/

section LTGoodRedNLGSec

noncomputable section

namespace LTGoodRed.NLG

open NumberField

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end LTGoodRed.NLG

end

end LTGoodRedNLGSec

/-! ## lt-goodred §2: `GoodRedTorsion` (copied verbatim) and its proof

`GoodRedTorsion` is copied verbatim from `scratch/linked-tate/parts/98_g3tate.lean` (L33-62).
Proof (`goodRedTorsion`): with `Ω = \bar{L'}`,
* `g = qEmbRing L' : ℚ̄ → Ω` is bijective and `g ∘ resQ σ' = σ' ∘ g` (`resQ_spec`);
* `τ : Ω ≃ₐ[K] \bar K` (both are algebraic closures of `K`); `ψ = g⁻¹ ∘ τ⁻¹ : \bar K ≃ ℚ̄`;
* `w = ψ^*(v)`, a valuation ring of `\bar K`, and `O = w ∩ K`, a valuation ring of the number field
  `K` with `p ∈ 𝔪_O`, hence `≠ K` and a DVR (neron-lg's classification); `3` and `ℓⁿ` are units
  in `O` because they are prime to `p`;
* `σ_K = τ σ' τ⁻¹` lies in the inertia group of `w` (transport of the inertia condition of
  `resQ σ'` at `v` along `ψ`, using `ψ ∘ σ_K = resQ σ' ∘ ψ`);
* NOS (a) ⇒ (b) at `(O, w)` makes `σ_K` fix `A(\bar K)[ℓⁿ]`;
* the points: `E = trPt τ ∘ bcPt ∘ bcPt : A_{L,L'}(Ω) ≃* A(\bar K)` is multiplicative and carries the
  action of `σ'` to that of `σ_K` (`bcPt_galAct` twice, `trPt_galAct`). -/

section LTGoodRedSec

set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise

-- (`HSyn.LinkedTate.GoodRedTorsion` is linked-tate's own definition here)

namespace LTGoodRed

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-! ### Valuation rings: nonunits, coprime integers, inertia (Mathlib only) -/

section Val

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

/-- Nonunits of a pulled-back valuation ring. -/
theorem mem_nonunits_comap (A : ValuationSubring F₂) (ψ : F₁ ≃+* F₂) (x : F₁) :
    x ∈ (A.comap (ψ : F₁ →+* F₂)).nonunits ↔ ψ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  have h0 : x = 0 ↔ ψ x = 0 := (map_eq_zero_iff ψ ψ.injective).symm
  have h1 : (ψ : F₁ →+* F₂) x⁻¹ = (ψ x)⁻¹ := map_inv₀ ψ x
  rw [h1, h0]

/-- An integer prime to `p` is a unit in a valuation ring in which `p` is not. -/
theorem natCast_notMem_nonunits (A : ValuationSubring F₁) {p m : ℕ}
    (hp : (p : F₁) ∈ A.nonunits) (hm : Nat.Coprime m p) : (m : F₁) ∉ A.nonunits := by
  intro hmn
  have hp' : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hp
  have hm' : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hmn
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hm
  have hsum : (u : A) * (m : A) + (w : A) * (p : A) = 1 := by
    have := congrArg (Int.cast : ℤ → A) huw
    push_cast at this
    exact this
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hsum]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hp')
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The inverse of a nonzero element outside the nonunits lies in the ring. -/
theorem inv_mem_of_notMem_nonunits (A : ValuationSubring F₁) {x : F₁} (hx : x ∉ A.nonunits) :
    x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hx
  exact hx

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L]

/-- The concrete form of an inertia element: it preserves `A` and acts trivially modulo the
maximal ideal. -/
theorem of_mem_inertia (A : ValuationSubring L) (σ : A.decompositionSubgroup K)
    (hσ : σ ∈ A.inertiaSubgroup K) :
    (∀ x, (σ : L ≃ₐ[K] L) x ∈ A ↔ x ∈ A) ∧
      ∀ a ∈ A, (σ : L ≃ₐ[K] L) a - a ∈ A.nonunits := by
  have hs : (σ : L ≃ₐ[K] L) • A = A := σ.2
  constructor
  · intro x
    have key : ∀ y, y ∈ A ↔ ((σ : L ≃ₐ[K] L)⁻¹ • y) ∈ A := fun y => by
      conv_lhs => rw [← hs]
      exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
    rw [key ((σ : L ≃ₐ[K] L) x)]
    rw [show ((σ : L ≃ₐ[K] L)⁻¹ • (σ : L ≃ₐ[K] L) x) = x by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]]
  · intro a ha
    have h0 : (σ • IsLocalRing.residue A ⟨a, ha⟩ : IsLocalRing.ResidueField A) =
        IsLocalRing.residue A ⟨a, ha⟩ :=
      DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff] at h0
    exact h0

/-- Conversely, the concrete conditions give PkgI2's `IsInertia`. -/
theorem isInertia_of (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (h1 : ∀ x, σ x ∈ A ↔ x ∈ A) (h2 : ∀ a ∈ A, σ a - a ∈ A.nonunits) :
    PkgI2.IsInertia A σ := by
  have hd : σ ∈ A.decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h1 (σ⁻¹ • x)]
    rw [show σ (σ⁻¹ • x) = x by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]]
  refine ⟨hd, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ, hd⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a =
    IsLocalRing.residue A a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact h2 a a.2

end Val

/-! ### The proof of `GoodRedTorsion` -/

set_option maxHeartbeats 1000000 in
/-- **`GoodRedTorsion`, proved** (Mathlib, the copied `bcPt`/`trPt` and neron-lg's DVR
classification; NOS enters as the hypothesis of the Prop). -/
theorem goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion := by
  intro hNOS K L L' _ hKL hLL' A hA ℓ _
  letI hNF : NumberField L' := numberField_of_fd L'
  intro p hp hp3 hpl v hv σ' hσ n x hx
  -- `K` is a number field
  haveI hKfd : FiniteDimensional ℚ K := FiniteDimensional.of_injective
    (IntermediateField.inclusion (hKL.trans hLL')).toLinearMap
    (IntermediateField.inclusion (hKL.trans hLL')).toRingHom.injective
  haveI hKNF : NumberField K := numberField_of_fd K
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  letI iKL' : Algebra K L' := incAlg (hKL.trans hLL')
  haveI tKLL' : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tKL'Ω : IsScalarTower K L' (AlgebraicClosure L') := inferInstance
  haveI tKLΩ : IsScalarTower K L (AlgebraicClosure L') := IsScalarTower.of_algebraMap_eq
    (fun y => by
      rw [IsScalarTower.algebraMap_apply K L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply K L L'])
  -- `Ω = \bar{L'}` is an algebraic closure of `K`
  haveI tQKL' : IsScalarTower ℚ K L' := IsScalarTower.of_algebraMap_eq (fun q => by
    rw [eq_ratCast (algebraMap ℚ L') q, eq_ratCast (algebraMap ℚ K) q, map_ratCast])
  haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans K L' (AlgebraicClosure L')
  haveI : IsAlgClosure K (AlgebraicClosure L') := ⟨inferInstance, inferInstance⟩
  let τ : AlgebraicClosure L' ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure L') (AlgebraicClosure K)
  -- `g : ℚ̄ → Ω` is bijective
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L' := (G0Galois.qEmbRing L').toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : PkgI4.Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective (G0Galois.qEmbRing L') hgbij
  have hge : ∀ z, ge z = G0Galois.qEmbRing L' z := fun _ => rfl
  -- the transport `ψ : \bar K ≃ ℚ̄`, the place `w` of `\bar K` and `O = w ∩ K`
  let ψ : AlgebraicClosure K ≃+* PkgI4.Qbar := τ.symm.toRingEquiv.trans ge.symm
  have hψ : ∀ y, ψ y = ge.symm (τ.symm y) := fun _ => rfl
  let w : ValuationSubring (AlgebraicClosure K) := v.comap (ψ : AlgebraicClosure K →+* PkgI4.Qbar)
  let O : ValuationSubring K := w.comap (algebraMap K (AlgebraicClosure K))
  -- `p ∈ 𝔪_w`
  have hpw : ((p : ℕ) : AlgebraicClosure K) ∈ w.nonunits := by
    rw [mem_nonunits_comap v ψ, map_natCast]; exact hv
  -- integers prime to `p` are units of `O`
  have hunit : ∀ m : ℕ, Nat.Coprime m p → IsUnit (m : O) := by
    intro m hm
    obtain ⟨hm0, hmi⟩ := inv_mem_of_notMem_nonunits w (natCast_notMem_nonunits w hpw hm)
    have hm0K : (m : K) ≠ 0 := by
      intro h; apply hm0
      rw [← map_natCast (algebraMap K (AlgebraicClosure K)), h, map_zero]
    have hmO : (m : K)⁻¹ ∈ O := by
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]; exact hmi
    refine isUnit_iff_exists_inv.mpr ⟨⟨(m : K)⁻¹, hmO⟩, Subtype.ext ?_⟩
    push_cast
    exact mul_inv_cancel₀ hm0K
  -- `O ≠ K`: `p⁻¹ ∉ O`
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hpi : ((p : K))⁻¹ ∈ O := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
  haveI hODVR : IsDiscreteValuationRing O := NLG.isDiscreteValuationRing_of_ne_top O hOtop
  -- `3` and `ℓⁿ` are units in `O`
  have hp3' : p ≠ 3 := fun h => hp3 (by rw [h]; exact Finset.mem_singleton_self 3)
  have h3 : IsUnit (3 : O) := by
    have := hunit 3 ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3'))
    exact_mod_cast this
  have hℓp : Nat.Coprime (ℓ ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr (Ne.symm hpl))
  -- NOS (a) ⇒ (b) at `(O, w)`
  have htriv := ((hNOS K O w rfl (ObjBridge.toGrp A)).1.mp (hA O h3)) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by exact_mod_cast hunit (ℓ ^ n) hℓp)
  -- the inertia element `σ_K = τ σ' τ⁻¹` at `w`
  obtain ⟨σ, hσI, hσeq⟩ := hσ
  obtain ⟨hv1, hv2⟩ := of_mem_inertia ℚ v σ hσI
  rw [hσeq] at hv1 hv2
  let s' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L' := σ'
  let σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    (τ.symm.trans (s'.restrictScalars K)).trans τ
  have hσK : ∀ y, σK y = τ (s' (τ.symm y)) := fun _ => rfl
  have hres : ∀ y, ψ (σK y) = (G0Galois.resQ L' σ') (ψ y) := by
    intro y
    apply ge.injective
    show ge (ge.symm (τ.symm (σK y))) = ge ((G0Galois.resQ L' σ') (ge.symm (τ.symm y)))
    rw [RingEquiv.apply_symm_apply, hσK, AlgEquiv.symm_apply_apply]
    have hspec := G0Galois.resQ_spec L' σ' (ge.symm (τ.symm y))
    rw [← hge, ← hge, RingEquiv.apply_symm_apply] at hspec
    exact hspec.symm
  have hI : PkgI2.IsInertia w σK := by
    refine isInertia_of K w σK (fun y => ?_) (fun a ha => ?_)
    · show ψ (σK y) ∈ v ↔ ψ y ∈ v
      rw [hres]; exact hv1 (ψ y)
    · rw [mem_nonunits_comap v ψ, map_sub, hres]
      exact hv2 (ψ a) ha
  -- the points
  let E := (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
    (AlgebraicClosure L')).trans ((UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')).trans
      (UnramTate.trPt A τ))
  have hE : ∀ y, E ((@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y) =
      A.galAct σK (E y) := by
    intro y
    show UnramTate.trPt A τ (UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')
        (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
          (AlgebraicClosure L')
          ((@PkgI3.AbVar.baseChange L _
            (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y))) = _
    rw [UnramTate.bcPt_galAct, UnramTate.bcPt_galAct]
    exact UnramTate.trPt_galAct A τ _ σK (fun z => by rw [hσK, AlgEquiv.symm_apply_apply]; rfl) _
  have hEx : E x ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hfix : A.galAct σK (E x) = E x := htriv σK hI (E x) hEx
  apply E.injective
  exact (hE x).trans hfix

end LTGoodRed

end

end LTGoodRedSec

#print axioms LTGoodRed.goodRedTorsion

/-! ## lt-goodred §4: `QMEndRank` reduced to I3.M1, T27 and one algebraic glue Prop

* `rank ≥ 4` (proved, `four_le_finrank`): `𝒪 ≅ ℤ⁴` (`ofIntHom`) and `endBC ∘ endBC ∘ ι` is an
  injective ring map `𝒪 → End(A')`; `End(A')` is finite over `ℤ` by I3.M1.
* `rank ≤ rank End(A'_Ω)` (proved, `finrank_le_baseChange`): `endBC` is injective, I3.M1.
* T27 at `A'' = A'_Ω`, `Ω = \bar{L'}`: its hypotheses are proved here: `dim A'' = 2`
  (`pkgI3_dim_baseChange`, three times), `B = (2,−3)` is a division algebra (`quatB6_isUnit`: the
  norm form `x₀² − 2x₁² + 3x₂² − 6x₃²` is anisotropic over `ℚ`, 3-adic descent), and
  `B →ₐ[ℚ] End⁰(A'')` (`quatEmbed`, from `ι` and base change).
* Case `End⁰(A'') ≅ B`: `rank End(A'') = dim_ℚ End⁰(A'') = 4` (proved).
* Case `End⁰(A'') ≅ M₂(ℚ(√d))`, `d < 0`: the named glue Prop `QMSplitCaseRank`. -/

section LTQMRankSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField LeafQM
open scoped Quaternion TensorProduct

/-! ### `𝒪 ≅ ℤ⁴` and the lower bound -/

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [ofInt] at h0 h1 h2 h3
  have e2 : (n 2 : ℚ) = m 2 := by linarith
  have e3 : (n 3 : ℚ) = m 3 := by linarith
  have e0 : (n 0 : ℚ) = m 0 := by linarith
  have e1 : (n 1 : ℚ) = m 1 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

/-- `n ↦ ofInt n`, an additive bijection `ℤ⁴ → 𝒪`. -/
def ofIntHom : (Fin 4 → ℤ) →+ O where
  toFun n := ⟨ofInt n, n, rfl⟩
  map_zero' := Subtype.ext ofInt_zero
  map_add' n m := Subtype.ext (ofInt_add n m).symm

theorem ofIntHom_injective : Function.Injective ofIntHom :=
  fun n m h => ofInt_injective (congrArg Subtype.val h)

/-- **`rank End(A) ≥ 4` for a QM abelian variety** (proved; I3.M1 for finiteness). -/
theorem four_le_finrank (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k)
    (φ : O →+* PkgI3.AbVar.End A) (hφ : Function.Injective φ) :
    4 ≤ Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 k A A
  let F : (Fin 4 → ℤ) →+ PkgI3.AbVar.End A := φ.toAddMonoidHom.comp ofIntHom
  have hF : Function.Injective F := hφ.comp ofIntHom_injective
  have := LinearMap.finrank_le_finrank_of_injective (f := F.toIntLinearMap) hF
  rwa [Module.finrank_fin_fun] at this

/-- **`rank End(A) ≤ rank End(A_Ω)`** (proved; `endBC` is injective, I3.M1). -/
theorem finrank_le_baseChange (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k]
    (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [Algebra k Ω] :
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤
      Module.finrank ℤ (PkgI3.AbVar.End (A.baseChange Ω)) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (HSyn.LinkedTate.endBC A Ω).toAddMonoidHom.toIntLinearMap)
    (HSyn.LinkedTate.endBC_injective A Ω)

/-- `rank_ℤ End(A) = dim_ℚ End⁰(A)` (I3.M1: `End(A)` is free). -/
theorem finrank_end0 (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k) :
    Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨hfree, -, -, -⟩ := hM1 k A A
  exact Module.finrank_baseChange

/-! ### `B = (2, −3)` is a division algebra -/

theorem mod3_step (a b e : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * e = 0) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hc := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at hc
  have h' : ((a : ZMod 3)) ^ 2 + ((b : ZMod 3)) ^ 2 = 0 := by
    linear_combination hc + ((b : ZMod 3) ^ 2 - (e : ZMod 3)) * h3
  have key : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  obtain ⟨ha, hb⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb⟩

theorem pow3_dvd (k : ℕ) : ∀ a b c d : ℤ, a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 →
    3 ^ k ∣ a ∧ 3 ^ k ∣ b ∧ 3 ^ k ∣ c ∧ 3 ^ k ∣ d := by
  induction k with
  | zero => intro a b c d _; simp
  | succ k ih =>
    intro a b c d h
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := mod3_step a b (c ^ 2 - 2 * d ^ 2) (by linear_combination h)
    have h' : (3 : ℤ) * (c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2)) = 0 := by
      linear_combination h
    obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := mod3_step c d (a' ^ 2 - 2 * b' ^ 2)
      ((mul_eq_zero.mp h').resolve_left (by norm_num))
    have h'' : (9 : ℤ) * (a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2) = 0 := by
      linear_combination h
    obtain ⟨h1, h2, h3, h4⟩ := ih a' b' c' d' ((mul_eq_zero.mp h'').resolve_left (by norm_num))
    rw [pow_succ']
    exact ⟨mul_dvd_mul_left 3 h1, mul_dvd_mul_left 3 h2, mul_dvd_mul_left 3 h3,
      mul_dvd_mul_left 3 h4⟩

theorem eq_zero_of_pow3_dvd (a : ℤ) (h : ∀ k : ℕ, 3 ^ k ∣ a) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h a.natAbs)
  rw [Int.natAbs_pow]
  exact Nat.lt_pow_self (by norm_num)

/-- The norm form of `B` is anisotropic over `ℤ`. -/
theorem norm6_int (a b c d : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨eq_zero_of_pow3_dvd a fun k => (pow3_dvd k a b c d h).1,
    eq_zero_of_pow3_dvd b fun k => (pow3_dvd k a b c d h).2.1,
    eq_zero_of_pow3_dvd c fun k => (pow3_dvd k a b c d h).2.2.1,
    eq_zero_of_pow3_dvd d fun k => (pow3_dvd k a b c d h).2.2.2⟩

/-- The norm form of `B` is anisotropic over `ℚ`. -/
theorem norm6_rat (q0 q1 q2 q3 : ℚ) (h : q0 ^ 2 - 2 * q1 ^ 2 + 3 * q2 ^ 2 - 6 * q3 ^ 2 = 0) :
    q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  have hd0 : (q0.den : ℚ) ≠ 0 := by exact_mod_cast q0.den_nz
  have hd1 : (q1.den : ℚ) ≠ 0 := by exact_mod_cast q1.den_nz
  have hd2 : (q2.den : ℚ) ≠ 0 := by exact_mod_cast q2.den_nz
  have hd3 : (q3.den : ℚ) ≠ 0 := by exact_mod_cast q3.den_nz
  set D : ℚ := q0.den * q1.den * q2.den * q3.den with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 hd1) hd2) hd3
  have e0 : ((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ) = q0 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q0]; ring
  have e1 : ((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ) = q1 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q1]; ring
  have e2 : ((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ) = q2 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q2]; ring
  have e3 : ((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ) = q3 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q3]; ring
  have hZ := norm6_int (q0.num * q1.den * q2.den * q3.den) (q1.num * q0.den * q2.den * q3.den)
    (q2.num * q0.den * q1.den * q3.den) (q3.num * q0.den * q1.den * q2.den) (by
      have : (((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          - 2 * (((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          + 3 * (((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ)) ^ 2
          - 6 * (((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ)) ^ 2 = 0 := by
        rw [e0, e1, e2, e3]; linear_combination D ^ 2 * h
      exact_mod_cast this)
  obtain ⟨z0, z1, z2, z3⟩ := hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e0; rw [z0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e1; rw [z1, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e2; rw [z2, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e3; rw [z3, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0

/-- **`B = (2,−3)_ℚ` is a division algebra** (proved): `x · x̄ = n(x)` with `n` anisotropic. -/
theorem quatB6_isUnit : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x := by
  intro x hx
  have hn : (x * star x).re = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
    simp [QuaternionAlgebra.re_mul]; ring
  have hn0 : (x * star x).re ≠ 0 := by
    intro h0
    rw [hn] at h0
    obtain ⟨z0, z1, z2, z3⟩ := norm6_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext z0 z1 z2 z3)
  set n := (x * star x).re with hndef
  have hxs : x * star x = (n : ℍ[ℚ, 2, -3]) := QuaternionAlgebra.mul_star_eq_coe x
  have hsx : star x * x = (n : ℍ[ℚ, 2, -3]) := by rw [← hxs]; exact (star_comm_self' x)
  have hinv : (n⁻¹ : ℚ) • (n : ℍ[ℚ, 2, -3]) = 1 := by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hn0,
      QuaternionAlgebra.coe_one]
  refine isUnit_iff_exists.mpr ⟨n⁻¹ • star x, ?_, ?_⟩
  · rw [mul_smul_comm, hxs, hinv]
  · rw [smul_mul_assoc, hsx, hinv]

/-! ### `B →ₐ[ℚ] End⁰(A)` from a QM structure -/

/-- `i ∈ 𝒪`. -/
def oI' : O := ⟨ofInt ![0, 1, 0, 0], _, rfl⟩
/-- `j = 2·(1+j)/2 − 1 ∈ 𝒪`. -/
def oJ' : O := ⟨ofInt ![-1, 0, 2, 0], _, rfl⟩

theorem oI'_mul_oI' : oI' * oI' = 2 := by
  apply Subtype.ext
  show ofInt ![0, 1, 0, 0] * ofInt ![0, 1, 0, 0] = 2
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oJ' : oJ' * oJ' = -3 := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![-1, 0, 2, 0] = -3
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oI' : oJ' * oI' = -(oI' * oJ') := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![0, 1, 0, 0] = -(ofInt ![0, 1, 0, 0] * ofInt ![-1, 0, 2, 0])
  ext <;> simp [ofInt] <;> norm_num

/-- **`B →ₐ[ℚ] End⁰(A)` from a ring map `𝒪 → End(A)`** (proved: `i ↦ 1 ⊗ φ(i)`, `j ↦ 1 ⊗ φ(j)`,
Mathlib's `QuaternionAlgebra.Basis.liftHom`). -/
theorem quatEmbed {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : O →+* PkgI3.AbVar.End A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) := by
  let ψ : O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End0 A).toRingHom.comp φ
  refine ⟨QuaternionAlgebra.Basis.liftHom
    { i := ψ oI', j := ψ oJ', k := ψ oI' * ψ oJ',
      i_mul_i := ?_, j_mul_j := ?_, i_mul_j := rfl, j_mul_i := ?_ }⟩
  · rw [← map_mul, oI'_mul_oI', map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oJ', map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oI', map_neg, map_mul, zero_smul, zero_sub]

/-! ### The reduction -/

/-- **Glue (algebra; Albert's classification for simple abelian surfaces in characteristic 0,
Mumford §21, numbering UNVERIFIED): the split geometric case.** For an abelian surface `A` over a
field `k` of characteristic `0` with an injective ring map `ι : 𝒪 → End_k(A)` and `EndDivision A`,
if `End⁰(A_Ω) ≅ M₂(ℚ(√d))` (`d < 0`) for an algebraically closed `Ω ⊇ k`, then
`rank_ℤ End_k(A) ≤ 4`. Route (STANDARD): `End⁰(A)` embeds in `End⁰(A_Ω)` (`endBC`, flatness of
`ℚ/ℤ`) as a subalgebra `S ⊇ ι(B)`; `S` is a left `B`-vector space, so `dim_ℚ S ∈ {4, 8}`; if
`dim S = 8` then `S = M₂(ℚ(√d))` contains a nonzero nilpotent, whose integer multiple in
`End(A)` is a nonzero nilpotent endomorphism; a nilpotent endomorphism of a positive-dimensional
abelian variety is not surjective, contradicting `EndDivision`. GLUE. -/
def QMSplitCaseRank : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] (φ : O →+* PkgI3.AbVar.End A), Function.Injective φ → A.dim = 2 →
    PkgI3.EndDivision A → ∀ d : ℚ, d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤ 4

/-- **`QMEndRank`, proved** from the leaves I3.M1 (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3) and
T27 (`PkgI3.QMDichotomyYu`, Yu 2013 Thm 1.1) and the glue `QMSplitCaseRank`. -/
theorem qmEndRank_of (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu)
    (hS : QMSplitCaseRank) : HSyn.LinkedTate.QMEndRank := by
  intro K L L' _ hKL hLL' PK hdiv
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  set A' : PkgI3.AbVar L' := @PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL') with hA'
  let φ : O →+* PkgI3.AbVar.End A' :=
    (HSyn.LinkedTate.endBC (PK.A.baseChange L) L').comp
      ((HSyn.LinkedTate.endBC PK.A L).comp PK.q.iota)
  have hφ : Function.Injective φ :=
    (HSyn.LinkedTate.endBC_injective _ L').comp
      ((HSyn.LinkedTate.endBC_injective _ L).comp PK.q.injective)
  have hdimA' : A'.dim = 2 := by
    rw [hA', G0Dim.pkgI3_dim_baseChange, G0Dim.pkgI3_dim_baseChange]
    exact PK.surface
  refine le_antisymm ?_ (four_le_finrank hM1 A' φ hφ)
  -- the geometric endomorphism algebra
  let Ω := AlgebraicClosure L'
  let A'' : PkgI3.AbVar Ω := A'.baseChange Ω
  have hdimA'' : A''.dim = 2 := by
    show (A'.baseChange Ω).dim = 2
    rw [G0Dim.pkgI3_dim_baseChange]; exact hdimA'
  let φ'' : O →+* PkgI3.AbVar.End A'' := (HSyn.LinkedTate.endBC A' Ω).comp φ
  rcases hT27 Ω A'' hdimA'' 2 (-3) PkgI3.quatIndefinite_two_neg_three quatB6_isUnit
      (quatEmbed A'' φ'') with he | ⟨d, hd, he⟩
  · obtain ⟨e⟩ := he
    calc Module.finrank ℤ (PkgI3.AbVar.End A')
        ≤ Module.finrank ℤ (PkgI3.AbVar.End A'') := finrank_le_baseChange hM1 A' Ω
      _ = Module.finrank ℚ (PkgI3.AbVar.End0 A'') := (finrank_end0 hM1 A'').symm
      _ = Module.finrank ℚ ℍ[ℚ, 2, -3] := e.toLinearEquiv.finrank_eq
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  · exact hS L' A' Ω φ hφ hdimA' hdiv d hd he

end LTGoodRed.QM

end

end LTQMRankSec

#print axioms LTGoodRed.QM.quatB6_isUnit
#print axioms LTGoodRed.QM.quatEmbed
#print axioms LTGoodRed.QM.four_le_finrank
#print axioms LTGoodRed.QM.qmEndRank_of

/-! ## lt-goodred §5: `QMSplitCaseRank`, proved from I3.M1

Suppose `rank End(A) > 4`. Then (all proved below):
* `End⁰(A) ↪ End⁰(A_Ω) ≅ M₂(ℚ(√d))`, a `ℚ`-algebra embedding (`endBC` injective, `ℚ` flat over
  `ℤ`); so `dim_ℚ End⁰(A) ≤ 8`;
* `B →ₐ[ℚ] End⁰(A)` (`quatEmbed`) and `B` is a division algebra, so for `s ∉ θ(B)` the map
  `(b, b') ↦ θ(b) + θ(b')·s` is injective: `dim End⁰(A) ≥ 8` (`eight_le_finrank`);
* hence `End⁰(A) ≅ M₂(ℚ(√d))`, and the preimage `x` of `E₁₂` is a nonzero element with `x² = 0`;
* clearing denominators, `n·x = 1 ⊗ m` with `m ∈ End(A)`, `m ≠ 0`, `m² = 0` (`End(A)` is free,
  I3.M1, so `m ↦ 1 ⊗ m` is injective);
* a nonzero `m` is an isogeny (`EndDivision`), so `m ∘ m = 0` is surjective; but the zero
  endomorphism factors through `Spec k`, a point, so `A` would be a point, against `dim A = 2`
  (`eq_zero_of_mul_self_eq_zero`). -/

section LTSplitSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM
open scoped Quaternion TensorProduct

/-! ### A square-zero endomorphism of an `EndDivision` surface is zero -/

/-- **A square-zero endomorphism of a positive-dimensional `EndDivision` abelian variety is zero**
(proved): otherwise it is surjective (an isogeny), so its square, the zero endomorphism, is
surjective; the zero endomorphism factors through `Spec k`, so `A` is a point, of dimension `≤ 0`. -/
theorem eq_zero_of_mul_self_eq_zero {k : Type} [Field k] (A : PkgI3.AbVar k)
    (hdiv : PkgI3.EndDivision A) (hdim : A.dim = 2) (m : PkgI3.AbVar.End A) (hm : m * m = 0) :
    m = 0 := by
  by_contra hm0
  obtain ⟨-, hsurj⟩ := hdiv m hm0
  have hcomp : (m * m).hom = m.hom ≫ m.hom := rfl
  have h1 : m.hom ≫ m.hom = (1 : A.X ⟶ A.X) := by rw [← hcomp, hm]; rfl
  have hs : Surjective (m.hom ≫ m.hom).left := by
    rw [Over.comp_left]; infer_instance
  rw [h1, Hom.one_def, Over.comp_left] at hs
  haveI hsub : Subsingleton A.X.left := by
    constructor
    intro y1 y2
    obtain ⟨x1, rfl⟩ := hs.surj y1
    obtain ⟨x2, rfl⟩ := hs.surj y2
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hle : A.dim ≤ 0 := topologicalKrullDim_zero_of_discreteTopology A.X.left
  rw [hdim] at hle
  exact absurd hle (by decide)

/-! ### `ℚ ⊗ M` for a free `ℤ`-module `M` -/

section Tensor

variable {M : Type} [Ring M]

theorem intCast_smul_one_tmul (c : ℤ) (m : M) :
    ((c : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (c • m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
    show ((c : ℤ) : ℚ) = c • (1 : ℚ) by simp, TensorProduct.smul_tmul]

/-- Every element of `ℚ ⊗ M` has an integer multiple of the form `1 ⊗ m`. -/
theorem exists_smul_eq_tmul (x : ℚ ⊗[ℤ] M) :
    ∃ (n : ℤ) (m : M), n ≠ 0 ∧ (n : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] m := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    refine ⟨q.den, q.num • m, by exact_mod_cast q.den_nz, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul,
      show ((q.den : ℤ) : ℚ) * q = ((q.num : ℤ) : ℚ) by
        rw [Int.cast_natCast, mul_comm]; exact Rat.mul_den_eq_num q,
      show ((q.num : ℤ) : ℚ) = q.num • (1 : ℚ) by simp, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n, m, hn, h⟩ := hx
    obtain ⟨n', m', hn', h'⟩ := hy
    refine ⟨n * n', n' • m + n • m', mul_ne_zero hn hn', ?_⟩
    rw [smul_add, Int.cast_mul, mul_comm, mul_smul, h, mul_comm, mul_smul, h',
      intCast_smul_one_tmul, intCast_smul_one_tmul, TensorProduct.tmul_add]

/-- `m ↦ 1 ⊗ m` is injective for a free `ℤ`-module (flatness). -/
theorem one_tmul_injective [Module.Free ℤ M] :
    Function.Injective (fun m : M => (1 : ℚ) ⊗ₜ[ℤ] m) := by
  have hinj : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => by simpa using h)
  intro m m' h
  apply (TensorProduct.lid ℤ M).symm.injective
  apply hinj
  simpa [TensorProduct.lid_symm_apply] using h

end Tensor

/-! ### A copy of `B` and an element outside it give dimension `≥ 8` -/

theorem eight_le_finrank {R : Type} [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R]
    (θ : ℍ[ℚ, 2, -3] →ₐ[ℚ] R) (h4 : 4 < Module.finrank ℚ R) : 8 ≤ Module.finrank ℚ R := by
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at h4
    omega
  have hr : Module.finrank ℚ (LinearMap.range θ.toLinearMap) ≤ 4 := by
    calc _ ≤ Module.finrank ℚ ℍ[ℚ, 2, -3] := LinearMap.finrank_range_le _
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  obtain ⟨s, hs⟩ : ∃ s, s ∉ LinearMap.range θ.toLinearMap := by
    by_contra h
    push_neg at h
    have htop : LinearMap.range θ.toLinearMap = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, finrank_top] at hr
    omega
  have hunit : ∀ b : ℍ[ℚ, 2, -3], b ≠ 0 → ∃ c, θ c * θ b = 1 := by
    intro b hb
    obtain ⟨u, rfl⟩ := quatB6_isUnit b hb
    exact ⟨↑u⁻¹, by rw [← map_mul, Units.inv_mul, map_one]⟩
  let Lm : (ℍ[ℚ, 2, -3] × ℍ[ℚ, 2, -3]) →ₗ[ℚ] R :=
    θ.toLinearMap.comp (LinearMap.fst ℚ _ _) +
      ((LinearMap.mulRight ℚ s).comp θ.toLinearMap).comp (LinearMap.snd ℚ _ _)
  have hLm : ∀ b b', Lm (b, b') = θ b + θ b' * s := fun _ _ => rfl
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨b, b'⟩ h
    rw [hLm] at h
    by_cases hb' : b' = 0
    · subst hb'
      rw [map_zero, zero_mul, add_zero] at h
      by_cases hb : b = 0
      · rw [hb]; rfl
      · obtain ⟨c, hc⟩ := hunit b hb
        rw [h, mul_zero] at hc
        exact absurd hc zero_ne_one
    · exfalso
      obtain ⟨c, hc⟩ := hunit b' hb'
      apply hs
      refine ⟨-(c * b), ?_⟩
      show θ (-(c * b)) = s
      have : s = θ c * (θ b' * s) := by rw [← _root_.mul_assoc, hc, _root_.one_mul]
      rw [this, eq_neg_of_add_eq_zero_right h, map_neg, map_mul, mul_neg]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, QuaternionAlgebra.finrank_eq_four (R := ℚ) 2 0 (-3)] at this

/-! ### The proof -/

/-- **`QMSplitCaseRank`, proved** from I3.M1 (`PkgI3.HomFreeFinite`). -/
theorem qmSplitCaseRank (hM1 : PkgI3.HomFreeFinite) : QMSplitCaseRank := by
  intro k _ _ A Ω _ _ _ φ _ hdim hdiv d _ he
  obtain ⟨e⟩ := he
  obtain ⟨hfreeM, hfinM, -, -⟩ := hM1 k A A
  obtain ⟨hfreeN, hfinN, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  by_contra hlt
  push_neg at hlt
  -- `F = ℚ(√d)`, `dim_ℚ M₂(F) = 8`
  have hf : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) d
  have hF : Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) = 2 := by
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim,
      Polynomial.natDegree_X_pow_sub_C]
  haveI : Module.Finite ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) :=
    (AdjoinRoot.powerBasis hf).finite
  haveI : Nontrivial (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at hF
    omega
  have h8 : Module.finrank ℚ
      (Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) = 8 := by
    rw [Module.finrank_matrix, hF]; rfl
  -- `End⁰(A) ↪ End⁰(A_Ω)`
  let β : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End (A.baseChange Ω) :=
    (HSyn.LinkedTate.endBC A Ω).toIntAlgHom
  let Φ₀ : PkgI3.AbVar.End0 A →ₐ[ℚ] PkgI3.AbVar.End0 (A.baseChange Ω) :=
    Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) β
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hΦ₀ : Function.Injective Φ₀ := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) β.toLinearMap
      (HSyn.LinkedTate.endBC_injective A Ω)
    have heq : ⇑Φ₀ = ⇑(β.toLinearMap.lTensor ℚ) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul q m => simp [Φ₀, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [heq]; exact h
  let Φ := e.toAlgHom.comp Φ₀
  have hΦ : Function.Injective Φ := e.injective.comp hΦ₀
  -- dimensions
  have hrank : Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) :=
    finrank_end0 hM1 A
  obtain ⟨θ⟩ := quatEmbed A φ
  have hge : 8 ≤ Module.finrank ℚ (PkgI3.AbVar.End0 A) :=
    eight_le_finrank θ (by rw [hrank]; exact hlt)
  have hle : Module.finrank ℚ (PkgI3.AbVar.End0 A) ≤ 8 := by
    rw [← h8]; exact LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hΦ
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap)
      (by rw [h8]; omega)).mp hΦ
  -- the preimage of `E₁₂`
  let E : Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := !![0, 1; 0, 0]
  have hE0 : E ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [E] at this
  have hEE : E * E = 0 := by
    simp only [E, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨x, hx⟩ := hsurj E
  have hx0 : x ≠ 0 := by rintro rfl; exact hE0 (by rw [← hx, map_zero])
  have hxx : x * x = 0 := hΦ (by rw [map_mul, hx, hEE, map_zero])
  -- clearing denominators
  obtain ⟨n, m, hn, hnm⟩ := exists_smul_eq_tmul x
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, smul_eq_zero] at hnm
    rcases hnm with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 h
  have hmm : m * m = 0 := by
    apply one_tmul_injective (M := PkgI3.AbVar.End A)
    show (1 : ℚ) ⊗ₜ[ℤ] (m * m) = (1 : ℚ) ⊗ₜ[ℤ] (0 : PkgI3.AbVar.End A)
    rw [TensorProduct.tmul_zero, ← _root_.mul_one (1 : ℚ), ← Algebra.TensorProduct.tmul_mul_tmul,
      ← hnm, smul_mul_smul_comm, hxx, smul_zero]
  exact hm0 (eq_zero_of_mul_self_eq_zero A hdiv hdim m hmm)

/-- **`QMEndRank` from the leaves I3.M1 and T27 alone** (proved). -/
theorem qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) :
    HSyn.LinkedTate.QMEndRank :=
  qmEndRank_of hM1 hT27 (qmSplitCaseRank hM1)

end LTGoodRed.QM

end

end LTSplitSec

#print axioms LTGoodRed.QM.eq_zero_of_mul_self_eq_zero
#print axioms LTGoodRed.QM.eight_le_finrank
#print axioms LTGoodRed.QM.qmSplitCaseRank
#print axioms LTGoodRed.QM.qmEndRank_of_leaves
