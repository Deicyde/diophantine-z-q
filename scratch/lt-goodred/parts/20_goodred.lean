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

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Glue: good reduction away from `3` makes inertia trivial on torsion points of the base
change** (linked-tate; the point-level transport half of G3, given the leaf R7a). Same hypotheses
as `GoodRedG3Bridge`. Conclusion: for `p ∉ {3}`, `p ≠ ℓ`, and an element `σ'` of `G_{L'}` whose
image `resQ σ'` lies in the inertia group of a place `v` of `ℚ̄` above `p`, `σ'` fixes every
`ℓⁿ`-torsion point of `A_{L,L'}(\bar{L'})`. Route (STANDARD): `v ∩ K` is a DVR of `K` with `3` a
unit; NOS (a) ⇒ (b) over `K` (PkgI2's `InertiaTrivialOn` on `A(K̄)[ℓⁿ]` at a valuation ring of
`K̄` over `v ∩ K`); transport along `\bar{L'} ≅ K̄` over `K` (`resQ`'s embedding `ℚ̄ → \bar{L'}`) and
`A_{L,L'}(\bar{L'}) = A(\bar{L'})` (unram-tate's `bcPt`). GLUE (definitions only; no new
literature). -/
def GoodRedTorsion : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov], IsUnit (3 : Ov) →
      PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      ∀ p : ℕ, p.Prime → p ∉ ({3} : Finset ℕ) → p ≠ ℓ →
        ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        ∀ σ' : Field.absoluteGaloisGroup L',
          (∃ σ ∈ v.inertiaSubgroup ℚ,
            ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = G0Galois.resQ L' σ') →
          ∀ (n : ℕ) (x : (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).Pt
              (AlgebraicClosure L')),
            x ^ (ℓ ^ n) = 1 →
            (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct σ' x = x

end HSyn.LinkedTate

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
