import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard

/-!
# d2a6-reroute (`Contrib/OneProof/A6IntModel.lean`): A6 on the manuscript's route (diophantine_zq.tex L529-530)

"The proper model and its universal abelian scheme give good reduction outside the places over `S`."
The proper model is the integral model of `Y₃` (L443-477), stated in the kernel as sgr-split's
`SGRSplit.ShimuraIntegralModelRep` (for every prime `p > 324`, a proper smooth curve `𝒴/ℤ_(p)` with a
`QMAbScheme` representing the full-three moduli problem on locally noetherian `ℤ_(p)`-schemes).

* `eta_pullback_fst` (proved): the identity of `f^*X` lies over the identity of `X`.
* `hasGoodReduction_of_intModel` (proved): for an object `PK : QML3 K` (`K ⊇ ℚ`) and a valuation subring `O` of
  `K` in which a prime `p > 324` is not a unit, `PK.A` has good reduction at `O` (PkgI2's `HasGoodReduction`: an
  abelian scheme over `O` with generic fibre isomorphic to `PK.A` as a group object). The proof is L529-530: the
  `K`-point `g` of `𝒴` classifying `PK` extends to `Spec O → 𝒴` (valuative criterion, `𝒴` proper over `ℤ_(p)`,
  `ℤ_(p) → O`), the pullback of the universal abelian scheme is the abelian scheme over `O`, and its generic fibre
  is the fibre at `g`, i.e. `PK.A` (pasting of pullbacks; a homomorphism by rigidity).
-/

set_option linter.style.longLine false

noncomputable section

namespace D2A6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec.VertWitness HDec.CurveSplitGR SGRSplit
open scoped CategoryTheory.Obj

/-- `f^*u` over the first projection (any base change `f`; sgr-split's `map_left_fst` is for field points). -/
theorem map_left_fst' {S S' : Scheme.{0}} (f : S' ⟶ S) {X Z : Over S} (u : X ⟶ Z) :
    ((Over.pullback f).map u).left ≫ pullback.fst Z.hom f = pullback.fst X.hom f ≫ u.left := by
  simp [Over.pullback_map_left]

/-- **The identity of a base change lies over the identity** (proved): for a group object `X` over `S` and
`f : S' → S`, `η[f^*X] ≫ pr₁ = f ≫ η[X]`. -/
theorem eta_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Over S) [GrpObj X] :
    (η[(Over.pullback f).obj X] : 𝟙_ _ ⟶ _).left ≫ pullback.fst X.hom f = f ≫ (η[X] : 𝟙_ _ ⟶ X).left := by
  rw [Functor.obj.η_def, Over.comp_left, Category.assoc, map_left_fst', ← Category.assoc]
  congr 1
  have h2 := Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have key : (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙_ (Over S)).hom f ≫
      (𝟙_ (Over S)).hom = f := by
    rw [pullback.condition, ← Category.assoc]
    change ((Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ ((Over.pullback f).obj (𝟙_ (Over S))).hom) ≫ f = f
    rw [h2]
    simp
  simpa using key

/-- **Integers prime to `p` are units of a local ring in which `p` is not a unit** (proved). -/
theorem isUnit_of_not_dvd {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [hp : Fact p.Prime]
    (hpR : ¬ IsUnit (p : R)) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) : IsUnit (m : R) := by
  have hcop : IsCoprime (m : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right m (p : ℤ)
    have hg : Int.gcd m p ∣ p := by exact_mod_cast this
    rcases (Nat.dvd_prime hp.out).mp hg with h | h
    · exact h
    · exfalso; apply hm
      have := Int.gcd_dvd_left m (p : ℤ)
      rw [h] at this; exact_mod_cast this
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : R) * m = 1 - b * p := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    linear_combination this
  have hu : IsUnit ((1 : R) - b * p) := by
    have hn : (b : R) * p ∈ IsLocalRing.maximalIdeal R :=
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hpR)
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
    exact this
  rw [← h1] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- The ring map `ℤ_(p) → O` when `p` is not a unit of the local ring `O`. -/
def zlocToLocal {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] (hpR : ¬ IsUnit (p : R)) :
    Zloc p →+* R :=
  IsLocalization.lift (M := (pIdeal p).primeCompl) (g := Int.castRingHom R) (fun x => by
    refine isUnit_of_not_dvd p hpR x ?_
    intro h
    exact x.2 (Ideal.mem_span_singleton.mpr h))

open PkgI3 in
/-- **A6 on the manuscript's route (proved)** from the integral model of `Y₃` (`ShimuraIntegralModelRep`,
diophantine_zq.tex L443-477): every object `PK : QML3 K` over a field `K ⊇ ℚ` has good reduction at every
valuation subring `O` of `K` in which some prime `p > 324` is not a unit (L529-530). -/
theorem hasGoodReduction_of_intModel (hRep : ShimuraIntegralModelRep) {K : Type} [Field K] [Algebra ℚ K]
    (PK : QML3 K) (Ov : ValuationSubring K) (p : ℕ) [Fact p.Prime] (hp : 324 < p)
    (hpO : ¬ IsUnit (p : Ov)) : PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) Ov := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨𝒴, 𝒜, hpr, hsm, hU⟩ := hRep p hp
  obtain ⟨𝒜P, h𝒜P⟩ := qml3AsQMAb_of abVarSurfaceRelDim K PK
  -- the point of `𝒴` classifying `PK`
  obtain ⟨g, hg, -⟩ := hU (Over.mk (Spec.map (CommRingCat.ofHom (zlocTo p K))))
    (by dsimp; infer_instance) 𝒜P
  obtain ⟨k, hpb, -, he⟩ : IsFibreOf 𝒜.toQMFamily g.left PK := (h𝒜P _ _ g.left).mpr hg
  -- the valuative lift `ℓ : Spec O → 𝒴`
  let j : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of Ov) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ov K))
  let i₂ : Spec (CommRingCat.of Ov) ⟶ Spec (CommRingCat.of (Zloc p)) :=
    Spec.map (CommRingCat.ofHom (zlocToLocal p hpO))
  have hsq : CommSq g.left j 𝒴.hom i₂ := ⟨spec_to_Zloc_ext p _ _⟩
  have hvc : ValuativeCriterion 𝒴.hom := by
    have h := hpr
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let SQ : ValuativeCommSq 𝒴.hom := ⟨Ov, K, g.left, i₂, hsq⟩
  obtain ⟨hL⟩ := hvc SQ
  let L := hL.default
  let ℓ : Spec (CommRingCat.of Ov) ⟶ 𝒴.left := L.l
  have hℓ : j ≫ ℓ = g.left := L.fac_left
  -- the abelian scheme over `O`
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  let FO : Over (Spec (CommRingCat.of Ov)) := (Over.pullback ℓ).obj 𝒜.F
  have hFOsm : SmoothOfRelativeDimension 2 FO.hom := by dsimp [FO]; infer_instance
  have : Smooth FO.hom := SmoothOfRelativeDimension.smooth 2 _
  have : IsProper FO.hom := by dsimp [FO]; infer_instance
  have : GeometricallyConnected FO.hom := by dsimp [FO]; infer_instance
  let GO : Grp (Over (Spec (CommRingCat.of Ov))) := Grp.mk FO
  refine ⟨GO, ⟨by dsimp [GO]; infer_instance, by dsimp [GO]; infer_instance,
    by dsimp [GO]; infer_instance⟩, ⟨?_⟩⟩
  -- its generic fibre is the fibre at `g`
  let Fj : Over (Spec (CommRingCat.of K)) := (Over.pullback j).obj FO
  have hpbj : IsPullback (pullback.fst FO.hom j ≫ pullback.fst 𝒜.F.hom ℓ) Fj.hom 𝒜.F.hom g.left := by
    rw [← hℓ]
    exact (IsPullback.of_hasPullback FO.hom j).paste_horiz (IsPullback.of_hasPullback 𝒜.F.hom ℓ)
  let e : PK.A.X.left ≅ Fj.left := hpb.isoIsPullback _ _ hpbj
  have ek : e.hom ≫ pullback.fst FO.hom j ≫ pullback.fst 𝒜.F.hom ℓ = k := hpb.isoIsPullback_hom_fst _ _ hpbj
  have eh : e.hom ≫ Fj.hom = PK.A.X.hom := hpb.isoIsPullback_hom_snd _ _ hpbj
  let eO : PK.A.X ≅ Fj := Over.isoMk e eh
  have : IsSeparated Fj.hom := by dsimp [Fj]; infer_instance
  have : LocallyOfFiniteType Fj.hom := by dsimp [Fj]; infer_instance
  have h0 : η[PK.A.X] ≫ eO.hom = η[Fj] := by
    apply Over.OverMorphism.ext
    apply hpbj.hom_ext
    · rw [Over.comp_left, Category.assoc]
      change η[PK.A.X].left ≫ e.hom ≫ _ = _
      rw [ek, eta_left_comp he]
      change _ = η[(Over.pullback j).obj FO].left ≫ _
      rw [← Category.assoc, eta_pullback_fst, Category.assoc, eta_pullback_fst, ← Category.assoc, hℓ,
        ← 𝒜.one_eq]
    · exact (Over.w (η[PK.A.X] ≫ eO.hom)).trans (Over.w η[Fj]).symm
  haveI : IsMonHom eO.hom := _root_.MulRigidity.isMonHom_of_geometricallyIntegral PK.A.X Fj eO.hom h0
  exact (Grp.mkIso' eO).symm

end D2A6

end

/-! ## `G3Out` outside the primes `≤ 324` on G7's model (the manuscript's A6, L529-530) -/

namespace HDec

namespace D2A6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- `GoodRedTorsion` (lt-goodred, TailF) for good reduction outside a finite set `T` of primes: if `A/K`
(`K ⊆ ℚ̄`) has good reduction at every DVR of `K` in which a prime `p ∉ T` is not a unit, then inertia of
`G_{L'}` at places above `p ∉ T`, `p ≠ ℓ`, fixes `A(\bar{L'})[ℓⁿ]` (the original is the case "`3` a unit", `T = {3}`). -/
def GoodRedTorsionT (T : Finset ℕ) : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov] (p : ℕ), p.Prime → p ∉ T →
      ¬ IsUnit (p : Ov) → PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ →
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

end D2A6

end HDec

-- copied from ZInQKernel/OneProof/H/TailF.lean:3649 (goodRedTorsion)
namespace HDec
open _root_.ZInQ (Contrib.AbVarBC.G0FibreSimple.MulIsogeny Contrib.AbVarBC.MulRigidity.CotangentMulN Contrib.AbVarBC.MulRigidity.KerUnitOpen Contrib.AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj Contrib.AbVarBC.MulRigidity.MulEtale Contrib.AbVarBC.MulRigidity.MulUnramified Contrib.AbVarBC.MulRigidity.O0 Contrib.AbVarBC.MulRigidity.QuasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.charZero_residueField Contrib.AbVarBC.MulRigidity.cotangentMap Contrib.AbVarBC.MulRigidity.diagonal_isPullback Contrib.AbVarBC.MulRigidity.diffKer Contrib.AbVarBC.MulRigidity.formallyUnramified_of_kerUnit Contrib.AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section Contrib.AbVarBC.MulRigidity.isProper_left Contrib.AbVarBC.MulRigidity.kerUnit Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_cotangent Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified Contrib.AbVarBC.MulRigidity.map_origin Contrib.AbVarBC.MulRigidity.mulIsogeny_of_cotangent Contrib.AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulEtale Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified' Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulUnramified_of_mulEtale Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf Contrib.AbVarBC.MulRigidity.origin Contrib.AbVarBC.MulRigidity.quasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.stalkEndo Contrib.AbVarBC.MulRigidity.surjective_of_lqf_self) -- op-dedupe
set_option maxHeartbeats 1000000
section G0A2_c75_ltgoodred
section LTGoodRedSec
set_option linter.style.haveILetI false
noncomputable section
open scoped Pointwise
namespace LTGoodRed
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField
set_option maxHeartbeats 1000000 in
/-- **`GoodRedTorsionT T`, proved** (d2a6-reroute: lt-goodred's `goodRedTorsion` copied, with DVRs in which `3` is a unit replaced by DVRs in which a prime `p ∉ T` is not a unit; the original's text otherwise: (Mathlib, the copied `bcPt`/`trPt` and neron-lg's DVR
classification; NOS enters as the hypothesis of the Prop). -/
theorem goodRedTorsionT (T : Finset ℕ) : _root_.HDec.D2A6.GoodRedTorsionT T := by
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
  have hpO : ¬ IsUnit ((p : ℕ) : O) := by
    intro hu
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
    have hc' : (p : K) * (c : K) = 1 := by
      have := congrArg Subtype.val hc
      push_cast at this
      exact this
    have hpi : ((p : K))⁻¹ ∈ O := by
      rw [← eq_inv_of_mul_eq_one_right hc']
      exact c.2
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
  have hℓp : Nat.Coprime (ℓ ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr (Ne.symm hpl))
  -- NOS (a) ⇒ (b) at `(O, w)`
  have htriv := ((hNOS K O w rfl (ObjBridge.toGrp A)).1.mp (hA O p hp hp3 hpO)) (ℓ ^ n)
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
end G0A2_c75_ltgoodred
end HDec



namespace HDec

namespace D2A6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- The primes `≤ 324` (the manuscript's minimal `S`, L383-384). -/
def T324 : Finset ℕ := (Finset.range 325).filter Nat.Prime

theorem lt_of_notMem_T324 {p : ℕ} (hp : p.Prime) (h : p ∉ T324) : 324 < p := by
  by_contra h'
  exact h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

theorem T324_subset_T (u : ℚ) : T324 ⊆ T u := by
  intro q hq
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_union_left _ (ZInQ.Mult.mem_S_mul_of_le hq2 (by
    have := Finset.mem_range.mp hq1; omega))

/-- **Glue G3 on base changes of `QML3` objects, the manuscript's form** (A6, diophantine_zq.tex L529-530: "the
proper model and its universal abelian scheme give good reduction outside the places over `S`"): as
linked-tate's `QMModelG3` (TailF), with `T = {3}` replaced by the primes `≤ 324` (`T324 ⊆ T(u)`, which is all its
reader uses). -/
def QMModelG3U : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K)
    (ℓ : ℕ) [Fact ℓ.Prime],
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ T324

/-- **`QMModelG3U`, proved** from the integral model of `Y₃` (`SGRSplit.ShimuraIntegralModelRep`, L443-477) and
Néron–Ogg–Shafarevich (R7a): `D2A6.hasGoodReduction_of_intModel` at every DVR over a prime `p > 324`, then
`goodRedTorsionT` and `tate_eq_one_of_torsion`. -/
theorem qmModelG3U_of (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRep : _root_.SGRSplit.ShimuraIntegralModelRep) :
    QMModelG3U := by
  intro K L L' _ hKL hLL' PK ℓ _
  letI : NumberField L' := numberField_of_fd L'
  intro p hp hpT hpl v hv σ' hσ
  exact HSyn.LinkedTate.tate_eq_one_of_torsion _ ℓ σ'
    (LTGoodRed.goodRedTorsionT T324 hNOS K L L' hKL hLL' PK.A
      (fun Ov _ q hq hqT hqO =>
        haveI : Fact q.Prime := ⟨hq⟩
        _root_.D2A6.hasGoodReduction_of_intModel hRep PK Ov q (lt_of_notMem_T324 hq hqT) hqO)
      ℓ p hp hpT hpl v hv σ' hσ)

/-- **`ModelG3G6` from `FibreSimple` and `QMModelG3U`** (proved): linked-tate's `modelG3G6_of` (TailF) with
`T324 ⊆ T(u)` in place of `{3} ⊆ T(u)`. -/
theorem modelG3G6_of_U (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3U) :
    HSyn.G0AssembleMod.ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hT := T324_subset_T u
  refine ⟨⟨HSyn.LinkedTate.endDivision_of_fibreSimple hFS hctx L' _ hmod, ?_⟩, ?_, ?_⟩
  · exact @HSyn.LinkedTate.noncomm_baseChange2 K _ PK L _ (incAlg hKL) L' _ (incAlg hLL')
  · exact HSyn.LinkedTate.g3Out_mono hT (hG3 K L L' hKL hLL' PK 5)
  · exact HSyn.LinkedTate.g3Out_mono hT (hG3 K L L' hKL hLL' PK 3)

/-- **G3 and G5-G6 on G7's model on the manuscript's route** (proved): replaces TailI's `modelG3G6_of_leaves3`
(`FibreSimple`, R7a, R6 = `RaynaudCriterionNF`, T5) by `FibreSimple`, R7a and the integral model of `Y₃`. -/
theorem modelG3G6_of_leavesU (hFS : HSyn.G0Split.FibreSimple) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRep : _root_.SGRSplit.ShimuraIntegralModelRep) : HSyn.G0AssembleMod.ModelG3G6 :=
  modelG3G6_of_U hFS (qmModelG3U_of hNOS hRep)

end D2A6

end HDec

#print axioms D2A6.hasGoodReduction_of_intModel
#print axioms HDec.LTGoodRed.goodRedTorsionT
#print axioms HDec.D2A6.qmModelG3U_of
#print axioms HDec.D2A6.modelG3G6_of_leavesU
