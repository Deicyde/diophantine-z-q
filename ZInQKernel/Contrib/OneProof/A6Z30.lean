import ZInQKernel.Contrib.OneProof.A6IntModel
import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30

/-!
# d2a6b (`Contrib/OneProof/A6Z30.lean`): A6 on the manuscript's `Y₃` leaf over `ℤ[1/30]` (diophantine_zq.tex L529-530)

d2a6-reroute proved A6 ("The proper model and its universal abelian scheme give good reduction outside the places
over `S`", L529-530) from sgr-split's `SGRSplit.ShimuraIntegralModelRep` (a proper smooth `ℤ_(p)`-model for each
`p > 324`). The proper model of L529-530 is the manuscript's own model of L443-477, over `ℤ[1/30]`, which y3-route-a
states as `Y3RouteA.Y3FullThreeRepZ30` (objects `QMAbSchemeP`: the printed, Mumford-form level structure). This file
proves A6 from that leaf, so that `ShimuraIntegralModelRep` is not needed:

* `spec_to_Z30_ext` (proved): morphisms `Spec R → Spec ℤ[1/30]` are unique;
* `z30ToLocal` (proved): the ring map `ℤ[1/30] → O` for a local ring `O` in which a prime `p ∤ 30` is not a unit;
* `hasGoodReduction_of_z30` (proved): for `PK : QML3 K` (`K ⊇ ℚ`) and a valuation subring `O ⊆ K` in which a prime
  `p ∤ 30` is not a unit, `PK.A` has good reduction at `O`. The proof is d2a6-reroute's
  `hasGoodReduction_of_intModel`, with one bridge: the object over `Spec K` is turned into a `QMAbSchemeP` by
  `Y3Fix.ofKer` (proved; the printed level structure from the kernel's over `ℚ`-schemes, through the proved
  `mumfordTorsionAlgClosed`), and the universal family is read in the kernel form by `Y3Fix.toKer` (proved; the
  same `QMFamily`);
* `qmModelG3U_of_z30`, `modelG3G6_of_leavesU_z30` (proved): the A6 readers, with `p > 324 ⇒ p ∤ 30`; the kernel
  field's reader is `good_of_QML3U` in `D2A6Wrap.lean`.

No `sorry`; never imports `ZInQKernel.OneProof.Main`. Report: docs/research/d2a6b.md.
-/

set_option linter.style.longLine false

noncomputable section

namespace D2A6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec.VertWitness HDec.CurveSplitGR SGRSplit
open Y3RouteA Y3Fix
open scoped CategoryTheory.Obj

/-- **Morphisms `Spec R → Spec ℤ[1/30]` are unique** (proved). -/
theorem spec_to_Z30_ext {R : CommRingCat.{0}} (f g : Spec R ⟶ Spec (CommRingCat.of Z30)) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (Submonoid.powers (30 : ℤ)) (RingHom.ext_int _ _)

/-- `ℤ[1/30] → K` for a field of characteristic `0`. -/
def z30To (K : Type) [Field K] [CharZero K] : Z30 →+* K :=
  IsLocalization.Away.lift (30 : ℤ) (g := Int.castRingHom K) (isUnit_iff_ne_zero.2 (by norm_num))

/-- **A prime `p > 324` does not divide `30`** (proved). -/
theorem not_dvd_thirty_of_lt {p : ℕ} (hp : 324 < p) : ¬ (p : ℤ) ∣ 30 := by
  intro h
  have h' : p ∣ 30 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) h'
  omega

/-- **The ring map `ℤ[1/30] → O`** when a prime `p ∤ 30` is not a unit of the local ring `O` (proved: `30` is then
a unit, `isUnit_of_not_dvd`). -/
def z30ToLocal {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] (hpR : ¬ IsUnit (p : R))
    (h30 : ¬ (p : ℤ) ∣ 30) : Z30 →+* R :=
  IsLocalization.Away.lift (30 : ℤ) (g := Int.castRingHom R) (isUnit_of_not_dvd p hpR 30 h30)

open PkgI3 in
/-- **A6 on the manuscript's route over `ℤ[1/30]` (proved)** from the manuscript's model of `Y₃`
(`Y3RouteA.Y3FullThreeRepZ30`, diophantine_zq.tex L443-477): every object `PK : QML3 K` over a field `K ⊇ ℚ` has
good reduction at every valuation subring `O` of `K` in which some prime `p ∤ 30` is not a unit (L529-530).

1. *The classifying point.* `PK` is a `QMAbScheme` over `Spec K` (`qml3AsQMAb_of`), hence a `QMAbSchemeP` over the
   `ℚ`-scheme `Spec K` (`ofKer`, the printed level structure); the universal property of the model on the locally
   noetherian `ℤ[1/30]`-scheme `Spec K` gives `g : Spec K → 𝒴` with `PK = g^*𝒜`.
2. *The lift to `O`.* `ℤ[1/30] → O` (`z30ToLocal`) and the valuative criterion for the proper `𝒴 → Spec ℤ[1/30]`
   give `ℓ : Spec O → 𝒴` extending `g` (maps to `Spec ℤ[1/30]` are unique).
3. *The abelian scheme* `ℓ^*𝒜` over `O` (base change preserves proper, smooth, geometrically connected).
4. *Its generic fibre* is `g^*𝒜 ≅ PK.A` (pasting of pullbacks), a homomorphism by rigidity
   (`MulRigidity.isMonHom_of_geometricallyIntegral`). -/
theorem hasGoodReduction_of_z30 (hY : Y3FullThreeRepZ30) {K : Type} [Field K] [Algebra ℚ K]
    (PK : QML3 K) (Ov : ValuationSubring K) (p : ℕ) [Fact p.Prime] (h30 : ¬ (p : ℤ) ∣ 30)
    (hpO : ¬ IsUnit (p : Ov)) : PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) Ov := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨𝒴, 𝒜₀, hpr, hsm, hU⟩ := hY
  let 𝒜 : QMAbScheme 𝒴.left := toKer 𝒜₀
  obtain ⟨𝒜P, h𝒜P⟩ := qml3AsQMAb_of abVarSurfaceRelDim K PK
  -- the object over the `ℚ`-scheme `Spec K`, with the printed level structure
  have hT : ObjBridge.TorsionStructure :=
    AvSplit.torsionStructure_of_mumford ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  let SQ : Over (Spec (CommRingCat.of ℚ)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
  let 𝒜PP : QMAbSchemeP SQ.left := ofKer hT (S := SQ) 𝒜P
  -- the point of `𝒴` classifying `PK`
  obtain ⟨g, hg, -⟩ := hU (Over.mk (Spec.map (CommRingCat.ofHom (z30To K))))
    (by dsimp; infer_instance) 𝒜PP
  have hg' : QMFamFibre 𝒜.toQMFamily g.left 𝒜P.toQMFamily := hg
  obtain ⟨k, hpb, -, he⟩ : IsFibreOf 𝒜.toQMFamily g.left PK := (h𝒜P _ _ g.left).mpr hg'
  -- the valuative lift `ℓ : Spec O → 𝒴`
  let j : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of Ov) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ov K))
  let i₂ : Spec (CommRingCat.of Ov) ⟶ Spec (CommRingCat.of Z30) :=
    Spec.map (CommRingCat.ofHom (z30ToLocal p hpO h30))
  have hsq : CommSq g.left j 𝒴.hom i₂ := ⟨spec_to_Z30_ext _ _⟩
  have hvc : ValuativeCriterion 𝒴.hom := by
    have h := hpr
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let SQv : ValuativeCommSq 𝒴.hom := ⟨Ov, K, g.left, i₂, hsq⟩
  obtain ⟨hL⟩ := hvc SQv
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

/-! ## The readers on `Y3FullThreeRepZ30` -/

namespace HDec

namespace D2A6

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **`QMModelG3U`, proved** from the manuscript's model of `Y₃` over `ℤ[1/30]` (`Y3RouteA.Y3FullThreeRepZ30`,
L443-477) and Néron–Ogg–Shafarevich (R7a): `D2A6.hasGoodReduction_of_z30` at every DVR over a prime `p > 324`
(so `p ∤ 30`), then `goodRedTorsionT` and `tate_eq_one_of_torsion` (d2a6-reroute's `qmModelG3U_of`, verbatim
otherwise). -/
theorem qmModelG3U_of_z30 (hNOS : PkgI2.NeronOggShafarevich.{0}) (hY : _root_.Y3RouteA.Y3FullThreeRepZ30) :
    QMModelG3U := by
  intro K L L' _ hKL hLL' PK ℓ _
  letI : NumberField L' := numberField_of_fd L'
  intro p hp hpT hpl v hv σ' hσ
  exact HSyn.LinkedTate.tate_eq_one_of_torsion _ ℓ σ'
    (LTGoodRed.goodRedTorsionT T324 hNOS K L L' hKL hLL' PK.A
      (fun Ov _ q hq hqT hqO =>
        haveI : Fact q.Prime := ⟨hq⟩
        _root_.D2A6.hasGoodReduction_of_z30 hY PK Ov q
          (_root_.D2A6.not_dvd_thirty_of_lt (lt_of_notMem_T324 hq hqT)) hqO)
      ℓ p hp hpT hpl v hv σ' hσ)

/-- **G3 and G5-G6 on G7's model from the manuscript's `Y₃` model** (proved). -/
theorem modelG3G6_of_leavesU_z30 (hFS : HSyn.G0Split.FibreSimple) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hY : _root_.Y3RouteA.Y3FullThreeRepZ30) : HSyn.G0AssembleMod.ModelG3G6 :=
  modelG3G6_of_U hFS (qmModelG3U_of_z30 hNOS hY)

end D2A6

end HDec

#print axioms D2A6.spec_to_Z30_ext
#print axioms D2A6.z30ToLocal
#print axioms D2A6.hasGoodReduction_of_z30
#print axioms HDec.D2A6.qmModelG3U_of_z30
#print axioms HDec.D2A6.modelG3G6_of_leavesU_z30
