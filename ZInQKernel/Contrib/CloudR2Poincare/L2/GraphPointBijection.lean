import ZInQKernel.Contrib.CloudR2Poincare.L2.QuotientPointClasses

/-!
# B2 and the ONE square input give actual graph field-point bijectivity

The quotient bundle is genuine data from L1's descent. Its compatibility with
q and the actual kernelPair give uniqueness. B2 gives existence on the ACTUAL
base-changed B; no graph-morphism or dual-universality input is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- Existence of a graph point above each actual Ω-point of J, from exactly
B2 and the shared native square, with the actual descended quotient bundle. -/
theorem exists_quotientGraph_fieldPoint_of_B2
    (hB2 : L3.PicZeroPointSurjectivity.{0}) (hSquare : NativeTheoremOfTheSquare.{0})
    {k Ω : Type} [Field k] [CharZero k] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (M : B.X.left.Modules) [M.IsInvertible] (hM : VeryAmple B.X.hom M)
    (q : PkgI3.AbVar.Hom B Q) (P : (pullback B.X.hom Q.X.hom).Pic)
    (hP : L1.IsNormalizedFamily B Q.X P)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X (Scheme.Pic.mk M) (𝟙 B.X))
    (x : L1.fieldTest k Ω ⟶ J.X) :
    ∃ a : L1.fieldTest k Ω ⟶ quotientGraph J B Q i L P,
      a ≫ (quotientGraphι J B Q i L P ≫ fst J.X Q.X) = x := by
  let T := L1.fieldTest k Ω
  let C : CommGrp (Over (Spec (.of k))) := CommGrp.mk B.X
  let BO : PkgI3.AbVar Ω :=
    { X := (L1.extendedGroup C).X
      proper := by change IsProper (pullback.snd B.X.hom T.hom); infer_instance
      smooth := by change Smooth (pullback.snd B.X.hom T.hom); infer_instance
      geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom T.hom); infer_instance }
  let MO : BO.X.left.Modules := (Scheme.Modules.pullback (pullback.fst B.X.hom T.hom)).obj M
  let N : BO.X.left.Pic := Scheme.Pic.map (L1.picardFamilyMap i.hom T)
    (L1.normalizedPolarizationFamily J.X L x)
  letI : Subsingleton T.left.Pic := inferInstanceAs (Subsingleton (Spec (.of Ω)).Pic)
  have hMO : VeryAmple BO.X.hom MO := hM.baseChange (IsPullback.of_hasPullback _ _)
  have hN : L3.TranslationInvariant BO N := by
    intro b
    let bT := L1.originalFieldPoint C b
    have h := hSquare k J B i L T x bT
    rw [← L1.normalizedPolarizationFamily_eq_of_subsingletonPic J.X L x] at h
    change Scheme.Pic.map (L1.translate (L1.extendedGroup C).X b).left N = N
    rw [L1.field_translation_left C b]
    exact h
  obtain ⟨NR, hNR, hrep⟩ := Scheme.Pic.exists_mk_eq N
  letI : NR.IsInvertible := hNR
  obtain ⟨b, hb⟩ := hB2 Ω BO MO NR hMO (by simpa only [hrep] using hN)
  rw [hrep] at hb
  let bT := L1.originalFieldPoint C b
  have hfamily : L1.normalizedPolarizationFamily B.X (Scheme.Pic.mk M) bT = N := by
    rw [L1.normalizedPolarizationFamily_eq_of_subsingletonPic,
      L1.polarizationFamily_eq_translate_parameter]
    rw [L1.parameterLineClass, Scheme.Pic.map_mk, ← L1.field_translation_left C b]
    exact hb.symm
  let z : T ⟶ Q.X := bT ≫ q.hom
  have hclass : N = Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom z) P := by
    rw [quotientBundle_parameter_class B Q (Scheme.Pic.mk M) q P hp bT, hfamily]
  obtain ⟨a, ha⟩ := (quotientGraph_fieldPoint_factor_iff J B Q i L P hP x z).mpr hclass
  refine ⟨a, ?_⟩
  rw [← Category.assoc, ha, lift_fst]

/-- Actual graph field points are unique above a given J field point, from
the actual quotient kernelPair and stabilizer scheme, not a representability Fact. -/
theorem quotientGraph_fieldPoint_projection_injective
    {k Ω : Type} [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (M : B.X.left.Pic) (H : L1.FiniteStabilizerScheme B M)
    (q : PkgI3.AbVar.Hom B Q) [IsFinite q.hom.left] [Surjective q.hom.left]
    (hk : IsPullback ((fst H.K B.X ≫ H.j) * snd H.K B.X) (snd H.K B.X) q.hom q.hom)
    (P : (pullback B.X.hom Q.X.hom).Pic) (hP : L1.IsNormalizedFamily B Q.X P)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X M (𝟙 B.X)) :
    Function.Injective (fun a : L1.fieldTest k Ω ⟶ quotientGraph J B Q i L P =>
      a ≫ (quotientGraphι J B Q i L P ≫ fst J.X Q.X)) := by
  intro a b h
  let ja := a ≫ quotientGraphι J B Q i L P
  let jb := b ≫ quotientGraphι J B Q i L P
  have ha : ja = lift (ja ≫ fst J.X Q.X) (ja ≫ snd J.X Q.X) := by ext <;> simp
  have hb : jb = lift (jb ≫ fst J.X Q.X) (jb ≫ snd J.X Q.X) := by ext <;> simp
  have hca := (quotientGraph_fieldPoint_factor_iff J B Q i L P hP
    (ja ≫ fst J.X Q.X) (ja ≫ snd J.X Q.X)).mp ⟨a, ha⟩
  have hcb := (quotientGraph_fieldPoint_factor_iff J B Q i L P hP
    (jb ≫ fst J.X Q.X) (jb ≫ snd J.X Q.X)).mp ⟨b, hb⟩
  have hj : ja ≫ fst J.X Q.X = jb ≫ fst J.X Q.X := h
  rw [hj] at hca
  have hz : ja ≫ snd J.X Q.X = jb ≫ snd J.X Q.X :=
    quotientBundle_fieldPoint_injective B Q M H q hk P hp (hca.symm.trans hcb)
  have hab : ja = jb := by
    rw [ha, hb, hj, hz]
  apply Over.OverMorphism.ext
  apply (cancel_mono (quotientGraphι J B Q i L P).left).mp
  simpa only [ja, jb, Over.comp_left] using congrArg Over.Hom.left hab

/-- B2 + square + the literal quotient bundle/kernelPair imply bijectivity of
the ORIGINAL graph projection on every algebraically closed field extension. -/
theorem quotientGraph_fieldPoint_projection_bijective
    (hB2 : L3.PicZeroPointSurjectivity.{0}) (hSquare : NativeTheoremOfTheSquare.{0})
    {k Ω : Type} [Field k] [CharZero k] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω]
    (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (M : B.X.left.Modules) [M.IsInvertible] (hM : VeryAmple B.X.hom M)
    (H : L1.FiniteStabilizerScheme B (Scheme.Pic.mk M))
    (q : PkgI3.AbVar.Hom B Q) [IsFinite q.hom.left] [Surjective q.hom.left]
    (hk : IsPullback ((fst H.K B.X ≫ H.j) * snd H.K B.X) (snd H.K B.X) q.hom q.hom)
    (P : (pullback B.X.hom Q.X.hom).Pic) (hP : L1.IsNormalizedFamily B Q.X P)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X (Scheme.Pic.mk M) (𝟙 B.X)) :
    Function.Bijective (fun a : L1.fieldTest k Ω ⟶ quotientGraph J B Q i L P =>
      a ≫ (quotientGraphι J B Q i L P ≫ fst J.X Q.X)) :=
  ⟨quotientGraph_fieldPoint_projection_injective J B Q i L (Scheme.Pic.mk M) H q hk P hP hp,
    exists_quotientGraph_fieldPoint_of_B2 hB2 hSquare J B Q i L M hM q P hP hp⟩

end ZInQ.Contrib.CloudR2Poincare.L2
