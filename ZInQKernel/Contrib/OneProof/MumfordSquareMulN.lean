import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyWeil

/-!
# Two of Mumford's displays over `k = k̄` from the Picard scheme (phisurj by-products)

pic-dict reduced `weilPairingMumford` to seven of Mumford's displays (`PicDict.*AC`); weil-proof proved two
(§20, §23). Here two more are theorems from L1 (`PicRepresentableAbVar`) and L2 (`PicZeroAbVar`), with no
cohomology and no seesaw:

* `PhiSurj.mumfordSquareAC_of_open : PicRepresentableAbVar → PicZeroAbVar → PicDict.MumfordSquareAC`
  (theorem of the square, Mumford §6 Cor. 4): `φ_c = λ_c ≫ j` with `λ_c` a homomorphism
  (`T09Pic.exists_hom_comp_eq_phiL`), `j` a homomorphism, and `kClass` an injective homomorphism (Kleiman 9.2.5 at
  `Spec k̄`);
* `PhiSurj.mumfordMulNPicZeroAC_of_open : PicRepresentableAbVar → PicZeroAbVar → PicDict.MumfordMulNPicZeroAC`
  (`n^*c = cⁿ` for translation-invariant `c`, Mumford §8 (iv)): `λ_c` vanishes on `k`-points, hence is zero; so
  `Λ(c)` is classified by the constant map and normalized along `0`, hence trivial (the vendored normalized Picard
  functor, as in phi-ample); induct on `n`.

Not used by the fold of `mumfordPhiSurjectiveAC` (docs/research/phisurj.md).
-/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj

open T09Pic PkgI3 PkgI3.AbVar PicDict

theorem kClass_mul {k : Type} [Field k] {X : AbVar k} {P : Over (Spec (CommRingCat.of k))}
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) (c c' : X.X.left.Pic) :
    let _ := picardFunctorCommGrpObj X.X.hom rep
    kClass rep (c * c') = kClass rep c * kClass rep c' := by
  let _ := picardFunctorCommGrpObj X.X.hom rep
  unfold kClass
  rw [Scheme.Pic.map_mul]
  exact homEquiv_symm_toPicardFunctor_mul X.X.hom rep _ _

/-- **`φ_c` is a homomorphism on `k`-points** (from L1, L2). -/
theorem phi_mul (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) {k : Type} [Field k] [IsAlgClosed k]
    (X : AbVar k) (c : X.X.left.Pic) (x y : AC.Kpt X) :
    AC.phi c (x * y) = AC.phi c x * AC.phi c y := by
  obtain ⟨P, ⟨rep⟩⟩ := h1 k X
  obtain ⟨B, j, hj⟩ := h2 k X P rep
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj c
  let _ := picardFunctorCommGrpObj X.X.hom rep
  have hmon : IsMonHom j := hj.2.2
  apply kClass_injective rep
  rw [kClass_mul, ← kpt_comp_phiL, ← kpt_comp_phiL, ← kpt_comp_phiL, ← hlam,
    ← Category.assoc, ← Category.assoc, ← Category.assoc, MonObj.mul_comp, MonObj.mul_comp]

/-- **pic-dict's `MumfordSquareAC` is a theorem** given L1 and L2. -/
theorem mumfordSquareAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) : MumfordSquareAC := by
  intro k _ _ X c x y
  have h := phi_mul h1 h2 X c x y
  simp only [AC.phi] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h]
  simp only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel_left]

end PhiSurj


open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj

open T09Pic PkgI3 PkgI3.AbVar PicDict

variable {k : Type} [Field k]

/-- Over `k = k̄`, morphisms of abelian varieties agreeing on `k`-points are equal. -/
theorem hom_ext_kpt [IsAlgClosed k] {A B : AbVar k} (u v : A.X ⟶ B.X)
    (H : ∀ x : AC.Kpt A, x ≫ u = x ≫ v) : u = v := by
  apply AVGlue.hom_ext_of_points
  intro z
  let φ := CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have : IsIso φ := (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  let zl : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ A.X.left := z.left
  have hz : zl ≫ A.X.hom = Spec.map φ := Over.w z
  let xl : Spec (CommRingCat.of k) ⟶ A.X.left := inv (Spec.map φ) ≫ zl
  have hxl : xl ≫ A.X.hom = 𝟙 _ := by
    simp only [xl, Category.assoc, hz, IsIso.inv_hom_id]
  let x : AC.Kpt A := Over.homMk xl hxl
  have hzx : zl = Spec.map φ ≫ xl := by
    simp only [xl, IsIso.hom_inv_id_assoc]
  have hu := congrArg CommaMorphism.left (H x)
  simp only [Over.comp_left] at hu
  apply Over.OverMorphism.ext
  change zl ≫ u.left = zl ≫ v.left
  rw [hzx, Category.assoc, Category.assoc]
  exact congrArg (Spec.map φ ≫ ·) hu

/-- For translation-invariant `c`, `λ_c` is zero. -/
theorem lam_eq_zero_of_isTI [IsAlgClosed k] {X : AbVar k} {P : Over (Spec (CommRingCat.of k))}
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) {B : AbVar k} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) {c : X.X.left.Pic} (hc : AC.IsTI c) {lam : X.X ⟶ B.X}
    (hlam : lam ≫ j = phiL rep c) :
    lam = CartesianMonoidalCategory.toUnit X.X ≫ η[B.X] := by
  let _ := picardFunctorCommGrpObj X.X.hom rep
  have hmon : IsMonHom j := hj.2.2
  have hjm : Mono j := by
    have : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  apply hom_ext_kpt
  intro x
  have h1 : AC.phi c x = 1 := by
    simp only [AC.phi, hc x, mul_inv_cancel]
  have h2 : kClass rep (1 : X.X.left.Pic) = CartesianMonoidalCategory.toUnit _ ≫ η[P] := by
    unfold kClass
    rw [Scheme.Pic.map_one]
    exact homEquiv_symm_one rep
  rw [← cancel_mono j, Category.assoc, hlam, kpt_comp_phiL, h1, h2, Category.assoc, Category.assoc,
    IsMonHom.one_hom j, ← Category.assoc x,
    CartesianMonoidalCategory.toUnit_unique (x ≫ _) (CartesianMonoidalCategory.toUnit _)]

/-- **`Λ(c) = 1` for translation-invariant `c`** (Mumford §8 (iv), first form). -/
theorem mumfordBundle_eq_one_of_isTI (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) [IsAlgClosed k]
    (X : AbVar k) (c : X.X.left.Pic) (hc : AC.IsTI c) : mumfordBundle X c = 1 := by
  obtain ⟨P, ⟨rep⟩⟩ := h1 k X
  obtain ⟨B, j, hj⟩ := h2 k X P rep
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj c
  let _ := picardFunctorCommGrpObj X.X.hom rep
  have hmon : IsMonHom j := hj.2.2
  have h0 := lam_eq_zero_of_isTI rep hj hc hlam
  have hphi : phiL rep c = CartesianMonoidalCategory.toUnit X.X ≫ η[P] := by
    rw [← hlam, h0, Category.assoc, IsMonHom.one_hom j]
  rw [phiL, ← homEquiv_symm_one rep] at hphi
  have e0 : zT X X.X = (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit X.X ≫ η[X.X])
      (𝟙 X.X)).left := by
    apply pullback.hom_ext <;> simp
  have hμ0 : zT X X.X ≫ (μ[X.X]).left = 𝟙 _ := by
    rw [e0, ← Over.comp_left, MonObj.lift_comp_one_left]; rfl
  have hS0 : Scheme.Pic.map (X.X.hom ≫ η[X.X].left) c = 1 := by
    rw [Scheme.Pic.map_comp, Subsingleton.elim (α := (Spec (CommRingCat.of k)).Pic)
      (Scheme.Pic.map η[X.X].left c) 1, Scheme.Pic.map_one]
  have hz0 : Scheme.Pic.map (zT X X.X) (mumfordBundle X c) = 1 := by
    rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
    simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ0,
      sectionBaseChange_fst, sectionBaseChange_snd, Scheme.Pic.map_id]
    rw [hS0]
    group
  have h3 : (1 : (pullback X.X.hom X.X.hom).Pic) ∈ (Nrm X).obj (op X.X) := by
    change Scheme.Pic.map _ 1 = 1; exact Scheme.Pic.map_one _
  have h5 := Θ_inj (A := X) pushforwardUnitUniversal (T := X.X)
    (x := ⟨mumfordBundle X c, hz0⟩) (y := ⟨(1 : (pullback X.X.hom X.X.hom).Pic), h3⟩) (by
      rw [Θ_hom_app, Θ_hom_app]
      exact rep.homEquiv.symm.injective hphi)
  exact congrArg Subtype.val h5

/-- `m^*c = p₁^*c ⊗ p₂^*c` for translation-invariant `c`. -/
theorem mu_pic_of_isTI (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) [IsAlgClosed k]
    (X : AbVar k) (c : X.X.left.Pic) (hc : AC.IsTI c) :
    Scheme.Pic.map (μ[X.X]).left c =
      Scheme.Pic.map (pullback.fst X.X.hom X.X.hom) c * Scheme.Pic.map (pullback.snd X.X.hom X.X.hom) c := by
  have h := mumfordBundle_eq_one_of_isTI h1 h2 X c hc
  unfold mumfordBundle at h
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h.trans (mul_comm _ _)

/-- **pic-dict's `MumfordMulNPicZeroAC` is a theorem** given L1 and L2. -/
theorem mumfordMulNPicZeroAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) :
    MumfordMulNPicZeroAC := by
  intro k _ _ X c hc n
  induction n with
  | zero =>
    have e : (AC.mul X 0).left = X.X.hom ≫ η[X.X].left := by
      simp only [AC.mul, pow_zero]
      rfl
    rw [e, Scheme.Pic.map_comp, Subsingleton.elim (α := (Spec (CommRingCat.of k)).Pic)
      (Scheme.Pic.map η[X.X].left c) 1, Scheme.Pic.map_one, pow_zero]
  | succ n ih =>
    have e : (AC.mul X (n + 1)).left =
        (CartesianMonoidalCategory.lift (AC.mul X n) (𝟙 X.X)).left ≫ (μ[X.X]).left := by
      simp only [AC.mul, pow_succ, CategoryTheory.Hom.mul_def, Over.comp_left]
    have hf : (CartesianMonoidalCategory.lift (AC.mul X n) (𝟙 X.X)).left ≫ pullback.fst X.X.hom X.X.hom =
        (AC.mul X n).left := by simp
    have hs : (CartesianMonoidalCategory.lift (AC.mul X n) (𝟙 X.X)).left ≫ pullback.snd X.X.hom X.X.hom =
        𝟙 _ := by simp
    rw [e, Scheme.Pic.map_comp, mu_pic_of_isTI h1 h2 X c hc, Scheme.Pic.map_mul, ← Scheme.Pic.map_comp,
      ← Scheme.Pic.map_comp, hf, hs, Scheme.Pic.map_id, ih, pow_succ]

end PhiSurj

