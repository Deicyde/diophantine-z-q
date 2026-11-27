import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.TorsionRep
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Frame representability at level three (draft)

From `MilneProp207 3` (multiplication by 3 is finite and etale) and `GeomFree3` (the
3-torsion of every geometric fibre has a generator) we prove `BuzzardFrameRep 3`.

1. `W := A[3]`, the fibre of `ι(3)` over the zero section, with `j : W ⟶ A` and `W ⟶ S`
   finite etale.
2. For `a : O`, `K a ⊆ W` is the locus where `ι(a)` vanishes: the preimage of the diagonal of
   `W ⟶ S` under `(ι(a), 0) : W ⟶ W ×_S W`. It is open (the diagonal of an etale map is an
   open immersion) and closed (the diagonal of a finite map is a closed immersion).
3. `Z := W \ ⋃_{a ∉ 3O} K a`, a finite union indexed by nonzero classes of `O/3O`. Its
   inclusion is an open immersion with closed range, hence a closed immersion.
4. A point factors through `Z` iff it generates the 3-torsion at every geometric point; the
   second clause of `IsGenAt` follows from the first and a generator, since right
   multiplication by an element of the finite ring `O/3O` is injective iff bijective.
5. `Z ⟶ S` is surjective: a generator at a geometric point lands in `Z`.
-/

attribute [local instance] FEC.grp

/-- At every geometric point, the 3-torsion of a false elliptic curve has a generator: it is
a free module of rank one over O/3O.
Source, in two steps: V_3(A) is free of rank one over B ⊗ Q_3 (J. S. Milne, Abelian Varieties,
course notes v2.0 (2008), Prop. 10.23 and its proof, pp. 52 to 53, in the case where B ⊗ Q_3 is
a division algebra; T_3(A) is free of rank 2g over Z_3 by Remark 7.3, p. 34); and every lattice
over the maximal order of the local division algebra B ⊗ Q_3 is principal (J. Voight,
Quaternion Algebras, GTM 288 (2021), Prop. 13.3.4 and 13.3.10). Hence T_3(A) is free of rank
one over O ⊗ Z_3 and A[3](k) = T_3(A)/3T_3(A) is free of rank one over O/3O. -/
def GeomFree3 : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left) (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ S.left), ∃ P : Over.mk s ⟶ A.F, IsGenAt 3 A s P

/-! ## 1. Algebra -/

section Alg

variable {S : Scheme.{0}} (A : FEC S)

theorem one_left_eq {U : Over S} : (1 : U ⟶ A.F).left = U.hom ≫ torsZeroL A :=
  (show (1 : U ⟶ A.F).left = (toUnit U).left ≫ torsZeroL A from rfl).trans
    (congrArg (fun t => t ≫ torsZeroL A) (torsToUnit_left U))

theorem comp_iota_eq_one_iff {U : Over S} (x : U ⟶ A.F) (a : O) :
    x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      x.left ≫ A.iota a = U.hom ≫ torsZeroL A := by
  constructor
  · intro h
    exact (congrArg (fun f : U ⟶ A.F => f.left) h).trans (one_left_eq A)
  · intro h
    exact Over.OverMorphism.ext (h.trans (one_left_eq A).symm)

theorem torsZeroL_iota (a : O) : torsZeroL A ≫ A.iota a = torsZeroL A := by
  have h : (1 : Over.mk (𝟙 S) ⟶ A.F) ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 :=
    one_comp_iotaHom A a
  have e0 : (Over.mk (𝟙 S)).hom ≫ torsZeroL A = torsZeroL A :=
    (show (Over.mk (𝟙 S)).hom ≫ torsZeroL A = 𝟙 S ≫ torsZeroL A from rfl).trans
      (Category.id_comp _)
  have e : (1 : Over.mk (𝟙 S) ⟶ A.F).left = torsZeroL A :=
    (one_left_eq A (U := Over.mk (𝟙 S))).trans e0
  have h' := (comp_iota_eq_one_iff A (1 : Over.mk (𝟙 S) ⟶ A.F) a).1 h
  calc torsZeroL A ≫ A.iota a = (1 : Over.mk (𝟙 S) ⟶ A.F).left ≫ A.iota a :=
        congrArg (fun t => t ≫ A.iota a) e.symm
    _ = (Over.mk (𝟙 S)).hom ≫ torsZeroL A := h'
    _ = torsZeroL A := e0

theorem mem3_iff (a : O) :
    (∃ b : O, a = ((3 : ℕ) : O) * b) ↔ (a : Y3OrderMod.OMod 3) = 0 := by
  have h0 : ((0 : O) : Y3OrderMod.OMod 3) = 0 := by
    first
      | rfl
      | simp
  have h1 := (Y3OrderMod.coe_eq_coe_iff (M := 3) (x := a) (y := 0)).symm
  have h2 : (a : Y3OrderMod.OMod 3) = ((0 : O) : Y3OrderMod.OMod 3) ↔
      (a : Y3OrderMod.OMod 3) = 0 := by rw [h0]
  refine Iff.trans ?_ (h1.trans h2)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [sub_zero]; exact hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [← sub_zero a]; exact hb⟩

/-- The second clause of `IsGenAt 3` from the first, given a generator `Q`. -/
theorem isGenAt_of_clause1 {k : Type} [Field k] {s : Spec (CommRingCat.of k) ⟶ S}
    {P Q : Over.mk s ⟶ A.F} (hQ : IsGenAt 3 A s Q) (hP3 : P ^ 3 = 1)
    (h1 : ∀ a : O, P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      ∃ b : O, a = ((3 : ℕ) : O) * b) : IsGenAt 3 A s P := by
  refine ⟨h1, fun x hx => ?_⟩
  obtain ⟨hQ1, hQ2⟩ := hQ
  obtain ⟨c, hc⟩ := hQ2 P hP3
  have key : ∀ a : O, (∃ b : O, a * c = ((3 : ℕ) : O) * b) ↔ ∃ b : O, a = ((3 : ℕ) : O) * b := by
    intro a
    have e : P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) =
        Q ≫ (Over.homMk (A.iota (a * c)) (A.iota_over _) : A.F ⟶ A.F) := by
      rw [hc]
      exact comp_iota_comp_iota A Q c a
    exact (hQ1 (a * c)).symm.trans ((iff_of_eq (congrArg (fun t => t = 1) e)).symm.trans (h1 a))
  haveI : Finite (Y3OrderMod.OMod 3) := Y3OrderMod.finite_OMod 3 (by norm_num)
  have hinj : Function.Injective
      (fun y : Y3OrderMod.OMod 3 => y * (c : Y3OrderMod.OMod 3)) := by
    intro y1 y2 hy
    obtain ⟨a1, rfl⟩ := Y3OrderMod.coe_surjective 3 y1
    obtain ⟨a2, rfl⟩ := Y3OrderMod.coe_surjective 3 y2
    have hy' : ((a1 * c : O) : Y3OrderMod.OMod 3) = ((a2 * c : O) : Y3OrderMod.OMod 3) := by
      rw [RingCon.coe_mul, RingCon.coe_mul]
      exact hy
    obtain ⟨m, hm⟩ := Y3OrderMod.coe_eq_coe_iff.1 hy'
    have hm' : (a1 - a2) * c = ((3 : ℕ) : O) * m := by rw [sub_mul]; exact hm
    obtain ⟨b, hb⟩ := (key (a1 - a2)).1 ⟨m, hm'⟩
    exact Y3OrderMod.coe_eq_coe_iff.2 ⟨b, hb⟩
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj 1
  obtain ⟨d, rfl⟩ := Y3OrderMod.coe_surjective 3 y
  have hdc : ((d * c : O) : Y3OrderMod.OMod 3) = ((1 : O) : Y3OrderMod.OMod 3) := by
    rw [RingCon.coe_mul, RingCon.coe_one]
    exact hy
  obtain ⟨e, hde⟩ := Y3OrderMod.coe_eq_coe_iff.1 hdc
  have hQ3 : Q ≫ (Over.homMk (A.iota ((3 : ℕ) : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (hQ1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  obtain ⟨b, rfl⟩ := hQ2 x hx
  refine ⟨b * d, ?_⟩
  have hdc' : d * c = 1 + ((3 : ℕ) : O) * e := by
    rw [← hde]
    abel
  have hbdc : b * d * c = b + ((3 : ℕ) : O) * (b * e) := by
    rw [_root_.mul_assoc, hdc', mul_add, _root_.mul_one, Y3OrderMod.mul_natCast_mul]
  rw [hc, comp_iota_comp_iota, hbdc, comp_iota_add, comp_iota_natCast_mul_eq_one A 3 Q hQ3,
    _root_.mul_one]

/-- On 3-torsion, `ι(a)` only depends on `a` modulo 3. -/
theorem iota_congr_of_tors {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ 3 = 1)
    {a b : O} (hab : (a : Y3OrderMod.OMod 3) = (b : Y3OrderMod.OMod 3)) :
    P ≫ A.iota a = P ≫ A.iota b := by
  obtain ⟨c, hc⟩ := Y3OrderMod.coe_eq_coe_iff.1 hab
  have ha : a = b + ((3 : ℕ) : O) * c := by rw [← hc]; abel
  subst ha
  set x : Over.mk (P ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl with hx
  have h3 : x ≫ (Over.homMk (A.iota ((3 : ℕ) : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (comp_iotaHom_natCast A x 3).trans hP
  have key : x ≫ (Over.homMk (A.iota (b + ((3 : ℕ) : O) * c)) (A.iota_over _) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F) := by
    rw [comp_iota_add, comp_iota_natCast_mul_eq_one A 3 x h3, _root_.mul_one]
  exact congrArg (fun f : Over.mk (P ≫ A.F.hom) ⟶ A.F => f.left) key

end Alg

/-! ## 2. Points of spectra of fields -/

theorem spec_field_nonempty (k : Type) [Field k] : Nonempty ↥(Spec (CommRingCat.of k)) := by
  first
    | exact inferInstance
    | exact ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum k)⟩

/-- A geometric point over a point `y` of a scheme. -/
abbrev geomK {Y : Scheme.{0}} (y : Y) : Type := AlgebraicClosure (Y.residueField y)

def geomPt {Y : Scheme.{0}} (y : Y) : Spec (CommRingCat.of (geomK y)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (geomK y))) ≫
    Y.fromSpecResidueField y

theorem geomPt_apply {Y : Scheme.{0}} (y : Y) (q : ↥(Spec (CommRingCat.of (geomK y)))) :
    geomPt y q = y := by
  first
    | (rw [geomPt, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply])
    | (simp only [geomPt, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply])
    | exact Scheme.fromSpecResidueField_apply y _

/-! ## 3. The torsion, the maps `ι(a)` and `0` on it, and the loci `K a` -/

section Geom

variable {S : Scheme.{0}} (A : FEC S)

abbrev W3 : Scheme.{0} := pullback (A.iota ((3 : ℕ) : O)) (torsZeroL A)

abbrev j3 : W3 A ⟶ A.F.left := pullback.fst (A.iota ((3 : ℕ) : O)) (torsZeroL A)

instance j3_mono : Mono (j3 A) := by
  constructor
  intro Z a b h
  have e := torsFst_hom A 3
  apply pullback.hom_ext h
  calc a ≫ pullback.snd (A.iota ((3 : ℕ) : O)) (torsZeroL A)
      = a ≫ (pullback.fst (A.iota ((3 : ℕ) : O)) (torsZeroL A) ≫ A.F.hom) :=
        congrArg (fun t => a ≫ t) e.symm
    _ = (a ≫ pullback.fst (A.iota ((3 : ℕ) : O)) (torsZeroL A)) ≫ A.F.hom :=
        (Category.assoc _ _ _).symm
    _ = (b ≫ pullback.fst (A.iota ((3 : ℕ) : O)) (torsZeroL A)) ≫ A.F.hom :=
        congrArg (fun t => t ≫ A.F.hom) h
    _ = b ≫ (pullback.fst (A.iota ((3 : ℕ) : O)) (torsZeroL A) ≫ A.F.hom) :=
        Category.assoc _ _ _
    _ = b ≫ pullback.snd (A.iota ((3 : ℕ) : O)) (torsZeroL A) :=
        congrArg (fun t => b ≫ t) e

theorem tors3_j : (Over.homMk (U := Over.mk (j3 A ≫ A.F.hom)) (j3 A) rfl :
    Over.mk (j3 A ≫ A.F.hom) ⟶ A.F) ^ 3 = 1 :=
  (torsChar A 3 (W3 A) (j3 A)).1 ⟨𝟙 _, Category.id_comp _⟩

/-- A 3-torsion point lifted to `W`. -/
def torsLift {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ 3 = 1) :
    T ⟶ W3 A :=
  Classical.choose ((torsChar A 3 T P).2 hP)

theorem torsLift_fac {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ 3 = 1) :
    torsLift A P hP ≫ j3 A = P :=
  Classical.choose_spec ((torsChar A 3 T P).2 hP)

/-- `ι(a)` restricted to the 3-torsion. -/
def fa (a : O) : W3 A ⟶ W3 A :=
  torsLift A (j3 A ≫ A.iota a) (torsion_comp_iota_pt A (j3 A) a 3 (tors3_j A))

theorem fa_spec (a : O) : fa A a ≫ j3 A = j3 A ≫ A.iota a :=
  torsLift_fac A _ _

theorem tors3_zero : (Over.homMk (U := Over.mk ((j3 A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom))
    (j3 A ≫ A.F.hom ≫ torsZeroL A) rfl :
      Over.mk ((j3 A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom) ⟶ A.F) ^ 3 = 1 := by
  refine (torsPow_eq_one_iff A _ 3).2 ?_
  have hP : (j3 A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom = j3 A ≫ A.F.hom := by
    rw [Category.assoc, Category.assoc, torsZeroL_sec, Category.comp_id]
  calc (j3 A ≫ A.F.hom ≫ torsZeroL A) ≫ A.iota ((3 : ℕ) : O)
      = j3 A ≫ A.F.hom ≫ (torsZeroL A ≫ A.iota ((3 : ℕ) : O)) := by
        simp only [Category.assoc]
    _ = j3 A ≫ A.F.hom ≫ torsZeroL A := by rw [torsZeroL_iota]
    _ = ((j3 A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom) ≫ torsZeroL A := by
        rw [hP, Category.assoc]

/-- The zero map of the 3-torsion. -/
def z3 : W3 A ⟶ W3 A := torsLift A (j3 A ≫ A.F.hom ≫ torsZeroL A) (tors3_zero A)

theorem z3_spec : z3 A ≫ j3 A = j3 A ≫ A.F.hom ≫ torsZeroL A :=
  torsLift_fac A _ _

theorem fa_p (a : O) : fa A a ≫ j3 A ≫ A.F.hom = j3 A ≫ A.F.hom := by
  rw [← Category.assoc, fa_spec, Category.assoc, A.iota_over]

theorem z3_p : z3 A ≫ j3 A ≫ A.F.hom = j3 A ≫ A.F.hom := by
  rw [← Category.assoc, z3_spec, Category.assoc, Category.assoc, torsZeroL_sec,
    Category.comp_id]

/-- `(ι(a), 0) : W ⟶ W ×_S W`. -/
def L3 (a : O) : W3 A ⟶ pullback (j3 A ≫ A.F.hom) (j3 A ≫ A.F.hom) :=
  pullback.lift (fa A a) (z3 A) ((fa_p A a).trans (z3_p A).symm)

theorem L3_fst (a : O) :
    L3 A a ≫ pullback.fst (j3 A ≫ A.F.hom) (j3 A ≫ A.F.hom) = fa A a :=
  pullback.lift_fst _ _ _

theorem L3_snd (a : O) :
    L3 A a ≫ pullback.snd (j3 A ≫ A.F.hom) (j3 A ≫ A.F.hom) = z3 A :=
  pullback.lift_snd _ _ _

theorem diag_open (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) :
    IsOpenImmersion (pullback.diagonal (j3 A ≫ A.F.hom)) := by
  haveI : AlgebraicGeometry.Etale (j3 A ≫ A.F.hom) := torsFst_hom_etale A 3 het
  first
    | exact AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal (j3 A ≫ A.F.hom)
    | infer_instance

theorem diag_closed (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O))) :
    IsClosedImmersion (pullback.diagonal (j3 A ≫ A.F.hom)) := by
  haveI hf : AlgebraicGeometry.IsFinite (j3 A ≫ A.F.hom) := torsFst_hom_isFinite A 3 hfin
  haveI : AlgebraicGeometry.IsSeparated (j3 A ≫ A.F.hom) := by
    first
      | infer_instance
      | (haveI : IsProper (j3 A ≫ A.F.hom) :=
            (AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mp hf).1
         infer_instance)
  exact AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal

/-- The locus where `ι(a)` vanishes on the 3-torsion. -/
def K3 (a : O) : Set ↥(W3 A) :=
  ⇑(L3 A a) ⁻¹' Set.range ⇑(pullback.diagonal (j3 A ≫ A.F.hom))

theorem isOpen_K3 (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) (a : O) :
    IsOpen (K3 A a) := by
  haveI := diag_open A het
  exact IsOpen.preimage (L3 A a).continuous
    (IsOpenImmersion.isOpen_range (pullback.diagonal (j3 A ≫ A.F.hom)))

theorem isClosed_K3 (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O))) (a : O) :
    IsClosed (K3 A a) := by
  haveI := diag_closed A hfin
  exact IsClosed.preimage (L3 A a).continuous
    (Scheme.Hom.isClosedEmbedding (pullback.diagonal (j3 A ≫ A.F.hom))).isClosed_range

/-- The image of `h` lies in `K a` iff `ι(a) ∘ h = 0 ∘ h`. -/
theorem range_sub_K3_iff (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O)))
    {Y : Scheme.{0}} (h : Y ⟶ W3 A) (a : O) :
    Set.range ⇑h ⊆ K3 A a ↔ h ≫ fa A a = h ≫ z3 A := by
  haveI := diag_open A het
  constructor
  · intro hr
    have hr' : Set.range ⇑(h ≫ L3 A a) ⊆
        Set.range ⇑(pullback.diagonal (j3 A ≫ A.F.hom)) := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hr ⟨y, rfl⟩
    have he := IsOpenImmersion.lift_fac (pullback.diagonal (j3 A ≫ A.F.hom)) (h ≫ L3 A a) hr'
    have h1 := congrArg (fun t => t ≫ pullback.fst (j3 A ≫ A.F.hom) (j3 A ≫ A.F.hom)) he
    have h2 := congrArg (fun t => t ≫ pullback.snd (j3 A ≫ A.F.hom) (j3 A ≫ A.F.hom)) he
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      L3_fst, L3_snd] at h1 h2
    exact h1.symm.trans h2
  · intro heq
    have hL : h ≫ L3 A a = (h ≫ fa A a) ≫ pullback.diagonal (j3 A ≫ A.F.hom) := by
      apply pullback.hom_ext
      · rw [Category.assoc, L3_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, L3_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact heq.symm
    rintro _ ⟨y, rfl⟩
    show ⇑(L3 A a) (h y) ∈ Set.range ⇑(pullback.diagonal (j3 A ≫ A.F.hom))
    refine ⟨fa A a (h y), ?_⟩
    have hy := congrArg
      (fun t : Y ⟶ pullback (j3 A ≫ A.F.hom) (j3 A ≫ A.F.hom) => t y) hL
    simp only [Scheme.Hom.comp_apply] at hy
    exact hy.symm

theorem comp_fa_eq_iff {Y : Scheme.{0}} (h : Y ⟶ W3 A) (a : O) :
    h ≫ fa A a = h ≫ z3 A ↔
      (h ≫ j3 A) ≫ A.iota a = ((h ≫ j3 A) ≫ A.F.hom) ≫ torsZeroL A := by
  have e1 : (h ≫ fa A a) ≫ j3 A = (h ≫ j3 A) ≫ A.iota a := by
    simp only [Category.assoc, fa_spec]
  have e2 : (h ≫ z3 A) ≫ j3 A = ((h ≫ j3 A) ≫ A.F.hom) ≫ torsZeroL A := by
    simp only [Category.assoc, z3_spec]
  refine (cancel_mono (j3 A)).symm.trans ?_
  rw [e1, e2]

theorem geom_cond_iff {T Y : Scheme.{0}} (g : T ⟶ W3 A) (P : T ⟶ A.F.left)
    (hP : g ≫ j3 A = P) (s : Y ⟶ T) (a : O) :
    (s ≫ g) ≫ fa A a = (s ≫ g) ≫ z3 A ↔
      (s ≫ P) ≫ A.iota a = (s ≫ P ≫ A.F.hom) ≫ torsZeroL A := by
  subst hP
  refine (comp_fa_eq_iff A (s ≫ g) a).trans ?_
  simp only [Category.assoc]

theorem mem_K3_iff (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O)))
    {Y : Scheme.{0}} (g : Y ⟶ W3 A) (y : Y) (a : O) :
    g y ∈ K3 A a ↔ (geomPt y ≫ g) ≫ fa A a = (geomPt y ≫ g) ≫ z3 A := by
  refine Iff.trans ?_ (range_sub_K3_iff A het (geomPt y ≫ g) a)
  constructor
  · rintro hy _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, geomPt_apply]
    exact hy
  · intro hr
    obtain ⟨q⟩ := spec_field_nonempty (geomK y)
    have hq := hr ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, geomPt_apply] at hq
    exact hq

/-! ## 4. The clopen subscheme `Z` -/

/-- A representative in `O` of a class modulo 3. -/
def repO (q : Y3OrderMod.OMod 3) : O := Classical.choose (Y3OrderMod.coe_surjective 3 q)

theorem repO_spec (q : Y3OrderMod.OMod 3) : ((repO q : O) : Y3OrderMod.OMod 3) = q :=
  Classical.choose_spec (Y3OrderMod.coe_surjective 3 q)

theorem fa_congr {a b : O} (hab : (a : Y3OrderMod.OMod 3) = (b : Y3OrderMod.OMod 3)) :
    fa A a = fa A b :=
  (cancel_mono (j3 A)).1 ((fa_spec A a).trans
    ((iota_congr_of_tors A (j3 A) (tors3_j A) hab).trans (fa_spec A b).symm))

theorem K3_congr {a b : O} (hab : (a : Y3OrderMod.OMod 3) = (b : Y3OrderMod.OMod 3)) :
    K3 A a = K3 A b := by
  have hL : L3 A a = L3 A b :=
    pullback.hom_ext ((L3_fst A a).trans ((fa_congr A hab).trans (L3_fst A b).symm))
      ((L3_snd A a).trans (L3_snd A b).symm)
  unfold K3
  rw [hL]

/-- The union of the `K a` over `a ∉ 3O`, indexed by nonzero classes modulo 3. -/
def Bad3 : Set ↥(W3 A) := ⋃ q : {q : Y3OrderMod.OMod 3 // q ≠ 0}, K3 A (repO q.1)

theorem mem_Bad3_iff (w : ↥(W3 A)) :
    w ∈ Bad3 A ↔ ∃ a : O, ¬ (∃ b : O, a = ((3 : ℕ) : O) * b) ∧ w ∈ K3 A a := by
  constructor
  · intro hw
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hw
    exact ⟨repO q.1, fun h => q.2 ((repO_spec q.1).symm.trans ((mem3_iff (repO q.1)).1 h)), hq⟩
  · rintro ⟨a, ha, hw⟩
    have hq : (a : Y3OrderMod.OMod 3) ≠ 0 := fun h => ha ((mem3_iff a).2 h)
    refine Set.mem_iUnion.2 ⟨⟨(a : Y3OrderMod.OMod 3), hq⟩, ?_⟩
    have e := K3_congr A (repO_spec (a : Y3OrderMod.OMod 3))
    exact (congrArg (fun s => w ∈ s) e).mpr hw

theorem isClosed_Bad3 (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O))) :
    IsClosed (Bad3 A) := by
  haveI : Finite (Y3OrderMod.OMod 3) := Y3OrderMod.finite_OMod 3 (by norm_num)
  exact isClosed_iUnion_of_finite (fun q => isClosed_K3 A hfin _)

theorem isOpen_Bad3 (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) :
    IsOpen (Bad3 A) :=
  isOpen_iUnion (fun q => isOpen_K3 A het _)

/-- `Z`, as an open subscheme of `W`. -/
def U3 (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O))) : (W3 A).Opens :=
  ⟨(Bad3 A)ᶜ, (isClosed_Bad3 A hfin).isOpen_compl⟩

theorem U3_isClosedImmersion (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) :
    IsClosedImmersion (U3 A hfin).ι := by
  haveI : IsPreimmersion (U3 A hfin).ι := inferInstance
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (isOpen_Bad3 A het).isClosed_compl

/-- The inclusion `Z ⟶ A`. -/
def i3 (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O))) :
    ((U3 A hfin : (W3 A).Opens) : Scheme.{0}) ⟶ A.F.left :=
  (U3 A hfin).ι ≫ j3 A

theorem range_sub_U3_iff (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    {T : Scheme.{0}} (g : T ⟶ W3 A) :
    Set.range ⇑g ⊆ ((U3 A hfin : (W3 A).Opens) : Set ↥(W3 A)) ↔
      ∀ (t : T) (a : O), ¬ (∃ b : O, a = ((3 : ℕ) : O) * b) → g t ∉ K3 A a := by
  constructor
  · intro hr t a ha hK
    have h1 : g t ∈ (Bad3 A)ᶜ := hr ⟨t, rfl⟩
    exact h1 ((mem_Bad3_iff A _).2 ⟨a, ha, hK⟩)
  · rintro hall _ ⟨t, rfl⟩
    show g t ∈ (Bad3 A)ᶜ
    intro hy
    obtain ⟨a, ha, hK⟩ := (mem_Bad3_iff A _).1 hy
    exact hall t a ha hK

/-! ## 5. The pointwise characterization -/

/-- The generator hypothesis for one family. -/
def GeomFreeAt : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    ∃ Q : Over.mk s ⟶ A.F, IsGenAt 3 A s Q

theorem isGen_of_lift (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O)))
    (hF : GeomFreeAt A) {T : Scheme.{0}} (g : T ⟶ W3 A) (P : T ⟶ A.F.left)
    (hP : g ≫ j3 A = P)
    (hall : ∀ (t : T) (a : O), ¬ (∃ b : O, a = ((3 : ℕ) : O) * b) → g t ∉ K3 A a) :
    IsGen 3 A P := by
  have htors : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl :
      Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ 3 = 1 := (torsChar A 3 T P).1 ⟨g, hP⟩
  have hPt : P ≫ A.iota ((3 : ℕ) : O) = (P ≫ A.F.hom) ≫ torsZeroL A :=
    (torsPow_eq_one_iff A P 3).1 htors
  dsimp only [IsGen]
  refine ⟨htors, ?_⟩
  intro k _ _ s
  set Ps : Over.mk (s ≫ P ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (s ≫ P ≫ A.F.hom)) (s ≫ P) (Category.assoc _ _ _) with hPs
  have hs3 : (s ≫ P) ≫ A.iota ((3 : ℕ) : O) = (s ≫ P ≫ A.F.hom) ≫ torsZeroL A := by
    simp only [Category.assoc, hPt]
  have hPs3' : Ps ≫ (Over.homMk (A.iota ((3 : ℕ) : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (comp_iota_eq_one_iff A Ps _).2 hs3
  have hP3 : Ps ^ 3 = 1 := (comp_iotaHom_natCast A Ps 3).symm.trans hPs3'
  have h1 : ∀ a : O, Ps ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      ∃ b : O, a = ((3 : ℕ) : O) * b := by
    intro a
    constructor
    · intro hone
      have heq : (s ≫ P) ≫ A.iota a = (s ≫ P ≫ A.F.hom) ≫ torsZeroL A :=
        (comp_iota_eq_one_iff A Ps a).1 hone
      by_contra ha
      have hcond : (s ≫ g) ≫ fa A a = (s ≫ g) ≫ z3 A := (geom_cond_iff A g P hP s a).2 heq
      have hr := (range_sub_K3_iff A het (s ≫ g) a).2 hcond
      obtain ⟨q⟩ := spec_field_nonempty k
      have hq : (s ≫ g) q ∈ K3 A a := hr ⟨q, rfl⟩
      rw [Scheme.Hom.comp_apply] at hq
      exact hall (s q) a ha hq
    · rintro ⟨b, rfl⟩
      exact comp_iota_natCast_mul_eq_one A 3 Ps hPs3' b
  obtain ⟨Q, hQ⟩ := hF k (s ≫ P ≫ A.F.hom)
  exact isGenAt_of_clause1 A hQ hP3 h1

theorem hall_of_isGen (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O)))
    {T : Scheme.{0}} (g : T ⟶ W3 A) (P : T ⟶ A.F.left) (hP : g ≫ j3 A = P)
    (hG : IsGen 3 A P) :
    ∀ (t : T) (a : O), ¬ (∃ b : O, a = ((3 : ℕ) : O) * b) → g t ∉ K3 A a := by
  intro t a ha hK
  dsimp only [IsGen] at hG
  obtain ⟨-, h2⟩ := hG
  have hcond := (mem_K3_iff A het g t a).1 hK
  have heq := (geom_cond_iff A g P hP (geomPt t) a).1 hcond
  have hone := (comp_iota_eq_one_iff A
    (Over.homMk (U := Over.mk (geomPt t ≫ P ≫ A.F.hom)) (geomPt t ≫ P)
      (Category.assoc _ _ _)) a).2 heq
  exact ha (((h2 (geomK t) (geomPt t)).1 a).1 hone)

theorem char3 (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) (hF : GeomFreeAt A)
    (T : Scheme.{0}) (P : T ⟶ A.F.left) :
    (∃ f : T ⟶ ((U3 A hfin : (W3 A).Opens) : Scheme.{0}), f ≫ i3 A hfin = P) ↔
      IsGen 3 A P := by
  constructor
  · rintro ⟨f, rfl⟩
    have hg : (f ≫ (U3 A hfin).ι) ≫ j3 A = f ≫ i3 A hfin := Category.assoc _ _ _
    have hrange : Set.range ⇑(f ≫ (U3 A hfin).ι) ⊆
        ((U3 A hfin : (W3 A).Opens) : Set ↥(W3 A)) := by
      rintro _ ⟨y, rfl⟩
      have hm : (U3 A hfin).ι (f y) ∈ Set.range ⇑(U3 A hfin).ι := ⟨f y, rfl⟩
      rw [Scheme.Opens.range_ι] at hm
      rw [Scheme.Hom.comp_apply]
      exact hm
    exact isGen_of_lift A het hF (f ≫ (U3 A hfin).ι) _ hg
      ((range_sub_U3_iff A hfin _).1 hrange)
  · intro hG
    have htors : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl :
        Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ 3 = 1 := by
      dsimp only [IsGen] at hG
      exact hG.1
    obtain ⟨g, hg⟩ := (torsChar A 3 T P).2 htors
    have hr : Set.range ⇑g ⊆ ((U3 A hfin : (W3 A).Opens) : Set ↥(W3 A)) :=
      (range_sub_U3_iff A hfin g).2 (hall_of_isGen A het g P hg hG)
    haveI : IsOpenImmersion (U3 A hfin).ι := inferInstance
    have hr' : Set.range ⇑g ⊆ Set.range ⇑(U3 A hfin).ι := by
      rw [Scheme.Opens.range_ι]
      exact hr
    refine ⟨IsOpenImmersion.lift (U3 A hfin).ι g hr', ?_⟩
    show IsOpenImmersion.lift (U3 A hfin).ι g hr' ≫ (U3 A hfin).ι ≫ j3 A = P
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact hg

/-! ## 6. Surjectivity -/

theorem surj3 (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) (hF : GeomFreeAt A) :
    Function.Surjective ⇑(i3 A hfin ≫ A.F.hom) := by
  intro x
  obtain ⟨Q, hQ⟩ := hF (geomK x) (geomPt x)
  have hQ' := hQ
  obtain ⟨hQ1, -⟩ := hQ'
  have hQ3 : Q ≫ (Over.homMk (A.iota ((3 : ℕ) : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (hQ1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  have hw : Q.left ≫ A.F.hom = geomPt x := Over.w Q
  -- `Q.left` is 3-torsion
  have hQt : Q.left ≫ A.iota ((3 : ℕ) : O) = (Q.left ≫ A.F.hom) ≫ torsZeroL A :=
    ((comp_iota_eq_one_iff A Q _).1 hQ3).trans
      (congrArg (fun t => t ≫ torsZeroL A) hw.symm)
  obtain ⟨g, hg⟩ := (torsChar A 3 _ Q.left).2 ((torsPow_eq_one_iff A Q.left 3).2 hQt)
  have hall : ∀ (t : ↥(Spec (CommRingCat.of (geomK x)))) (a : O),
      ¬ (∃ b : O, a = ((3 : ℕ) : O) * b) → g t ∉ K3 A a := by
    intro t a ha hK
    apply ha
    have hr : Set.range ⇑g ⊆ K3 A a := by
      rintro _ ⟨t', rfl⟩
      have htt : t' = t := by
        first
          | exact Subsingleton.elim t' t
          | (have key : ∀ q : PrimeSpectrum (geomK x), q.asIdeal = ⊥ := fun q =>
                (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
             exact PrimeSpectrum.ext ((key t').trans (key t).symm))
      rw [htt]
      exact hK
    have hcond := (range_sub_K3_iff A het g a).1 hr
    have heq := (geom_cond_iff A g Q.left hg (𝟙 _) a).1
      (by simpa only [Category.id_comp] using hcond)
    have heq' : Q.left ≫ A.iota a = (Over.mk (geomPt x)).hom ≫ torsZeroL A := by
      have e := heq
      simp only [Category.id_comp] at e
      exact e.trans (congrArg (fun t => t ≫ torsZeroL A) hw)
    exact (hQ1 a).1 ((comp_iota_eq_one_iff A Q a).2 heq')
  have hr : Set.range ⇑g ⊆ Set.range ⇑(U3 A hfin).ι := by
    rw [Scheme.Opens.range_ι]
    exact (range_sub_U3_iff A hfin g).2 hall
  haveI : IsOpenImmersion (U3 A hfin).ι := inferInstance
  obtain ⟨q⟩ := spec_field_nonempty (geomK x)
  refine ⟨IsOpenImmersion.lift (U3 A hfin).ι g hr q, ?_⟩
  have hfac : IsOpenImmersion.lift (U3 A hfin).ι g hr ≫ i3 A hfin ≫ A.F.hom = geomPt x := by
    show IsOpenImmersion.lift (U3 A hfin).ι g hr ≫ ((U3 A hfin).ι ≫ j3 A) ≫ A.F.hom = geomPt x
    rw [← Category.assoc, ← Category.assoc, IsOpenImmersion.lift_fac, hg]
    exact hw
  have := congrArg (fun t : Spec (CommRingCat.of (geomK x)) ⟶ S => t q) hfac
  simp only [Scheme.Hom.comp_apply] at this
  rw [Scheme.Hom.comp_apply]
  exact this.trans (geomPt_apply x q)

/-! ## 7. Properties of `i` -/

theorem i3_isClosedImmersion (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) : IsClosedImmersion (i3 A hfin) := by
  haveI := U3_isClosedImmersion A hfin het
  haveI := torsFst_isClosedImmersion A 3
  first
    | (unfold i3; infer_instance)
    | exact MorphismProperty.comp_mem (@IsClosedImmersion) _ _ inferInstance inferInstance

theorem i3_isFinite (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) :
    AlgebraicGeometry.IsFinite (i3 A hfin ≫ A.F.hom) := by
  haveI := U3_isClosedImmersion A hfin het
  have h1 : AlgebraicGeometry.IsFinite (U3 A hfin).ι := inferInstance
  have h2 : AlgebraicGeometry.IsFinite (j3 A ≫ A.F.hom) := torsFst_hom_isFinite A 3 hfin
  show AlgebraicGeometry.IsFinite (((U3 A hfin).ι ≫ j3 A) ≫ A.F.hom)
  rw [Category.assoc]
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.IsFinite) _ _ h1 h2

theorem i3_etale (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) :
    AlgebraicGeometry.Etale (i3 A hfin ≫ A.F.hom) := by
  haveI h1 : AlgebraicGeometry.Etale (U3 A hfin).ι := inferInstance
  haveI h2 : AlgebraicGeometry.Etale (j3 A ≫ A.F.hom) := torsFst_hom_etale A 3 het
  show AlgebraicGeometry.Etale (((U3 A hfin).ι ≫ j3 A) ≫ A.F.hom)
  rw [Category.assoc]
  first
    | infer_instance
    | exact (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).2
        (smoothOfRelativeDimension_comp
          (hf := (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).1 h1)
          (hg := (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).1 h2) 0 0 _ _)

end Geom

/-! ## 8. The theorem -/

theorem frameRep3_of (hM : MilneProp207 3) (hF : GeomFree3) : BuzzardFrameRep 3 := by
  intro S A
  have hfin := (hM S A).1
  have het := (hM S A).2
  have hFA : GeomFreeAt A := fun k _ _ s => hF S A k s
  refine ⟨_, i3 A hfin, i3_isClosedImmersion A hfin het, i3_isFinite A hfin het,
    i3_etale A hfin het, ?_, fun T P => char3 A hfin het hFA T P⟩
  first
    | exact ⟨surj3 A hfin het hFA⟩
    | exact { surj := surj3 A hfin het hFA }

end Y3Buzzard
