import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.Defs
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Frame representability at an arbitrary level

From `MilneProp207 M` (multiplication by `M` is finite and etale) and `GeomFreeM M` (the
`M`-torsion of every geometric fibre has a generator) we prove `BuzzardFrameRep M` for every
`M ≠ 0`. The argument is the one at level three, with `3` replaced by `M`.

1. `W := A[M]`, the fibre of `ι(M)` over the zero section, with `j : W ⟶ A` and `W ⟶ S`
   finite etale.
2. For `a : O`, `K a ⊆ W` is the locus where `ι(a)` vanishes: the preimage of the diagonal of
   `W ⟶ S` under `(ι(a), 0) : W ⟶ W ×_S W`. It is open (the diagonal of an etale map is an
   open immersion) and closed (the diagonal of a finite map is a closed immersion).
3. `Z := W \ ⋃_{a ∉ MO} K a`, a union indexed by the nonzero classes of `O/MO`. Since `M ≠ 0`
   the ring `O/MO` is finite, so the union is finite and closed. The inclusion of `Z` is an
   open immersion with closed range, hence a closed immersion.
4. A point factors through `Z` iff it generates the `M`-torsion at every geometric point; the
   second clause of `IsGenAt` follows from the first and a generator, since right
   multiplication by an element of the finite ring `O/MO` is injective iff bijective.
5. `Z ⟶ S` is surjective: a generator at a geometric point lands in `Z`.

The only property of the level used besides the two hypotheses is `M ≠ 0`, through the
finiteness of `O/MO` in steps 3 and 4. For `M = 0` the ring `O/MO = O` is infinite and the
union in step 3 need not be closed.
-/

attribute [local instance] FEC.grp

namespace LevelM

/-! ## 1. Algebra -/

section Alg

variable (M : ℕ) {S : Scheme.{0}} (A : FEC S)

theorem memM_iff (a : O) :
    (∃ b : O, a = (M : O) * b) ↔ (a : Y3OrderMod.OMod M) = 0 := by
  have h0 : ((0 : O) : Y3OrderMod.OMod M) = 0 := rfl
  have h1 := (Y3OrderMod.coe_eq_coe_iff (M := M) (x := a) (y := 0)).symm
  have h2 : (a : Y3OrderMod.OMod M) = ((0 : O) : Y3OrderMod.OMod M) ↔
      (a : Y3OrderMod.OMod M) = 0 := by rw [h0]
  refine Iff.trans ?_ (h1.trans h2)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [sub_zero]; exact hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [← sub_zero a]; exact hb⟩

/-- The second clause of `IsGenAt M` from the first, given a generator `Q`. -/
theorem isGenAt_of_clause1 [NeZero M] {k : Type} [Field k] {s : Spec (CommRingCat.of k) ⟶ S}
    {P Q : Over.mk s ⟶ A.F} (hQ : IsGenAt M A s Q) (hPM : P ^ M = 1)
    (h1 : ∀ a : O, P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      ∃ b : O, a = (M : O) * b) : IsGenAt M A s P := by
  refine ⟨h1, fun x hx => ?_⟩
  obtain ⟨hQ1, hQ2⟩ := hQ
  obtain ⟨c, hc⟩ := hQ2 P hPM
  have key : ∀ a : O, (∃ b : O, a * c = (M : O) * b) ↔ ∃ b : O, a = (M : O) * b := by
    intro a
    have e : P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) =
        Q ≫ (Over.homMk (A.iota (a * c)) (A.iota_over _) : A.F ⟶ A.F) := by
      rw [hc]
      exact comp_iota_comp_iota A Q c a
    exact (hQ1 (a * c)).symm.trans ((iff_of_eq (congrArg (fun t => t = 1) e)).symm.trans (h1 a))
  have : Finite (Y3OrderMod.OMod M) := Y3OrderMod.instFiniteOMod M
  have hinj : Function.Injective
      (fun y : Y3OrderMod.OMod M => y * (c : Y3OrderMod.OMod M)) := by
    intro y1 y2 hy
    obtain ⟨a1, rfl⟩ := Y3OrderMod.coe_surjective M y1
    obtain ⟨a2, rfl⟩ := Y3OrderMod.coe_surjective M y2
    have hy' : ((a1 * c : O) : Y3OrderMod.OMod M) = ((a2 * c : O) : Y3OrderMod.OMod M) := by
      rw [RingCon.coe_mul, RingCon.coe_mul]
      exact hy
    obtain ⟨m, hm⟩ := Y3OrderMod.coe_eq_coe_iff.1 hy'
    have hm' : (a1 - a2) * c = (M : O) * m := by rw [sub_mul]; exact hm
    obtain ⟨b, hb⟩ := (key (a1 - a2)).1 ⟨m, hm'⟩
    exact Y3OrderMod.coe_eq_coe_iff.2 ⟨b, hb⟩
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj 1
  obtain ⟨d, rfl⟩ := Y3OrderMod.coe_surjective M y
  have hdc : ((d * c : O) : Y3OrderMod.OMod M) = ((1 : O) : Y3OrderMod.OMod M) := by
    rw [RingCon.coe_mul, RingCon.coe_one]
    exact hy
  obtain ⟨e, hde⟩ := Y3OrderMod.coe_eq_coe_iff.1 hdc
  have hQM : Q ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (hQ1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  obtain ⟨b, rfl⟩ := hQ2 x hx
  refine ⟨b * d, ?_⟩
  have hdc' : d * c = 1 + (M : O) * e := by
    rw [← hde]
    abel
  have hbdc : b * d * c = b + (M : O) * (b * e) := by
    rw [_root_.mul_assoc, hdc', mul_add, _root_.mul_one, Y3OrderMod.mul_natCast_mul]
  rw [hc, comp_iota_comp_iota, hbdc, comp_iota_add, comp_iota_natCast_mul_eq_one A M Q hQM,
    _root_.mul_one]

/-- On `M`-torsion, `ι(a)` only depends on `a` modulo `M`. -/
theorem iota_congr_of_tors {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1)
    {a b : O} (hab : (a : Y3OrderMod.OMod M) = (b : Y3OrderMod.OMod M)) :
    P ≫ A.iota a = P ≫ A.iota b := by
  obtain ⟨c, hc⟩ := Y3OrderMod.coe_eq_coe_iff.1 hab
  have ha : a = b + (M : O) * c := by rw [← hc]; abel
  subst ha
  set x : Over.mk (P ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl with hx
  have hxM : x ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (comp_iotaHom_natCast A x M).trans hP
  have key : x ≫ (Over.homMk (A.iota (b + (M : O) * c)) (A.iota_over _) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F) := by
    rw [comp_iota_add, comp_iota_natCast_mul_eq_one A M x hxM, _root_.mul_one]
  exact congrArg (fun f : Over.mk (P ≫ A.F.hom) ⟶ A.F => f.left) key

end Alg

/-! ## 2. The torsion, the maps `ι(a)` and `0` on it, and the loci `K a` -/

section Geom

variable (M : ℕ) {S : Scheme.{0}} (A : FEC S)

/-- The `M`-torsion: the fibre of `ι(M)` over the zero section. -/
abbrev WM : Scheme.{0} := pullback (A.iota (M : O)) (torsZeroL A)

/-- The inclusion of the `M`-torsion into `A`. -/
abbrev jM : WM M A ⟶ A.F.left := pullback.fst (A.iota (M : O)) (torsZeroL A)

instance jM_mono : Mono (jM M A) := by
  constructor
  intro Z a b h
  have e := torsFst_hom A M
  apply pullback.hom_ext h
  calc a ≫ pullback.snd (A.iota (M : O)) (torsZeroL A)
      = a ≫ (pullback.fst (A.iota (M : O)) (torsZeroL A) ≫ A.F.hom) :=
        congrArg (fun t => a ≫ t) e.symm
    _ = (a ≫ pullback.fst (A.iota (M : O)) (torsZeroL A)) ≫ A.F.hom :=
        (Category.assoc _ _ _).symm
    _ = (b ≫ pullback.fst (A.iota (M : O)) (torsZeroL A)) ≫ A.F.hom :=
        congrArg (fun t => t ≫ A.F.hom) h
    _ = b ≫ (pullback.fst (A.iota (M : O)) (torsZeroL A) ≫ A.F.hom) :=
        Category.assoc _ _ _
    _ = b ≫ pullback.snd (A.iota (M : O)) (torsZeroL A) :=
        congrArg (fun t => b ≫ t) e

theorem torsM_j : (Over.homMk (U := Over.mk (jM M A ≫ A.F.hom)) (jM M A) rfl :
    Over.mk (jM M A ≫ A.F.hom) ⟶ A.F) ^ M = 1 :=
  (torsChar A M (WM M A) (jM M A)).1 ⟨𝟙 _, Category.id_comp _⟩

/-- An `M`-torsion point lifted to `W`. -/
def torsLift {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1) :
    T ⟶ WM M A :=
  Classical.choose ((torsChar A M T P).2 hP)

theorem torsLift_fac {T : Scheme.{0}} (P : T ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1) :
    torsLift M A P hP ≫ jM M A = P :=
  Classical.choose_spec ((torsChar A M T P).2 hP)

/-- `ι(a)` restricted to the `M`-torsion. -/
def fa (a : O) : WM M A ⟶ WM M A :=
  torsLift M A (jM M A ≫ A.iota a) (torsion_comp_iota_pt A (jM M A) a M (torsM_j M A))

theorem fa_spec (a : O) : fa M A a ≫ jM M A = jM M A ≫ A.iota a :=
  torsLift_fac M A _ _

theorem torsM_zero : (Over.homMk (U := Over.mk ((jM M A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom))
    (jM M A ≫ A.F.hom ≫ torsZeroL A) rfl :
      Over.mk ((jM M A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom) ⟶ A.F) ^ M = 1 := by
  refine (torsPow_eq_one_iff A _ M).2 ?_
  have hP : (jM M A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom = jM M A ≫ A.F.hom := by
    rw [Category.assoc, Category.assoc, torsZeroL_sec, Category.comp_id]
  calc (jM M A ≫ A.F.hom ≫ torsZeroL A) ≫ A.iota (M : O)
      = jM M A ≫ A.F.hom ≫ (torsZeroL A ≫ A.iota (M : O)) := by
        simp only [Category.assoc]
    _ = jM M A ≫ A.F.hom ≫ torsZeroL A := by rw [torsZeroL_iota]
    _ = ((jM M A ≫ A.F.hom ≫ torsZeroL A) ≫ A.F.hom) ≫ torsZeroL A := by
        rw [hP, Category.assoc]

/-- The zero map of the `M`-torsion. -/
def zM : WM M A ⟶ WM M A := torsLift M A (jM M A ≫ A.F.hom ≫ torsZeroL A) (torsM_zero M A)

theorem zM_spec : zM M A ≫ jM M A = jM M A ≫ A.F.hom ≫ torsZeroL A :=
  torsLift_fac M A _ _

theorem fa_p (a : O) : fa M A a ≫ jM M A ≫ A.F.hom = jM M A ≫ A.F.hom := by
  rw [← Category.assoc, fa_spec, Category.assoc, A.iota_over]

theorem zM_p : zM M A ≫ jM M A ≫ A.F.hom = jM M A ≫ A.F.hom := by
  rw [← Category.assoc, zM_spec, Category.assoc, Category.assoc, torsZeroL_sec,
    Category.comp_id]

/-- `(ι(a), 0) : W ⟶ W ×_S W`. -/
def LM (a : O) : WM M A ⟶ pullback (jM M A ≫ A.F.hom) (jM M A ≫ A.F.hom) :=
  pullback.lift (fa M A a) (zM M A) ((fa_p M A a).trans (zM_p M A).symm)

theorem LM_fst (a : O) :
    LM M A a ≫ pullback.fst (jM M A ≫ A.F.hom) (jM M A ≫ A.F.hom) = fa M A a :=
  pullback.lift_fst _ _ _

theorem LM_snd (a : O) :
    LM M A a ≫ pullback.snd (jM M A ≫ A.F.hom) (jM M A ≫ A.F.hom) = zM M A :=
  pullback.lift_snd _ _ _

theorem diag_open (het : AlgebraicGeometry.Etale (A.iota (M : O))) :
    IsOpenImmersion (pullback.diagonal (jM M A ≫ A.F.hom)) := by
  have : AlgebraicGeometry.Etale (jM M A ≫ A.F.hom) := torsFst_hom_etale A M het
  exact AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal (jM M A ≫ A.F.hom)

theorem diag_closed (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O))) :
    IsClosedImmersion (pullback.diagonal (jM M A ≫ A.F.hom)) := by
  have : AlgebraicGeometry.IsFinite (jM M A ≫ A.F.hom) := torsFst_hom_isFinite A M hfin
  have : AlgebraicGeometry.IsSeparated (jM M A ≫ A.F.hom) := inferInstance
  exact AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal

/-- The locus where `ι(a)` vanishes on the `M`-torsion. -/
def KM (a : O) : Set ↥(WM M A) :=
  ⇑(LM M A a) ⁻¹' Set.range ⇑(pullback.diagonal (jM M A ≫ A.F.hom))

theorem isOpen_KM (het : AlgebraicGeometry.Etale (A.iota (M : O))) (a : O) :
    IsOpen (KM M A a) := by
  have := diag_open M A het
  exact IsOpen.preimage (LM M A a).continuous
    (IsOpenImmersion.isOpen_range (pullback.diagonal (jM M A ≫ A.F.hom)))

theorem isClosed_KM (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O))) (a : O) :
    IsClosed (KM M A a) := by
  have := diag_closed M A hfin
  exact IsClosed.preimage (LM M A a).continuous
    (Scheme.Hom.isClosedEmbedding (pullback.diagonal (jM M A ≫ A.F.hom))).isClosed_range

/-- The image of `h` lies in `K a` iff `ι(a) ∘ h = 0 ∘ h`. -/
theorem range_sub_KM_iff (het : AlgebraicGeometry.Etale (A.iota (M : O)))
    {Y : Scheme.{0}} (h : Y ⟶ WM M A) (a : O) :
    Set.range ⇑h ⊆ KM M A a ↔ h ≫ fa M A a = h ≫ zM M A := by
  have := diag_open M A het
  constructor
  · intro hr
    have hr' : Set.range ⇑(h ≫ LM M A a) ⊆
        Set.range ⇑(pullback.diagonal (jM M A ≫ A.F.hom)) := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hr ⟨y, rfl⟩
    have he := IsOpenImmersion.lift_fac (pullback.diagonal (jM M A ≫ A.F.hom))
      (h ≫ LM M A a) hr'
    have h1 := congrArg (fun t => t ≫ pullback.fst (jM M A ≫ A.F.hom) (jM M A ≫ A.F.hom)) he
    have h2 := congrArg (fun t => t ≫ pullback.snd (jM M A ≫ A.F.hom) (jM M A ≫ A.F.hom)) he
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      LM_fst, LM_snd] at h1 h2
    exact h1.symm.trans h2
  · intro heq
    have hL : h ≫ LM M A a = (h ≫ fa M A a) ≫ pullback.diagonal (jM M A ≫ A.F.hom) := by
      apply pullback.hom_ext
      · rw [Category.assoc, LM_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, LM_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact heq.symm
    rintro _ ⟨y, rfl⟩
    show ⇑(LM M A a) (h y) ∈ Set.range ⇑(pullback.diagonal (jM M A ≫ A.F.hom))
    refine ⟨fa M A a (h y), ?_⟩
    have hy := congrArg
      (fun t : Y ⟶ pullback (jM M A ≫ A.F.hom) (jM M A ≫ A.F.hom) => t y) hL
    simp only [Scheme.Hom.comp_apply] at hy
    exact hy.symm

theorem comp_fa_eq_iff {Y : Scheme.{0}} (h : Y ⟶ WM M A) (a : O) :
    h ≫ fa M A a = h ≫ zM M A ↔
      (h ≫ jM M A) ≫ A.iota a = ((h ≫ jM M A) ≫ A.F.hom) ≫ torsZeroL A := by
  have e1 : (h ≫ fa M A a) ≫ jM M A = (h ≫ jM M A) ≫ A.iota a := by
    simp only [Category.assoc, fa_spec]
  have e2 : (h ≫ zM M A) ≫ jM M A = ((h ≫ jM M A) ≫ A.F.hom) ≫ torsZeroL A := by
    simp only [Category.assoc, zM_spec]
  refine (cancel_mono (jM M A)).symm.trans ?_
  rw [e1, e2]

theorem geom_cond_iff {T Y : Scheme.{0}} (g : T ⟶ WM M A) (P : T ⟶ A.F.left)
    (hP : g ≫ jM M A = P) (s : Y ⟶ T) (a : O) :
    (s ≫ g) ≫ fa M A a = (s ≫ g) ≫ zM M A ↔
      (s ≫ P) ≫ A.iota a = (s ≫ P ≫ A.F.hom) ≫ torsZeroL A := by
  subst hP
  refine (comp_fa_eq_iff M A (s ≫ g) a).trans ?_
  simp only [Category.assoc]

theorem mem_KM_iff (het : AlgebraicGeometry.Etale (A.iota (M : O)))
    {Y : Scheme.{0}} (g : Y ⟶ WM M A) (y : Y) (a : O) :
    g y ∈ KM M A a ↔ (geomPt y ≫ g) ≫ fa M A a = (geomPt y ≫ g) ≫ zM M A := by
  refine Iff.trans ?_ (range_sub_KM_iff M A het (geomPt y ≫ g) a)
  constructor
  · rintro hy _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, geomPt_apply]
    exact hy
  · intro hr
    obtain ⟨q⟩ := spec_field_nonempty (geomK y)
    have hq := hr ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, geomPt_apply] at hq
    exact hq

/-! ## 3. The clopen subscheme `Z` -/

/-- A representative in `O` of a class modulo `M`. -/
def repO (q : Y3OrderMod.OMod M) : O := Classical.choose (Y3OrderMod.coe_surjective M q)

theorem repO_spec (q : Y3OrderMod.OMod M) : ((repO M q : O) : Y3OrderMod.OMod M) = q :=
  Classical.choose_spec (Y3OrderMod.coe_surjective M q)

theorem fa_congr {a b : O} (hab : (a : Y3OrderMod.OMod M) = (b : Y3OrderMod.OMod M)) :
    fa M A a = fa M A b :=
  (cancel_mono (jM M A)).1 ((fa_spec M A a).trans
    ((iota_congr_of_tors M A (jM M A) (torsM_j M A) hab).trans (fa_spec M A b).symm))

theorem KM_congr {a b : O} (hab : (a : Y3OrderMod.OMod M) = (b : Y3OrderMod.OMod M)) :
    KM M A a = KM M A b := by
  have hL : LM M A a = LM M A b :=
    pullback.hom_ext ((LM_fst M A a).trans ((fa_congr M A hab).trans (LM_fst M A b).symm))
      ((LM_snd M A a).trans (LM_snd M A b).symm)
  unfold KM
  rw [hL]

/-- The union of the `K a` over `a ∉ MO`, indexed by the nonzero classes modulo `M`. -/
def BadM : Set ↥(WM M A) := ⋃ q : {q : Y3OrderMod.OMod M // q ≠ 0}, KM M A (repO M q.1)

theorem mem_BadM_iff (w : ↥(WM M A)) :
    w ∈ BadM M A ↔ ∃ a : O, ¬ (∃ b : O, a = (M : O) * b) ∧ w ∈ KM M A a := by
  constructor
  · intro hw
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hw
    exact ⟨repO M q.1,
      fun h => q.2 ((repO_spec M q.1).symm.trans ((memM_iff M (repO M q.1)).1 h)), hq⟩
  · rintro ⟨a, ha, hw⟩
    have hq : (a : Y3OrderMod.OMod M) ≠ 0 := fun h => ha ((memM_iff M a).2 h)
    refine Set.mem_iUnion.2 ⟨⟨(a : Y3OrderMod.OMod M), hq⟩, ?_⟩
    have e := KM_congr M A (repO_spec M (a : Y3OrderMod.OMod M))
    exact (congrArg (fun s => w ∈ s) e).mpr hw

/-- `Bad` is closed: a finite union of closed sets, since `O/MO` is finite for `M ≠ 0`. -/
theorem isClosed_BadM [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O))) :
    IsClosed (BadM M A) := by
  have : Finite (Y3OrderMod.OMod M) := Y3OrderMod.instFiniteOMod M
  exact isClosed_iUnion_of_finite (fun q => isClosed_KM M A hfin _)

theorem isOpen_BadM (het : AlgebraicGeometry.Etale (A.iota (M : O))) :
    IsOpen (BadM M A) :=
  isOpen_iUnion (fun _ => isOpen_KM M A het _)

/-- `Z`, as an open subscheme of `W`. -/
def UM [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O))) : (WM M A).Opens :=
  ⟨(BadM M A)ᶜ, (isClosed_BadM M A hfin).isOpen_compl⟩

theorem UM_isClosedImmersion [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    (het : AlgebraicGeometry.Etale (A.iota (M : O))) :
    IsClosedImmersion (UM M A hfin).ι := by
  have : IsPreimmersion (UM M A hfin).ι := inferInstance
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (isOpen_BadM M A het).isClosed_compl

/-- The inclusion `Z ⟶ A`. -/
def iM [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O))) :
    ((UM M A hfin : (WM M A).Opens) : Scheme.{0}) ⟶ A.F.left :=
  (UM M A hfin).ι ≫ jM M A

theorem range_sub_UM_iff [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    {T : Scheme.{0}} (g : T ⟶ WM M A) :
    Set.range ⇑g ⊆ ((UM M A hfin : (WM M A).Opens) : Set ↥(WM M A)) ↔
      ∀ (t : T) (a : O), ¬ (∃ b : O, a = (M : O) * b) → g t ∉ KM M A a := by
  constructor
  · intro hr t a ha hK
    have h1 : g t ∈ (BadM M A)ᶜ := hr ⟨t, rfl⟩
    exact h1 ((mem_BadM_iff M A _).2 ⟨a, ha, hK⟩)
  · rintro hall _ ⟨t, rfl⟩
    show g t ∈ (BadM M A)ᶜ
    intro hy
    obtain ⟨a, ha, hK⟩ := (mem_BadM_iff M A _).1 hy
    exact hall t a ha hK

/-! ## 4. The pointwise characterization -/

/-- The generator hypothesis for one family. -/
def GeomFreeAtM : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    ∃ Q : Over.mk s ⟶ A.F, IsGenAt M A s Q

theorem isGen_of_lift [NeZero M] (het : AlgebraicGeometry.Etale (A.iota (M : O)))
    (hF : GeomFreeAtM M A) {T : Scheme.{0}} (g : T ⟶ WM M A) (P : T ⟶ A.F.left)
    (hP : g ≫ jM M A = P)
    (hall : ∀ (t : T) (a : O), ¬ (∃ b : O, a = (M : O) * b) → g t ∉ KM M A a) :
    IsGen M A P := by
  have htors : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl :
      Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1 := (torsChar A M T P).1 ⟨g, hP⟩
  have hPt : P ≫ A.iota (M : O) = (P ≫ A.F.hom) ≫ torsZeroL A :=
    (torsPow_eq_one_iff A P M).1 htors
  dsimp only [IsGen]
  refine ⟨htors, ?_⟩
  intro k _ _ s
  set Ps : Over.mk (s ≫ P ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (s ≫ P ≫ A.F.hom)) (s ≫ P) (Category.assoc _ _ _) with hPs
  have hsM : (s ≫ P) ≫ A.iota (M : O) = (s ≫ P ≫ A.F.hom) ≫ torsZeroL A := by
    simp only [Category.assoc, hPt]
  have hPsM' : Ps ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (comp_iota_eq_one_iff A Ps _).2 hsM
  have hPM : Ps ^ M = 1 := (comp_iotaHom_natCast A Ps M).symm.trans hPsM'
  have h1 : ∀ a : O, Ps ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      ∃ b : O, a = (M : O) * b := by
    intro a
    constructor
    · intro hone
      have heq : (s ≫ P) ≫ A.iota a = (s ≫ P ≫ A.F.hom) ≫ torsZeroL A :=
        (comp_iota_eq_one_iff A Ps a).1 hone
      by_contra ha
      have hcond : (s ≫ g) ≫ fa M A a = (s ≫ g) ≫ zM M A :=
        (geom_cond_iff M A g P hP s a).2 heq
      have hr := (range_sub_KM_iff M A het (s ≫ g) a).2 hcond
      obtain ⟨q⟩ := spec_field_nonempty k
      have hq : (s ≫ g) q ∈ KM M A a := hr ⟨q, rfl⟩
      rw [Scheme.Hom.comp_apply] at hq
      exact hall (s q) a ha hq
    · rintro ⟨b, rfl⟩
      exact comp_iota_natCast_mul_eq_one A M Ps hPsM' b
  obtain ⟨Q, hQ⟩ := hF k (s ≫ P ≫ A.F.hom)
  exact isGenAt_of_clause1 M A hQ hPM h1

theorem hall_of_isGen (het : AlgebraicGeometry.Etale (A.iota (M : O)))
    {T : Scheme.{0}} (g : T ⟶ WM M A) (P : T ⟶ A.F.left) (hP : g ≫ jM M A = P)
    (hG : IsGen M A P) :
    ∀ (t : T) (a : O), ¬ (∃ b : O, a = (M : O) * b) → g t ∉ KM M A a := by
  intro t a ha hK
  dsimp only [IsGen] at hG
  obtain ⟨-, h2⟩ := hG
  have hcond := (mem_KM_iff M A het g t a).1 hK
  have heq := (geom_cond_iff M A g P hP (geomPt t) a).1 hcond
  have hone := (comp_iota_eq_one_iff A
    (Over.homMk (U := Over.mk (geomPt t ≫ P ≫ A.F.hom)) (geomPt t ≫ P)
      (Category.assoc _ _ _)) a).2 heq
  exact ha (((h2 (geomK t) (geomPt t)).1 a).1 hone)

theorem charM [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    (het : AlgebraicGeometry.Etale (A.iota (M : O))) (hF : GeomFreeAtM M A)
    (T : Scheme.{0}) (P : T ⟶ A.F.left) :
    (∃ f : T ⟶ ((UM M A hfin : (WM M A).Opens) : Scheme.{0}), f ≫ iM M A hfin = P) ↔
      IsGen M A P := by
  constructor
  · rintro ⟨f, rfl⟩
    have hg : (f ≫ (UM M A hfin).ι) ≫ jM M A = f ≫ iM M A hfin := Category.assoc _ _ _
    have hrange : Set.range ⇑(f ≫ (UM M A hfin).ι) ⊆
        ((UM M A hfin : (WM M A).Opens) : Set ↥(WM M A)) := by
      rintro _ ⟨y, rfl⟩
      have hm : (UM M A hfin).ι (f y) ∈ Set.range ⇑(UM M A hfin).ι := ⟨f y, rfl⟩
      rw [Scheme.Opens.range_ι] at hm
      rw [Scheme.Hom.comp_apply]
      exact hm
    exact isGen_of_lift M A het hF (f ≫ (UM M A hfin).ι) _ hg
      ((range_sub_UM_iff M A hfin _).1 hrange)
  · intro hG
    have htors : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl :
        Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1 := by
      dsimp only [IsGen] at hG
      exact hG.1
    obtain ⟨g, hg⟩ := (torsChar A M T P).2 htors
    have hr : Set.range ⇑g ⊆ ((UM M A hfin : (WM M A).Opens) : Set ↥(WM M A)) :=
      (range_sub_UM_iff M A hfin g).2 (hall_of_isGen M A het g P hg hG)
    have : IsOpenImmersion (UM M A hfin).ι := inferInstance
    have hr' : Set.range ⇑g ⊆ Set.range ⇑(UM M A hfin).ι := by
      rw [Scheme.Opens.range_ι]
      exact hr
    refine ⟨IsOpenImmersion.lift (UM M A hfin).ι g hr', ?_⟩
    show IsOpenImmersion.lift (UM M A hfin).ι g hr' ≫ (UM M A hfin).ι ≫ jM M A = P
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact hg

/-! ## 5. Surjectivity -/

theorem surjM [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    (het : AlgebraicGeometry.Etale (A.iota (M : O))) (hF : GeomFreeAtM M A) :
    Function.Surjective ⇑(iM M A hfin ≫ A.F.hom) := by
  intro x
  obtain ⟨Q, hQ⟩ := hF (geomK x) (geomPt x)
  have hQ' := hQ
  obtain ⟨hQ1, -⟩ := hQ'
  have hQM : Q ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (hQ1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  have hw : Q.left ≫ A.F.hom = geomPt x := Over.w Q
  -- `Q.left` is `M`-torsion
  have hQt : Q.left ≫ A.iota (M : O) = (Q.left ≫ A.F.hom) ≫ torsZeroL A :=
    ((comp_iota_eq_one_iff A Q _).1 hQM).trans
      (congrArg (fun t => t ≫ torsZeroL A) hw.symm)
  obtain ⟨g, hg⟩ := (torsChar A M _ Q.left).2 ((torsPow_eq_one_iff A Q.left M).2 hQt)
  have hall : ∀ (t : ↥(Spec (CommRingCat.of (geomK x)))) (a : O),
      ¬ (∃ b : O, a = (M : O) * b) → g t ∉ KM M A a := by
    intro t a ha hK
    apply ha
    have hr : Set.range ⇑g ⊆ KM M A a := by
      rintro _ ⟨t', rfl⟩
      have htt : t' = t := by
        have key : ∀ q : PrimeSpectrum (geomK x), q.asIdeal = ⊥ := fun q =>
          (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
        exact PrimeSpectrum.ext ((key t').trans (key t).symm)
      rw [htt]
      exact hK
    have hcond := (range_sub_KM_iff M A het g a).1 hr
    have heq := (geom_cond_iff M A g Q.left hg (𝟙 _) a).1
      (by simpa only [Category.id_comp] using hcond)
    have heq' : Q.left ≫ A.iota a = (Over.mk (geomPt x)).hom ≫ torsZeroL A := by
      have e := heq
      simp only [Category.id_comp] at e
      exact e.trans (congrArg (fun t => t ≫ torsZeroL A) hw)
    exact (hQ1 a).1 ((comp_iota_eq_one_iff A Q a).2 heq')
  have hr : Set.range ⇑g ⊆ Set.range ⇑(UM M A hfin).ι := by
    rw [Scheme.Opens.range_ι]
    exact (range_sub_UM_iff M A hfin g).2 hall
  have : IsOpenImmersion (UM M A hfin).ι := inferInstance
  obtain ⟨q⟩ := spec_field_nonempty (geomK x)
  refine ⟨IsOpenImmersion.lift (UM M A hfin).ι g hr q, ?_⟩
  have hfac : IsOpenImmersion.lift (UM M A hfin).ι g hr ≫ iM M A hfin ≫ A.F.hom =
      geomPt x := by
    show IsOpenImmersion.lift (UM M A hfin).ι g hr ≫ ((UM M A hfin).ι ≫ jM M A) ≫ A.F.hom =
      geomPt x
    rw [← Category.assoc, ← Category.assoc, IsOpenImmersion.lift_fac, hg]
    exact hw
  have := congrArg (fun t : Spec (CommRingCat.of (geomK x)) ⟶ S => t q) hfac
  simp only [Scheme.Hom.comp_apply] at this
  rw [Scheme.Hom.comp_apply]
  exact this.trans (geomPt_apply x q)

/-! ## 6. Properties of `i` -/

theorem iM_isClosedImmersion [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    (het : AlgebraicGeometry.Etale (A.iota (M : O))) : IsClosedImmersion (iM M A hfin) := by
  have := UM_isClosedImmersion M A hfin het
  have := torsFst_isClosedImmersion A M
  unfold iM
  infer_instance

theorem iM_isFinite [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    (het : AlgebraicGeometry.Etale (A.iota (M : O))) :
    AlgebraicGeometry.IsFinite (iM M A hfin ≫ A.F.hom) := by
  have := UM_isClosedImmersion M A hfin het
  have h1 : AlgebraicGeometry.IsFinite (UM M A hfin).ι := inferInstance
  have h2 : AlgebraicGeometry.IsFinite (jM M A ≫ A.F.hom) := torsFst_hom_isFinite A M hfin
  show AlgebraicGeometry.IsFinite (((UM M A hfin).ι ≫ jM M A) ≫ A.F.hom)
  rw [Category.assoc]
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.IsFinite) _ _ h1 h2

theorem iM_etale [NeZero M] (hfin : AlgebraicGeometry.IsFinite (A.iota (M : O)))
    (het : AlgebraicGeometry.Etale (A.iota (M : O))) :
    AlgebraicGeometry.Etale (iM M A hfin ≫ A.F.hom) := by
  have : AlgebraicGeometry.Etale (UM M A hfin).ι := inferInstance
  have : AlgebraicGeometry.Etale (jM M A ≫ A.F.hom) := torsFst_hom_etale A M het
  show AlgebraicGeometry.Etale (((UM M A hfin).ι ≫ jM M A) ≫ A.F.hom)
  rw [Category.assoc]
  infer_instance

end Geom

/-! ## 7. The theorem -/

/-- Frame representability at level `M ≠ 0` from Milne, Prop. 20.7 at `M` and the existence
of generators of the `M`-torsion at geometric points. -/
theorem frameRepM_of (M : ℕ) [NeZero M] (hM : MilneProp207 M) (hF : GeomFreeM M) :
    BuzzardFrameRep M := by
  intro S A
  have hfin := (hM S A).1
  have het := (hM S A).2
  have hFA : GeomFreeAtM M A := fun k _ _ s => hF S A k s
  refine ⟨_, iM M A hfin, iM_isClosedImmersion M A hfin het, iM_isFinite M A hfin het,
    iM_etale M A hfin het, ⟨surjM M A hfin het hFA⟩, fun T P => charM M A hfin het hFA T P⟩

/-- The level-three case, as a check: `GeomFree3` is `GeomFreeM 3`. -/
theorem frameRepM_three (hM : MilneProp207 3) (hF : GeomFree3) : BuzzardFrameRep 3 :=
  frameRepM_of 3 hM hF

end LevelM

end Y3Buzzard
