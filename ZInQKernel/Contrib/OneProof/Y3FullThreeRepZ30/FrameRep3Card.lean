import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameModuli
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Frame representability at level three from the torsion count (draft)

From `MilneProp207 3` (multiplication by 3 is finite and etale), `GeomCard3` (the 3-torsion of
every geometric fibre has exactly 81 points) and `Nat.card (O / 3O) = 81`, we prove
`BuzzardFrameRepNS 3`: frame representability without the torsor clause and without
surjectivity.

The subscheme `Z`, its inclusion `i3` and the properties of `i3` are reused unchanged. Only the
pointwise characterization changes: the second clause of `IsGenAt 3` is derived from the first
by counting. If `P` is 3-torsion and `ι(a) P = 0` exactly when `a ∈ 3O`, then `q ↦ ι(q) P` is an
injective map from `O / 3O` to the 3-torsion points over the same geometric point. Both sides
have 81 elements, so the map is bijective, which is the second clause.
-/

attribute [local instance] FEC.grp

/-- At every geometric point, the 3-torsion of a false elliptic curve has exactly 81 points.
Source: J. S. Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic
Geometry*, Springer (1986), Remark 8.4, p. 14 of the author's retyped edition, with subscripts
and exponents transcribed: "If k is separably algebraically closed and n is not divisible by its
characteristic, then the theorem says that the kernel A_n(k) of n : A(k) → A(k) has n^{2g}
elements. As this is also true for all n′ dividing n, it follows that A_n(k) is a free
Z/nZ-module of rank 2g." The same statement is Remark 7.3, p. 34, of Milne's course notes v2.0
(2008). A geometric fibre of a false elliptic curve is an abelian variety of dimension `g = 2`
(ibid. (1986), Section 20, p. 42), and no residue characteristic of a `Z[1/30]`-scheme is 3, so
the count is `3^4 = 81`. -/
def GeomCard3 : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left) (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ S.left),
    letI := A.grp
    Nat.card {x : Over.mk s ⟶ A.F // x ^ 3 = 1} = 81

section Card

variable {S : Scheme.{0}} (A : FEC S)

/-- If `ι(a) x = ι(b) x` then `ι(a - b) x = 0`. -/
theorem iotaSub_eq_one_card {U : Over S} (x : U ⟶ A.F) {a b : O}
    (h : x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F)) :
    x ≫ (Over.homMk (A.iota (a - b)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
  have hb0 : b + -b = 0 := by
    first
      | exact add_neg_cancel b
      | exact add_right_neg b
      | simp
  have e0 : x ≫ (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F) = 1 := by
    rw [iotaHom_zero]
    first
      | exact MonObj.comp_one x
      | exact MonObj.comp_one _
      | simp only [MonObj.comp_one]
  have e1 : x ≫ (Over.homMk (A.iota (a - b)) (A.iota_over _) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) *
        x ≫ (Over.homMk (A.iota (-b)) (A.iota_over _) : A.F ⟶ A.F) :=
    (congrArg (fun c : O => x ≫ (Over.homMk (A.iota c) (A.iota_over c) : A.F ⟶ A.F))
      (sub_eq_add_neg a b)).trans (comp_iota_add A x a (-b))
  have e2 : x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F) *
        x ≫ (Over.homMk (A.iota (-b)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (comp_iota_add A x b (-b)).symm.trans
      ((congrArg (fun c : O => x ≫ (Over.homMk (A.iota c) (A.iota_over c) : A.F ⟶ A.F))
        hb0).trans e0)
  exact e1.trans ((congrArg (fun t : U ⟶ A.F =>
    t * x ≫ (Over.homMk (A.iota (-b)) (A.iota_over _) : A.F ⟶ A.F)) h).trans e2)

/-- The orbit map `O / 3O → A[3]`, `q ↦ ι(q) P`, through a chosen representative. -/
def orbitMap3 {U : Over S} (P : U ⟶ A.F) (hP3 : P ^ 3 = 1) (q : Y3OrderMod.OMod 3) :
    {x : U ⟶ A.F // x ^ 3 = 1} :=
  ⟨P ≫ (Over.homMk (A.iota (repO q)) (A.iota_over _) : A.F ⟶ A.F),
    torsion_comp_iota A 3 P hP3 (repO q)⟩

theorem orbitMap3_val {U : Over S} (P : U ⟶ A.F) (hP3 : P ^ 3 = 1) (q : Y3OrderMod.OMod 3) :
    (orbitMap3 A P hP3 q).1 =
      P ≫ (Over.homMk (A.iota (repO q)) (A.iota_over _) : A.F ⟶ A.F) :=
  rfl

/-- The orbit map is injective when `ι(a) P = 0` forces `a ∈ 3O`. -/
theorem orbitMap3_injective {U : Over S} (P : U ⟶ A.F) (hP3 : P ^ 3 = 1)
    (h1 : ∀ a : O, P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 →
      ∃ b : O, a = ((3 : ℕ) : O) * b) :
    Function.Injective (orbitMap3 A P hP3) := by
  intro q1 q2 h
  have e : P ≫ (Over.homMk (A.iota (repO q1)) (A.iota_over _) : A.F ⟶ A.F) =
      P ≫ (Over.homMk (A.iota (repO q2)) (A.iota_over _) : A.F ⟶ A.F) :=
    (orbitMap3_val A P hP3 q1).symm.trans
      ((congrArg Subtype.val h).trans (orbitMap3_val A P hP3 q2))
  obtain ⟨c, hc⟩ := h1 _ (iotaSub_eq_one_card A P e)
  have hq : ((repO q1 : O) : Y3OrderMod.OMod 3) = ((repO q2 : O) : Y3OrderMod.OMod 3) :=
    Y3OrderMod.coe_eq_coe_iff.2 ⟨c, hc⟩
  exact (repO_spec q1).symm.trans (hq.trans (repO_spec q2))

/-- The second clause of `IsGenAt 3` from the first, by counting: the orbit map is an injection
between two sets with 81 elements. -/
theorem isGenAt_of_clause1_card (hcard : Nat.card (Y3OrderMod.OMod 3) = 81) {k : Type}
    [Field k] {s : Spec (CommRingCat.of k) ⟶ S} {P : Over.mk s ⟶ A.F}
    (hT : Nat.card {x : Over.mk s ⟶ A.F // x ^ 3 = 1} = 81) (hP3 : P ^ 3 = 1)
    (h1 : ∀ a : O, P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      ∃ b : O, a = ((3 : ℕ) : O) * b) : IsGenAt 3 A s P := by
  refine ⟨h1, fun x hx => ?_⟩
  haveI : Finite {x : Over.mk s ⟶ A.F // x ^ 3 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  haveI : Finite (Y3OrderMod.OMod 3) := Y3OrderMod.finite_OMod 3 (by norm_num)
  have hinj : Function.Injective (orbitMap3 A P hP3) :=
    orbitMap3_injective A P hP3 (fun a => (h1 a).1)
  have hle : Nat.card {x : Over.mk s ⟶ A.F // x ^ 3 = 1} ≤ Nat.card (Y3OrderMod.OMod 3) :=
    le_of_eq (hT.trans hcard.symm)
  have heq : Nat.card (Y3OrderMod.OMod 3) = Nat.card {x : Over.mk s ⟶ A.F // x ^ 3 = 1} :=
    hcard.trans hT.symm
  have hbij : Function.Bijective (orbitMap3 A P hP3) := by
    first
      | exact hinj.bijective_of_nat_card_le hle
      | exact Function.Injective.bijective_of_nat_card_le hinj hle
      | exact (Nat.bijective_iff_injective_and_card (orbitMap3 A P hP3)).2 ⟨hinj, heq⟩
      | (letI := Fintype.ofFinite (Y3OrderMod.OMod 3)
         letI := Fintype.ofFinite {x : Over.mk s ⟶ A.F // x ^ 3 = 1}
         exact (Fintype.bijective_iff_injective_and_card (orbitMap3 A P hP3)).2
           ⟨hinj, Nat.card_eq_fintype_card.symm.trans (heq.trans Nat.card_eq_fintype_card)⟩)
  obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨repO q, (congrArg Subtype.val hq).symm.trans (orbitMap3_val A P hP3 q)⟩

/-- The counting hypothesis for one family. -/
def GeomCard3At : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    Nat.card {x : Over.mk s ⟶ A.F // x ^ 3 = 1} = 81

theorem isGen_of_lift_card (hcard : Nat.card (Y3OrderMod.OMod 3) = 81)
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O)))
    (hC : GeomCard3At A) {T : Scheme.{0}} (g : T ⟶ W3 A) (P : T ⟶ A.F.left)
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
  exact isGenAt_of_clause1_card A hcard (hC k (s ≫ P ≫ A.F.hom)) hP3 h1

theorem char3_card (hcard : Nat.card (Y3OrderMod.OMod 3) = 81)
    (hfin : AlgebraicGeometry.IsFinite (A.iota ((3 : ℕ) : O)))
    (het : AlgebraicGeometry.Etale (A.iota ((3 : ℕ) : O))) (hC : GeomCard3At A)
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
    exact isGen_of_lift_card A hcard het hC (f ≫ (U3 A hfin).ι) _ hg
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

end Card

/-! ## The theorem -/

theorem frameRepNS3_of (hM : MilneProp207 3) (hC : GeomCard3)
    (hcard : Nat.card (Y3OrderMod.OMod 3) = 81) : BuzzardFrameRepNS 3 := by
  intro S A
  have hfin := (hM S A).1
  have het := (hM S A).2
  have hCA : GeomCard3At A := fun k _ _ s => hC S A k s
  exact ⟨_, i3 A hfin, i3_isClosedImmersion A hfin het, i3_isFinite A hfin het,
    i3_etale A hfin het, fun T P => char3_card A hcard hfin het hCA T P⟩

end Y3Buzzard
