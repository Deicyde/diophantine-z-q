import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Fibre transfer for generators of full level structures (draft)

Algebra of the `O`-action on hom-monoids, transport of `IsGenAt` and `IsGen` along an
`O`-compatible cartesian square, invariance of `IsGen` under units mod `M`, and the
construction of a `V15` structure from a section generating the 5-torsion.
-/

attribute [local instance] FEC.grp

/-! ## 1. The action on hom-monoids -/

section Iota

variable {S : Scheme.{0}} (A : FEC S)

theorem iotaHom_one :
    (Over.homMk (A.iota 1) (A.iota_over 1) : A.F ⟶ A.F) = 𝟙 A.F :=
  Over.OverMorphism.ext (by show A.iota 1 = 𝟙 A.F.left; exact A.iota_one)

theorem iotaHom_mul (a b : O) :
    (Over.homMk (A.iota (a * b)) (A.iota_over _) : A.F ⟶ A.F) =
      Over.homMk (A.iota b) (A.iota_over b) ≫ Over.homMk (A.iota a) (A.iota_over a) :=
  Over.OverMorphism.ext (by show A.iota (a * b) = A.iota b ≫ A.iota a; exact A.iota_mul a b)

theorem iotaHom_zero : (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F) = 1 := by
  letI : Group (A.F ⟶ A.F) := Hom.group
  have h := A.iota_add 0 0
  rw [show (0 : O) + 0 = 0 from add_zero 0] at h
  exact mul_left_cancel (a := (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F))
    (h.symm.trans (_root_.mul_one _).symm)

theorem iotaHom_natCast (n : ℕ) :
    (Over.homMk (A.iota (n : O)) (A.iota_over _) : A.F ⟶ A.F) = (𝟙 A.F) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero]; exact iotaHom_zero A
  | succ n ih => rw [Nat.cast_succ, A.iota_add, ih, iotaHom_one, pow_succ]

theorem comp_iotaHom_natCast {U : Over S} (x : U ⟶ A.F) (n : ℕ) :
    x ≫ (Over.homMk (A.iota (n : O)) (A.iota_over _) : A.F ⟶ A.F) = x ^ n := by
  rw [iotaHom_natCast, MonObj.comp_pow, Category.comp_id]

theorem one_comp_isMonHom {U V W : Over S} [MonObj V] [MonObj W] (f : V ⟶ W) [IsMonHom f] :
    (1 : U ⟶ V) ≫ f = 1 :=
  MonObj.one_comp f

theorem pow_comp_isMonHom {U V W : Over S} [MonObj V] [MonObj W] (f : V ⟶ W) [IsMonHom f]
    (u : U ⟶ V) (n : ℕ) : (u ^ n) ≫ f = (u ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact MonObj.one_comp f
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem one_comp_iotaHom {U : Over S} (a : O) :
    (1 : U ⟶ A.F) ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 := by
  haveI := A.iota_hom a
  exact MonObj.one_comp _

theorem comp_iota_comp_iota {U : Over S} (x : U ⟶ A.F) (a b : O) :
    (x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F)) ≫
        (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota (b * a)) (A.iota_over _) : A.F ⟶ A.F) := by
  rw [Category.assoc, iotaHom_mul]

theorem comp_iota_add {U : Over S} (x : U ⟶ A.F) (a b : O) :
    x ≫ (Over.homMk (A.iota (a + b)) (A.iota_over _) : A.F ⟶ A.F) =
      x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) *
        x ≫ (Over.homMk (A.iota b) (A.iota_over b) : A.F ⟶ A.F) := by
  rw [A.iota_add, MonObj.comp_mul]

/-- If `x ≫ ι(M) = 1` then `x ≫ ι(M * e) = 1`. -/
theorem comp_iota_natCast_mul_eq_one (M : ℕ) {U : Over S} (x : U ⟶ A.F)
    (hx : x ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1) (e : O) :
    x ≫ (Over.homMk (A.iota ((M : O) * e)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
  rw [Nat.cast_comm, iotaHom_mul, ← Category.assoc, hx]
  exact one_comp_iotaHom A e

/-- `M`-torsion is preserved by the action. -/
theorem torsion_comp_iota (M : ℕ) {U : Over S} (x : U ⟶ A.F) (hx : x ^ M = 1) (a : O) :
    (x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F)) ^ M = 1 := by
  rw [← comp_iotaHom_natCast A (x ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F)) M,
    comp_iota_comp_iota, Nat.cast_comm, iotaHom_mul, ← Category.assoc,
    comp_iotaHom_natCast A x M, hx]
  exact one_comp_iotaHom A a

theorem homMk_mk_comp_iota {T : Scheme.{0}} (u : T ⟶ S) (Q : T ⟶ A.F.left)
    (hQ : Q ≫ A.F.hom = u) (a : O) (hQa : (Q ≫ A.iota a) ≫ A.F.hom = u) :
    (Over.homMk (U := Over.mk u) (Q ≫ A.iota a) hQa : Over.mk u ⟶ A.F) =
      Over.homMk (U := Over.mk u) Q hQ ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) :=
  Over.OverMorphism.ext rfl

/-- Transport of torsion between `Over.mk u₁` and `Over.mk u₂` when `u₁ = u₂`. -/
theorem homMk_pow_eq_one_congr {T : Scheme.{0}} {u₁ u₂ : T ⟶ S} (e : u₁ = u₂)
    (Q : T ⟶ A.F.left) (h₁ : Q ≫ A.F.hom = u₁) (h₂ : Q ≫ A.F.hom = u₂) (n : ℕ) :
    (Over.homMk (U := Over.mk u₁) Q h₁ : Over.mk u₁ ⟶ A.F) ^ n = 1 ↔
      (Over.homMk (U := Over.mk u₂) Q h₂ : Over.mk u₂ ⟶ A.F) ^ n = 1 := by
  subst e
  exact Iff.rfl

/-- Transport of `IsGenAt` between `Over.mk t₁` and `Over.mk t₂` when `t₁ = t₂`. -/
theorem isGenAt_congr {M : ℕ} {k : Type} [Field k] {t₁ t₂ : Spec (CommRingCat.of k) ⟶ S}
    (e : t₁ = t₂) (Q : Spec (CommRingCat.of k) ⟶ A.F.left) (h₁ : Q ≫ A.F.hom = t₁)
    (h₂ : Q ≫ A.F.hom = t₂) :
    IsGenAt M A t₁ (Over.homMk (U := Over.mk t₁) Q h₁) ↔
      IsGenAt M A t₂ (Over.homMk (U := Over.mk t₂) Q h₂) := by
  subst e
  exact Iff.rfl

end Iota

theorem IsGenAt.of_eq {M : ℕ} {S : Scheme.{0}} {A : FEC S} {k : Type} [Field k]
    {s : Spec (CommRingCat.of k) ⟶ S} {P Q : Over.mk s ⟶ A.F} (hPQ : P = Q)
    (hP : IsGenAt M A s P) : IsGenAt M A s Q :=
  hPQ ▸ hP

/-! ## 2. Transfer along an `O`-compatible cartesian square -/

section Fibre

variable {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
  {h : A'.F.left ⟶ A.F.left}

/-- Points of `A'` over `t'` give points of `A` over `t = t' ≫ g`. -/
def fibreMap (hpb : IsPullback h A'.F.hom A.F.hom g) {W : Scheme.{0}} {t' : W ⟶ S'}
    {t : W ⟶ S} (ht : t' ≫ g = t) (x' : Over.mk t' ⟶ A'.F) : Over.mk t ⟶ A.F :=
  Over.homMk (x'.left ≫ h) (by
    have h1 : x'.left ≫ A'.F.hom = t' := Over.w x'
    show (x'.left ≫ h) ≫ A.F.hom = t
    rw [Category.assoc, hpb.w, ← Category.assoc, h1, ht])

variable (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a)
include hpb

@[simp]
theorem fibreMap_left {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t)
    (x' : Over.mk t' ⟶ A'.F) : (fibreMap hpb ht x').left = x'.left ≫ h :=
  Over.homMk_left _ _

theorem fibreMap_injective {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t) :
    Function.Injective (fibreMap hpb ht) := by
  intro x y hxy
  apply Over.OverMorphism.ext
  apply hpb.hom_ext
  · simpa only [fibreMap_left] using congrArg (fun z => z.left) hxy
  · rw [Over.w x, Over.w y]

theorem fibreMap_surjective {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t) :
    Function.Surjective (fibreMap hpb ht) := by
  intro y
  have hy : y.left ≫ A.F.hom = t' ≫ g := by rw [ht]; exact Over.w y
  refine ⟨Over.homMk (hpb.lift y.left t' hy) (hpb.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact hpb.lift_fst y.left t' hy

theorem fibreMap_bijective {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t) :
    Function.Bijective (fibreMap hpb ht) :=
  ⟨fibreMap_injective hpb ht, fibreMap_surjective hpb ht⟩

include hι

theorem fibreMap_iota {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t)
    (x' : Over.mk t' ⟶ A'.F) (a : O) :
    fibreMap hpb ht x' ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) =
      fibreMap hpb ht (x' ≫ (Over.homMk (A'.iota a) (A'.iota_over a) : A'.F ⟶ A'.F)) :=
  Over.OverMorphism.ext (by
    show (x'.left ≫ h) ≫ A.iota a = (x'.left ≫ A'.iota a) ≫ h
    rw [Category.assoc, Category.assoc, hι])

theorem fibreMap_one {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t) :
    fibreMap hpb ht (1 : Over.mk t' ⟶ A'.F) = 1 := by
  have h0 := fibreMap_iota hpb hι ht 1 0
  simp only [iotaHom_zero, MonObj.comp_one] at h0
  exact h0.symm

theorem fibreMap_pow {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t)
    (x' : Over.mk t' ⟶ A'.F) (n : ℕ) :
    fibreMap hpb ht (x' ^ n) = (fibreMap hpb ht x') ^ n := by
  rw [← comp_iotaHom_natCast A' x' n, ← comp_iotaHom_natCast A (fibreMap hpb ht x') n,
    fibreMap_iota hpb hι]

theorem fibreMap_eq_one_iff {W : Scheme.{0}} {t' : W ⟶ S'} {t : W ⟶ S} (ht : t' ≫ g = t)
    (x' : Over.mk t' ⟶ A'.F) : fibreMap hpb ht x' = 1 ↔ x' = 1 := by
  rw [← fibreMap_one hpb hι ht]
  exact (fibreMap_injective hpb ht).eq_iff

theorem isGenAt_of_fibre {M : ℕ} {k : Type} [Field k] {t' : Spec (CommRingCat.of k) ⟶ S'}
    {t : Spec (CommRingCat.of k) ⟶ S} (ht : t' ≫ g = t) {P' : Over.mk t' ⟶ A'.F}
    (hP : IsGenAt M A' t' P') : IsGenAt M A t (fibreMap hpb ht P') := by
  dsimp only [IsGenAt] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun a => ?_, fun x hx => ?_⟩
  · rw [fibreMap_iota hpb hι, fibreMap_eq_one_iff hpb hι]
    exact h1 a
  · obtain ⟨x', rfl⟩ := fibreMap_surjective hpb ht x
    rw [← fibreMap_pow hpb hι, fibreMap_eq_one_iff hpb hι] at hx
    obtain ⟨a, rfl⟩ := h2 x' hx
    exact ⟨a, (fibreMap_iota hpb hι ht P' a).symm⟩

theorem isGen_of_fibre {M : ℕ} {T : Scheme.{0}} {P' : T ⟶ A'.F.left} (hP : IsGen M A' P') :
    IsGen M A (P' ≫ h) := by
  dsimp only [IsGen] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  have ht : (P' ≫ A'.F.hom) ≫ g = (P' ≫ h) ≫ A.F.hom := by
    simp only [Category.assoc, hpb.w]
  refine ⟨?_, ?_⟩
  · have e : (Over.homMk (U := Over.mk ((P' ≫ h) ≫ A.F.hom)) (P' ≫ h) rfl :
          Over.mk ((P' ≫ h) ≫ A.F.hom) ⟶ A.F) =
        fibreMap hpb ht (Over.homMk (U := Over.mk (P' ≫ A'.F.hom)) P' rfl) :=
      Over.OverMorphism.ext rfl
    rw [e, ← fibreMap_pow hpb hι, h1, fibreMap_one hpb hι]
  · intro k _ _ s
    have ht' : (s ≫ P' ≫ A'.F.hom) ≫ g = s ≫ (P' ≫ h) ≫ A.F.hom := by
      simp only [Category.assoc, hpb.w]
    refine IsGenAt.of_eq ?_ (isGenAt_of_fibre hpb hι ht' (h2 k s))
    exact Over.OverMorphism.ext (Category.assoc s P' h)

end Fibre

/-! ## 3. Invariance under units modulo `M` -/

theorem isGenAt_comp_iota {M : ℕ} {S : Scheme.{0}} {A : FEC S} {k : Type} [Field k]
    {s : Spec (CommRingCat.of k) ⟶ S} {q : Over.mk s ⟶ A.F} (hq : IsGenAt M A s q)
    {u u' d d' : O} (hd : u' * u - 1 = (M : O) * d) (hd' : u * u' - 1 = (M : O) * d') :
    IsGenAt M A s (q ≫ (Over.homMk (A.iota u) (A.iota_over u) : A.F ⟶ A.F)) := by
  dsimp only [IsGenAt] at hq ⊢
  obtain ⟨h1, h2⟩ := hq
  have hqM : q ≫ (Over.homMk (A.iota (M : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 :=
    (h1 _).2 ⟨1, (_root_.mul_one _).symm⟩
  refine ⟨fun a => ?_, fun x hx => ?_⟩
  · rw [comp_iota_comp_iota, h1]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b * u' - a * d', ?_⟩
      calc a = a * (u * u') - a * (u * u' - 1) := by rw [mul_sub, _root_.mul_one, sub_sub_cancel]
        _ = a * u * u' - a * ((M : O) * d') := by rw [hd']; simp only [_root_.mul_assoc]
        _ = (M : O) * b * u' - (M : O) * (a * d') := by
            rw [hb, ← _root_.mul_assoc a (M : O) d', ← Nat.cast_comm M a, _root_.mul_assoc (M : O) a d']
        _ = (M : O) * (b * u' - a * d') := by rw [mul_sub]; simp only [_root_.mul_assoc]
    · rintro ⟨b, rfl⟩
      exact ⟨b * u, _root_.mul_assoc _ _ _⟩
  · obtain ⟨c, rfl⟩ := h2 x hx
    refine ⟨c * u', ?_⟩
    rw [comp_iota_comp_iota]
    have hc : c * u' * u = c + (M : O) * (c * d) := by
      calc c * u' * u = c * (u' * u - 1) + c := by
            rw [mul_sub, _root_.mul_one, sub_add_cancel, _root_.mul_assoc]
        _ = c * ((M : O) * d) + c := by rw [hd]
        _ = c + (M : O) * (c * d) := by
            rw [add_comm (c * ((M : O) * d)) c, ← _root_.mul_assoc c (M : O) d, ← Nat.cast_comm M c,
              _root_.mul_assoc (M : O) c d]
    rw [hc, comp_iota_add, comp_iota_natCast_mul_eq_one A M q hqM, _root_.mul_one]

theorem isGen_mul_unit {M : ℕ} {S : Scheme.{0}} {A : FEC S} {T : Scheme.{0}}
    {P : T ⟶ A.F.left} (hP : IsGen M A P) {u u' d d' : O}
    (hd : u' * u - 1 = (M : O) * d) (hd' : u * u' - 1 = (M : O) * d') :
    IsGen M A (P ≫ A.iota u) := by
  dsimp only [IsGen] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  have e : (P ≫ A.iota u) ≫ A.F.hom = P ≫ A.F.hom := by rw [Category.assoc, A.iota_over]
  refine ⟨(homMk_pow_eq_one_congr A e (P ≫ A.iota u) rfl e M).2 ?_, ?_⟩
  · rw [homMk_mk_comp_iota A (P ≫ A.F.hom) P rfl u e]
    exact torsion_comp_iota A M _ h1 u
  · intro k _ _ s
    have e' : s ≫ (P ≫ A.iota u) ≫ A.F.hom = s ≫ P ≫ A.F.hom := by rw [e]
    have h₂ : (s ≫ P ≫ A.iota u) ≫ A.F.hom = s ≫ P ≫ A.F.hom := by
      simp only [Category.assoc, A.iota_over]
    refine (isGenAt_congr A e' (s ≫ P ≫ A.iota u) (Category.assoc _ _ _) h₂).2 ?_
    refine IsGenAt.of_eq ?_ (isGenAt_comp_iota (h2 k s) hd hd')
    exact Over.OverMorphism.ext (Category.assoc s P (A.iota u))

/-! ## 4. From a generator of the 5-torsion to a `V₁(5)`-structure -/

/-- The element `-6 - 2k` of `O`, written `ofInt ![-6, 2, 0, -4]`. -/
def c5 : O :=
  ⟨ofInt ![-6, 2, 0, -4], show InO (ofInt ![-6, 2, 0, -4]) from ⟨![-6, 2, 0, -4], rfl⟩⟩

theorem e5_coe : ((e5 : O) : (QuaternionAlgebra ℚ 2 0 (-3))) = ⟨3, 0, 0, 2⟩ := by
  show ofInt ![3, -2, 0, 4] = _
  ext <;> norm_num [ofInt]

theorem c5_coe : ((c5 : O) : (QuaternionAlgebra ℚ 2 0 (-3))) = ⟨-6, 0, 0, -2⟩ := by
  show ofInt ![-6, 2, 0, -4] = _
  ext <;> norm_num [ofInt]

/-- The natural number `5` in the quaternion algebra, written as a record. -/
theorem natCast_five_eq : ((5 : ℕ) : (QuaternionAlgebra ℚ 2 0 (-3))) = ⟨5, 0, 0, 0⟩ := by
  ext
  · rw [QuaternionAlgebra.re_natCast]; norm_num
  · exact QuaternionAlgebra.imI_natCast 5
  · exact QuaternionAlgebra.imJ_natCast 5
  · exact QuaternionAlgebra.imK_natCast 5

/-- `(3 + 2k)(-2 - 2k) = -30 - 10k = 5 (-6 - 2k)`. -/
theorem e5_mul_one_sub : e5 * (1 - e5) = ((5 : ℕ) : O) * c5 := by
  apply Subtype.ext
  show (e5 : (QuaternionAlgebra ℚ 2 0 (-3))) * (1 - (e5 : (QuaternionAlgebra ℚ 2 0 (-3)))) =
    ((5 : ℕ) : (QuaternionAlgebra ℚ 2 0 (-3))) * (c5 : (QuaternionAlgebra ℚ 2 0 (-3)))
  rw [e5_coe, c5_coe, natCast_five_eq]
  ext <;> simp <;> norm_num

theorem e5_mul_one_sub' : e5 * (1 - e5) = 5 * c5 := by
  rw [e5_mul_one_sub, Nat.cast_ofNat]

/-- `1 - e5 = -2 - 2k` is not divisible by 5 in `O`: its `k`-coordinate is `-2`, while that
of `5 b` is `5 m₃ / 2` for integral coordinates `m`. -/
theorem one_sub_e5_not_mem : ¬ ∃ b : O, 1 - e5 = ((5 : ℕ) : O) * b := by
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ : InO (b : (QuaternionAlgebra ℚ 2 0 (-3))) := b.2
  have h := congrArg (fun z : O => (z : (QuaternionAlgebra ℚ 2 0 (-3))).imK) hb
  change ((1 : (QuaternionAlgebra ℚ 2 0 (-3))) - (e5 : (QuaternionAlgebra ℚ 2 0 (-3)))).imK =
    (((5 : ℕ) : (QuaternionAlgebra ℚ 2 0 (-3))) * (b : (QuaternionAlgebra ℚ 2 0 (-3)))).imK at h
  rw [e5_coe, hm, natCast_five_eq] at h
  simp [ofInt] at h
  have h' : (5 * (m 3 : ℚ)) = -4 := by linarith
  have h'' : 5 * m 3 = -4 := by exact_mod_cast h'
  omega

section V15

variable {S : Scheme.{0}} (A : FEC S)

/-- The isomorphism with identity underlying map from the unit of `Over S` to
`Over.mk (P ≫ A.F.hom)`, for a section `P`. -/
def unitIso (P : S ⟶ A.F.left) (hPs : P ≫ A.F.hom = 𝟙 S) :
    𝟙_ (Over S) ≅ Over.mk (P ≫ A.F.hom) :=
  Over.isoMk (Iso.refl S) (by
    show 𝟙 S ≫ P ≫ A.F.hom = 𝟙 S
    rw [Category.id_comp, hPs])

theorem unit_homMk_eq (P : S ⟶ A.F.left) (hPs : P ≫ A.F.hom = 𝟙 S) (Q : S ⟶ A.F.left)
    (hQ : Q ≫ A.F.hom = 𝟙 S) (hQ' : Q ≫ A.F.hom = P ≫ A.F.hom) :
    (Over.homMk (U := 𝟙_ (Over S)) Q hQ : 𝟙_ (Over S) ⟶ A.F) =
      (unitIso A P hPs).hom ≫
        (Over.homMk (U := Over.mk (P ≫ A.F.hom)) Q hQ' : Over.mk (P ≫ A.F.hom) ⟶ A.F) :=
  Over.OverMorphism.ext (Category.id_comp Q).symm

/-- A section generating the 5-torsion gives a `V₁(5)`-structure, with
`Q := P ≫ ι(1 - e5)`. -/
def v15_of_isGen5 (P : S ⟶ A.F.left) (hPs : P ≫ A.F.hom = 𝟙 S) (hP : IsGen 5 A P) :
    V15 A where
  Q := P ≫ A.iota (1 - e5)
  Q_sec := by rw [Category.assoc, A.iota_over, hPs]
  order := by
    dsimp only [IsGen] at hP
    obtain ⟨h1, -⟩ := hP
    have h4 : (P ≫ A.iota (1 - e5)) ≫ A.F.hom = P ≫ A.F.hom := by
      rw [Category.assoc, A.iota_over]
    rw [unit_homMk_eq A P hPs (P ≫ A.iota (1 - e5)) _ h4,
      homMk_mk_comp_iota A (P ≫ A.F.hom) P rfl (1 - e5) h4, ← MonObj.comp_pow,
      torsion_comp_iota A 5 _ h1, MonObj.comp_one]
  inKer := by
    dsimp only [IsGen] at hP
    obtain ⟨h1, -⟩ := hP
    have h3 : ((P ≫ A.iota (1 - e5)) ≫ A.iota e5) ≫ A.F.hom = P ≫ A.F.hom := by
      simp only [Category.assoc, A.iota_over]
    have h4 : (P ≫ A.iota (1 - e5)) ≫ A.F.hom = P ≫ A.F.hom := by
      rw [Category.assoc, A.iota_over]
    have hp5 : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ≫
        (Over.homMk (A.iota ((5 : ℕ) : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
      rw [comp_iotaHom_natCast, h1]
    rw [unit_homMk_eq A P hPs ((P ≫ A.iota (1 - e5)) ≫ A.iota e5) _ h3,
      homMk_mk_comp_iota A (P ≫ A.F.hom) (P ≫ A.iota (1 - e5)) h4 e5 h3,
      homMk_mk_comp_iota A (P ≫ A.F.hom) P rfl (1 - e5) h4, comp_iota_comp_iota,
      e5_mul_one_sub, comp_iota_natCast_mul_eq_one A 5 _ hp5, MonObj.comp_one]
  nonzero := by
    dsimp only [IsGen] at hP
    obtain ⟨-, h2⟩ := hP
    intro k _ _ s hzero
    have e : s ≫ P ≫ A.F.hom = s := by rw [hPs, Category.comp_id]
    have hs : (s ≫ P) ≫ A.F.hom = s := by rw [Category.assoc, e]
    have hq := (isGenAt_congr A e (s ≫ P) (Category.assoc _ _ _) hs).1 (h2 k s)
    dsimp only [IsGenAt] at hq
    have hQ : (s ≫ P ≫ A.iota (1 - e5)) ≫ A.F.hom = s := by
      simp only [Category.assoc, A.iota_over]; exact e
    have hsplit : (Over.homMk (U := Over.mk s) (s ≫ P ≫ A.iota (1 - e5)) hQ :
          Over.mk s ⟶ A.F) =
        Over.homMk (U := Over.mk s) (s ≫ P) hs ≫
          (Over.homMk (A.iota (1 - e5)) (A.iota_over _) : A.F ⟶ A.F) :=
      Over.OverMorphism.ext (Category.assoc s P (A.iota (1 - e5))).symm
    rw [hsplit] at hzero
    exact one_sub_e5_not_mem ((hq.1 (1 - e5)).1 hzero)

end V15

end Y3Buzzard
