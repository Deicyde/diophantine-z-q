import ZInQKernel.Contrib.OneProof.SerreRigidityZ30.Leaves
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.Defs
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.GeomFree5
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.IotaInjective
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ActionMulCompat
import Mathlib

/-!
# Rigidity at level three on geometric fibres

Let `k` be an algebraically closed field receiving a map from `Z[1/30]`, `A` a false elliptic
curve over `k`, and `θ` an `O`-linear automorphism of `A` fixing a generator `P` of the
3-torsion. Then `θ` fixes every point:

1. `θ` commutes with `ι(0)`, the constant map to the unit, so it fixes the unit section and is a
   homomorphism.
2. `θ` permutes the finite set of 5-torsion points, so some power `θ^m`, `m ≥ 1`, fixes a
   generator of the 5-torsion; by Buzzard's Lemma 2.2, `θ^m = 1`.
3. On the commutative group of points, `x ↦ θ(x)` has finite order and fixes the 3-torsion,
   whose subgroups have Milne's orders `3^(4j)`. The 3-adic statement shows that `θ` fixes the
   points of 3-power order, and Milne's Theorem 12.5 gives `θ = 1`.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard

/-- The statement proved by a parallel file; it is a hypothesis here and will be discharged on assembly. -/
def ThreeAdicStmt : Prop := ∀ {G : Type} [CommGroup G] (φ : G →* G) (m : ℕ), 0 < m →
  (∀ x, (φ^[m]) x = x) → (∀ x : G, x ^ 3 = 1 → φ x = x) → ∀ r : ℕ,
  (∀ j : ℕ, Nat.card {x : G // x ^ (3 ^ j) = 1} = 3 ^ (r * j)) →
  ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → φ x = x

attribute [local instance] FEC.grp

namespace SR30

/-! ## Powers of an automorphism -/

/-- The `n`-fold composite `θ ≫ ⋯ ≫ θ` of an automorphism `θ`. -/
def isoPow {C : Type*} [Category C] {X : C} (θ : X ≅ X) : ℕ → (X ≅ X)
  | 0 => Iso.refl X
  | n + 1 => isoPow θ n ≪≫ θ

theorem isoPow_zero_hom {C : Type*} [Category C] {X : C} (θ : X ≅ X) :
    (isoPow θ 0).hom = 𝟙 X := rfl

theorem isoPow_succ_hom {C : Type*} [Category C] {X : C} (θ : X ≅ X) (n : ℕ) :
    (isoPow θ (n + 1)).hom = (isoPow θ n).hom ≫ θ.hom := rfl

/-- Composing with `θⁿ` is the `n`-th iterate of composing with `θ`. -/
theorem comp_isoPow {C : Type*} [Category C] {X U : C} (θ : X ≅ X) (g : (U ⟶ X) → (U ⟶ X))
    (hg : ∀ y, g y = y ≫ θ.hom) (x : U ⟶ X) : ∀ n : ℕ, x ≫ (isoPow θ n).hom = g^[n] x
  | 0 => by rw [isoPow_zero_hom, Category.comp_id, Function.iterate_zero_apply]
  | n + 1 => by
      rw [isoPow_succ_hom, Function.iterate_succ_apply', hg, ← comp_isoPow θ g hg x n,
        Category.assoc]

theorem isoPow_isMonHom {C : Type*} [Category C] [MonoidalCategory C] {X : C} [MonObj X]
    (θ : X ≅ X) [IsMonHom θ.hom] : ∀ n : ℕ, IsMonHom (isoPow θ n).hom
  | 0 => by rw [isoPow_zero_hom]; infer_instance
  | n + 1 => by
      have := isoPow_isMonHom θ n
      rw [isoPow_succ_hom]; infer_instance

/-- An injective self-map preserving a finite set has a positive iterate fixing each of its
points (pigeonhole). -/
theorem exists_iterate_eq {α : Type*} (p : α → Prop) [Finite {y // p y}] (g : α → α)
    (hg : Function.Injective g) (hp : ∀ y, p y → p (g y)) (P : α) (hP : p P) :
    ∃ m, 0 < m ∧ g^[m] P = P := by
  have hmem : ∀ n : ℕ, p (g^[n] P) := by
    intro n
    induction n with
    | zero => exact hP
    | succ n ih => rw [Function.iterate_succ_apply']; exact hp _ ih
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨g^[n] P, hmem n⟩ : {y // p y}))
  have heq : g^[i] P = g^[j] P := congrArg Subtype.val hfij
  have key : ∀ a b : ℕ, a < b → g^[a] P = g^[b] P → ∃ m, 0 < m ∧ g^[m] P = P := by
    intro a b hab h
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    rw [← Nat.add_sub_of_le hab.le, Function.iterate_add_apply] at h
    exact ((hg.iterate a) h).symm
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h heq
  · exact key j i h heq.symm

/-! ## Endomorphisms of a false elliptic curve -/

section FEC

variable {S : Scheme.{0}} (A : FEC S)

/-- A map commuting with `ι(a)` on total spaces commutes with it in `Over S`. -/
theorem homMk_iota_comm (f : A.F ⟶ A.F) (a : O) (h : A.iota a ≫ f.left = f.left ≫ A.iota a) :
    (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) ≫ f =
      f ≫ Over.homMk (A.iota a) (A.iota_over a) :=
  Over.OverMorphism.ext h

/-- `ι(0)` is the unit of the group of endomorphisms of `A`. -/
theorem homMk_iota_zero : (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F) = 1 := by
  have h := comp_iotaHom_natCast A (𝟙 A.F) 0
  rw [Nat.cast_zero, Category.id_comp, pow_zero] at h
  exact h

/-- An endomorphism commuting with `ι(0)` fixes the unit section. -/
theorem one_comp_of_comm_zero (f : A.F ⟶ A.F) (h : A.iota 0 ≫ f.left = f.left ≫ A.iota 0) :
    (MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ f = MonObj.one := by
  have h1 := homMk_iota_comm A f 0 h
  rw [homMk_iota_zero, MonObj.comp_one] at h1
  have h2 : (MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ ((1 : A.F ⟶ A.F) ≫ f) =
      (MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ (1 : A.F ⟶ A.F) := by rw [h1]
  rw [← Category.assoc, MonObj.comp_one] at h2
  rw [MonObj.one_eq_one]
  exact h2

/-- Powers of an `O`-linear automorphism are `O`-linear. -/
theorem isoPow_comm (θ : A.F ≅ A.F)
    (hθ : ∀ a : O, A.iota a ≫ θ.hom.left = θ.hom.left ≫ A.iota a) :
    ∀ (n : ℕ) (a : O), A.iota a ≫ (isoPow θ n).hom.left = (isoPow θ n).hom.left ≫ A.iota a
  | 0, a => by rw [isoPow_zero_hom, Over.id_left, Category.comp_id, Category.id_comp]
  | n + 1, a => by
      rw [isoPow_succ_hom, Over.comp_left, ← Category.assoc, isoPow_comm θ hθ n a,
        Category.assoc, hθ a, Category.assoc]

/-- The points of `A` over `U` form a commutative group: `x ↦ x ^ 2` is the action of `ι(2)`,
which is multiplicative. -/
abbrev ptsCommGroup (U : Over S) : CommGroup (U ⟶ A.F) :=
  { (inferInstance : Group (U ⟶ A.F)) with mul_comm := (GF5.fecAct A U).comm }

end FEC

end SR30

/-- Rigidity at level three on geometric fibres, from the 3-adic statement, Buzzard's Lemma 2.2,
Milne's Theorem 12.5 and Remark 8.4, and the fact that unit-preserving maps are homomorphisms. -/
theorem serreRigidityFibreZ30_of_leaves (hthree : ThreeAdicStmt) (hBz : BuzzardLemma22Full5)
    (hMl : MilneThm125Pts) (hR : MilneRem84) (hZ : ZeroPreservingIsHomLN) :
    SerreRigidityFibreZ30 := by
  intro k _ _ φ A θ hθι P hP hPθ
  have h30 : (30 : k) ≠ 0 := by
    have hu : IsUnit ((ringHomOfSpec φ).hom (30 : Y3RouteA.Z30)) := isUnit_thirty.map _
    rw [map_ofNat] at hu
    exact hu.ne_zero
  have h3 : ((3 : ℕ) : k) ≠ 0 := by
    intro h0
    apply h30
    rw [show (30 : k) = ((3 : ℕ) : k) * 10 by norm_num, h0, zero_mul]
  have hne : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  have hmon : IsMonHom θ.hom :=
    hZ (Spec (CommRingCat.of k)) A A θ.hom (SR30.one_comp_of_comm_zero A θ.hom (hθι 0))
  have hinj : Function.Injective A.iota := @iota_injective hR (Over.mk φ) A hne
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F), ∀ y, ψ y = y ≫ θ.hom :=
    ⟨IsMonHom.monoidHom θ.hom _, fun _ => rfl⟩
  have hψinj : Function.Injective ψ := fun y z h => by
    rw [hψ, hψ] at h
    exact (cancel_mono θ.hom).1 h
  obtain ⟨P5, hP5⟩ : ∃ P5 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F,
      IsGenAt 5 A (𝟙 _) P5 :=
    geomFree5_of_card (geomCard5_of_rem84 hR) (Over.mk φ) A k (𝟙 (Spec (CommRingCat.of k)))
  have hP5t : P5 ^ 5 = 1 :=
    (comp_iotaHom_natCast A P5 5).symm.trans ((hP5.1 ((5 : ℕ) : O)).2 ⟨1, (_root_.mul_one _).symm⟩)
  have hcard5 : Nat.card {y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F // y ^ 5 = 1} = 625 :=
    geomCard5_of_rem84 hR (Over.mk φ) A k (𝟙 (Spec (CommRingCat.of k)))
  have : Finite {y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F // y ^ 5 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard5]; norm_num)
  obtain ⟨m, hm, hmP⟩ := SR30.exists_iterate_eq (fun y => y ^ 5 = 1) ψ hψinj
    (fun y hy => by rw [← map_pow, hy, map_one]) P5 hP5t
  have hθm : (SR30.isoPow θ m).hom = 𝟙 A.F :=
    hBz k h30 A hinj (SR30.isoPow θ m) (SR30.isoPow_isMonHom θ m) (SR30.isoPow_comm A θ hθι m)
      P5 hP5 ((SR30.comp_isoPow θ ψ hψ P5 m).trans hmP)
  have hiter : ∀ y, (ψ^[m]) y = y := fun y =>
    (SR30.comp_isoPow θ ψ hψ y m).symm.trans (by rw [hθm, Category.comp_id])
  have hfix3 : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F, y ^ 3 = 1 → ψ y = y := by
    intro y hy
    obtain ⟨a, rfl⟩ := hP.2 y hy
    rw [hψ, Category.assoc, SR30.homMk_iota_comm A θ.hom a (hθι a), ← Category.assoc, hPθ]
  have hcard : ∀ j : ℕ, Nat.card {y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F //
      y ^ (3 ^ j) = 1} = 3 ^ (4 * j) := by
    intro j
    have h3j : ((3 ^ j : ℕ) : k) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero j h3
    exact (hR (Over.mk φ) A k (𝟙 (Spec (CommRingCat.of k))) (3 ^ j) h3j).trans
      (by rw [← pow_mul, mul_comm])
  have hthree' := @hthree _ (SR30.ptsCommGroup A _) ψ m hm hiter hfix3 4 hcard
  have hθ : θ.hom = 𝟙 A.F :=
    hMl k A 3 Nat.prime_three h3 θ.hom (𝟙 A.F) hmon inferInstance
      (fun n y hy => by rw [← hψ, Category.comp_id]; exact hthree' n y hy)
  intro x
  rw [hθ, Category.comp_id]

end Y3Buzzard
