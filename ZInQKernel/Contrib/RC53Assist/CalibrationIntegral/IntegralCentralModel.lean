import ZInQKernel.Contrib.RC53Assist.Calibration.KummerIntegral
import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Integral central Kummer comparison and calibration orders

The actual central compact complex is the compact Kummer complex of the quadratic
 twist. The Tate projections, the integral twist identification, and the fixed
 decomposition comparisons give the canonical coefficient map into the genuine
 finite-level complexes. Reduction of the Kummer cocycles is proved, including
 compatibility with the actual local Kummer coefficient maps and coboundaries.
 These maps induce a comparison of the Selmer cones.

The central normal form has a free line in degrees one and two and three disks
 in degrees zero to one, one to two, and two to three. Cohomology is computed as
 modules before taking orders. Both scalar disks and matrix disks are treated.
 Matrix disks retain noncyclic finite torsion; their determinant scalars compute
 the same finite coefficient orders once the precision exceeds their valuations.

The remaining inputs `CanonicalIntegralCentralModel` and `IntegralBlockCentralModel`
 specify a finite-free retained-basis model, an integral normalization, an actual
 quasi-isomorphism to the compact central complex, and quasi-isomorphisms of its
 canonical finite coefficient comparisons. They contain no order equalities.
 Neither the integral model nor the derived finite-fibre quasi-isomorphisms are
 constructed here. The latter cannot be inferred just from rational comparisons
 or reduction of individual cocycles.

The determinant-basis matrices are integral and unimodular, and the three order
 equalities of `DiskTie` are proved from these model inputs. `DiskArith` remains
 the separate arithmetic-order input. The rational calibration identification,
 coordinate transfer, and free class and functional coefficients also remain inputs.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.CalibrationIntegral

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

section NormalForm

variable {R : Type} [CommRing R]

/-- Multiplication by a scalar. -/
def scalarMap (x : R) : R →ₗ[R] R where
  toFun a := x * a
  map_add' := mul_add x
  map_smul' a b := by change x * (a * b) = a * (x * b); ring

/-- The terms of the central normal form, in its integral bases. -/
def normalTerms (R : Type) [CommRing R] : ℕ → ModuleCat R
  | 0 => ModuleCat.of R R
  | 1 => ModuleCat.of R (R × R × R)
  | 2 => ModuleCat.of R (R × R × R)
  | 3 => ModuleCat.of R R
  | _ + 4 => ModuleCat.of R PUnit

/-- The degree-zero differential of the first disk. -/
def normalD0 (x : R) : R →ₗ[R] (R × R × R) where
  toFun a := (0, x * a, 0)
  map_add' a b := by simp [mul_add]
  map_smul' a b := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · change x * (a * b) = a * (x * b); ring
      · simp

/-- The middle disk differential. -/
def normalD1 (x : R) : (R × R × R) →ₗ[R] (R × R × R) where
  toFun a := (0, x * a.2.2, 0)
  map_add' a b := by simp [mul_add]
  map_smul' a b := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · change x * (a * b.2.2) = a * (x * b.2.2); ring
      · simp

/-- The degree-two differential of the last disk. -/
def normalD2 (x : R) : (R × R × R) →ₗ[R] R :=
  (scalarMap x).comp ((LinearMap.snd R R R).comp (LinearMap.snd R R (R × R)))

/-- The differentials in the retained normal-form bases. -/
def normalD (x₁ x₂ x₃ : R) : (n : ℕ) → normalTerms R n ⟶ normalTerms R (n + 1)
  | 0 => ModuleCat.ofHom (normalD0 x₁)
  | 1 => ModuleCat.ofHom (normalD1 x₂)
  | 2 => ModuleCat.ofHom (normalD2 x₃)
  | _ + 3 => 0

/-- Consecutive normal-form differentials compose to zero. -/
theorem normalD_sq (x₁ x₂ x₃ : R) (n : ℕ) :
    normalD x₁ x₂ x₃ n ≫ normalD x₁ x₂ x₃ (n + 1) = 0 := by
  rcases n with _ | _ | _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (0, x₂ * 0, 0) = (0 : R × R × R)
    simp
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change x₃ * 0 = 0
    simp
  · exact Limits.comp_zero
  · exact Limits.zero_comp

/-- The integral central normal form, extended by zero in negative degrees. -/
def normalComplex (x₁ x₂ x₃ : R) : CochainComplex (ModuleCat R) ℤ :=
  (natCx (CochainComplex.of (normalTerms R) (normalD x₁ x₂ x₃)
    (normalD_sq x₁ x₂ x₃))).toCC

/-- A cohomology presentation from a surjective cycle-class map with the exact boundary kernel. -/
def homologyEquivOfClass (C : CochainComplex (ModuleCat R) ℤ) (i n j : ℤ)
    (hi : (ComplexShape.up ℤ).prev n = i) (hj : (ComplexShape.up ℤ).next n = j)
    {H : Type} [AddCommGroup H] [Module R H]
    (f : LinearMap.ker (C.sc' i n j).g.hom →ₗ[R] H) (hf : Function.Surjective f)
    (hker : LinearMap.range (C.sc' i n j).moduleCatToCycles = LinearMap.ker f) :
    C.homology n ≃ₗ[R] H :=
  (C.homologyIsoSc' i n j hi hj).toLinearEquiv.trans
    ((C.sc' i n j).moduleCatHomologyIso.toLinearEquiv.trans
      ((Submodule.Quotient.equiv _ _ (LinearEquiv.refl R _) (by simpa using hker)).trans
        (f.quotKerEquivOfSurjective hf)))

/-- The first normal-form differential in the cochain complex. -/
theorem normalComplex_d0 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 0 1).hom = normalD0 x₁ := by
  unfold normalComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of, CochainComplex.of.d, normalD, Category.comp_id]
  rfl

/-- The middle normal-form differential in the cochain complex. -/
theorem normalComplex_d1 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 1 2).hom = normalD1 x₂ := by
  unfold normalComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of, CochainComplex.of.d, normalD, Category.comp_id]
  rfl

/-- The last normal-form differential in the cochain complex. -/
theorem normalComplex_d2 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 2 3).hom = normalD2 x₃ := by
  unfold normalComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of, CochainComplex.of.d, normalD, Category.comp_id]
  rfl

/-- No differential enters degree zero. -/
theorem normalComplex_dneg (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d (-1) 0).hom = 0 := by
  unfold normalComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  rfl

/-- No differential exits degree three. -/
theorem normalComplex_d3 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 3 4).hom = 0 := by
  unfold normalComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of, CochainComplex.of.d, normalD, Category.comp_id]
  rfl

/-- Multiplication has image the principal ideal. -/
theorem range_scalarMap (x : R) :
    LinearMap.range (scalarMap x) = (Ideal.span {x} : Submodule R R) := by
  ext a
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩

/-- The class map in degree zero is the first disk's kernel coordinate. -/
def class0 (x₁ x₂ x₃ : R) :
    LinearMap.ker ((normalComplex x₁ x₂ x₃).sc' (-1) 0 1).g.hom →ₗ[R]
      LinearMap.ker (scalarMap x₁) where
  toFun a := ⟨a.1, by
    have h := a.2
    change ((normalComplex x₁ x₂ x₃).d 0 1).hom a.1 = 0 at h
    rw [normalComplex_d0] at h
    exact congrArg (fun b : R × R × R => b.2.1) h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zeroth cohomology is the kernel of the degree-one disk differential. -/
def normalH0Equiv (x₁ x₂ x₃ : R) :
    (normalComplex x₁ x₂ x₃).homology 0 ≃ₗ[R] LinearMap.ker (scalarMap x₁) := by
  apply homologyEquivOfClass _ (-1) 0 1 (by simp) (by simp) (class0 x₁ x₂ x₃)
  · intro a
    refine ⟨⟨a.1, ?_⟩, rfl⟩
    change ((normalComplex x₁ x₂ x₃).d 0 1).hom a.1 = 0
    rw [normalComplex_d0]
    have h : x₁ * a.1 = 0 := a.2
    change (0, x₁ * a.1, 0) = (0 : R × R × R)
    simp [h]
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, rfl⟩
      apply Subtype.ext
      change ((normalComplex x₁ x₂ x₃).d (-1) 0).hom b = 0
      rw [normalComplex_dneg]
      rfl
    · intro ha
      refine ⟨0, ?_⟩
      apply Subtype.ext
      change ((normalComplex x₁ x₂ x₃).d (-1) 0).hom 0 = a.1
      rw [normalComplex_dneg]
      exact (congrArg Subtype.val ha).symm

/-- The cycle-class map in degree two retains the free line and the two disk contributions. -/
def class2 (x₁ x₂ x₃ : R) :
    LinearMap.ker ((normalComplex x₁ x₂ x₃).sc' 1 2 3).g.hom →ₗ[R]
      (R × (R ⧸ Ideal.span {x₂}) × LinearMap.ker (scalarMap x₃)) where
  toFun a := (a.1.1, Submodule.Quotient.mk a.1.2.1, ⟨a.1.2.2, by
    have h := a.2
    change ((normalComplex x₁ x₂ x₃).d 2 3).hom a.1 = 0 at h
    rw [normalComplex_d2] at h
    exact h⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Second cohomology is a free line, the middle disk cokernel, and the last disk kernel. -/
def normalH2Equiv (x₁ x₂ x₃ : R) :
    (normalComplex x₁ x₂ x₃).homology 2 ≃ₗ[R]
      (R × (R ⧸ Ideal.span {x₂}) × LinearMap.ker (scalarMap x₃)) := by
  apply homologyEquivOfClass _ 1 2 3 (by simp) (by simp) (class2 x₁ x₂ x₃)
  · rintro ⟨a, b, c⟩
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨⟨(a, b', c.1), ?_⟩, rfl⟩
    change ((normalComplex x₁ x₂ x₃).d 2 3).hom (a, b', c.1) = 0
    rw [normalComplex_d2]
    exact c.2
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, rfl⟩
      have h : (Submodule.Quotient.mk (x₂ * b.2.2) : R ⧸ Ideal.span {x₂}) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ⟨b.2.2, rfl⟩)
      apply Prod.ext
      · change (((normalComplex x₁ x₂ x₃).d 1 2).hom b).1 = 0
        rw [normalComplex_d1]
        rfl
      · apply Prod.ext
        · change (Submodule.Quotient.mk (((normalComplex x₁ x₂ x₃).d 1 2).hom b).2.1 :
            R ⧸ Ideal.span {x₂}) = 0
          rw [normalComplex_d1]
          exact h
        · apply Subtype.ext
          change (((normalComplex x₁ x₂ x₃).d 1 2).hom b).2.2 = 0
          rw [normalComplex_d1]
          rfl
    · intro ha
      have h0 : a.1.1 = 0 := congrArg Prod.fst ha
      have h2 : (Submodule.Quotient.mk a.1.2.1 : R ⧸ Ideal.span {x₂}) = 0 :=
        congrArg (fun b => b.2.1) ha
      have h3 : a.1.2.2 = 0 := congrArg (fun b => (b.2.2 : R)) ha
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h2)
      refine ⟨(0, 0, b), ?_⟩
      apply Subtype.ext
      change ((normalComplex x₁ x₂ x₃).d 1 2).hom (0, 0, b) = a.1
      rw [normalComplex_d1]
      exact Prod.ext h0.symm (Prod.ext hb.symm h3.symm)

/-- The degree-three class map is the last disk's cokernel coordinate. -/
def class3 (x₁ x₂ x₃ : R) :
    LinearMap.ker ((normalComplex x₁ x₂ x₃).sc' 2 3 4).g.hom →ₗ[R]
      (R ⧸ Ideal.span {x₃}) :=
  (Ideal.span {x₃}).mkQ.comp (LinearMap.ker ((normalComplex x₁ x₂ x₃).sc' 2 3 4).g.hom).subtype

/-- Third cohomology is the last disk's cokernel. -/
def normalH3Equiv (x₁ x₂ x₃ : R) :
    (normalComplex x₁ x₂ x₃).homology 3 ≃ₗ[R] (R ⧸ Ideal.span {x₃}) := by
  apply homologyEquivOfClass _ 2 3 4 (by simp) (by simp) (class3 x₁ x₂ x₃)
  · intro a
    obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
    refine ⟨⟨a', ?_⟩, rfl⟩
    change ((normalComplex x₁ x₂ x₃).d 3 4).hom a' = 0
    rw [normalComplex_d3]
    rfl
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, hb⟩
      apply (Submodule.Quotient.mk_eq_zero (Ideal.span {x₃})).2
      have h := congrArg Subtype.val hb
      change ((normalComplex x₁ x₂ x₃).d 2 3).hom b = a.1 at h
      rw [normalComplex_d2] at h
      exact Ideal.mem_span_singleton.2 ⟨b.2.2, h.symm⟩
    · intro ha
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1
        ((Submodule.Quotient.mk_eq_zero (Ideal.span {x₃})).1 ha)
      refine ⟨(0, 0, b), Subtype.ext ?_⟩
      change ((normalComplex x₁ x₂ x₃).d 2 3).hom (0, 0, b) = a.1
      rw [normalComplex_d2]
      exact hb.symm

/-- The degree-one cycle-class map retains the first disk's cokernel and the middle disk's kernel. -/
def class1 (x₁ x₂ x₃ : R) :
    LinearMap.ker ((normalComplex x₁ x₂ x₃).sc' 0 1 2).g.hom →ₗ[R]
      (R × (R ⧸ Ideal.span {x₁}) × LinearMap.ker (scalarMap x₂)) where
  toFun a := (a.1.1, Submodule.Quotient.mk a.1.2.1, ⟨a.1.2.2, by
    have h := a.2
    change ((normalComplex x₁ x₂ x₃).d 1 2).hom a.1 = 0 at h
    rw [normalComplex_d1] at h
    exact congrArg (fun b : R × R × R => b.2.1) h⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- First cohomology is a free line, the first disk cokernel, and the middle disk kernel. -/
def normalH1Equiv (x₁ x₂ x₃ : R) :
    (normalComplex x₁ x₂ x₃).homology 1 ≃ₗ[R]
      (R × (R ⧸ Ideal.span {x₁}) × LinearMap.ker (scalarMap x₂)) := by
  apply homologyEquivOfClass _ 0 1 2 (by simp) (by simp) (class1 x₁ x₂ x₃)
  · rintro ⟨a, b, c⟩
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨⟨(a, b', c.1), ?_⟩, rfl⟩
    change ((normalComplex x₁ x₂ x₃).d 1 2).hom (a, b', c.1) = 0
    rw [normalComplex_d1]
    have h : x₂ * c.1 = 0 := c.2
    change (0, x₂ * c.1, 0) = (0 : R × R × R)
    simp [h]
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, rfl⟩
      let b₀ : R := b
      have h : (Submodule.Quotient.mk (x₁ * b₀) : R ⧸ Ideal.span {x₁}) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ⟨b₀, rfl⟩)
      apply Prod.ext
      · change (((normalComplex x₁ x₂ x₃).d 0 1).hom b).1 = 0
        rw [normalComplex_d0]
        rfl
      · apply Prod.ext
        · change (Submodule.Quotient.mk (((normalComplex x₁ x₂ x₃).d 0 1).hom b).2.1 :
            R ⧸ Ideal.span {x₁}) = 0
          rw [normalComplex_d0]
          exact h
        · apply Subtype.ext
          change (((normalComplex x₁ x₂ x₃).d 0 1).hom b).2.2 = 0
          rw [normalComplex_d0]
          rfl
    · intro ha
      have h0 : a.1.1 = 0 := congrArg Prod.fst ha
      have h2 : (Submodule.Quotient.mk a.1.2.1 : R ⧸ Ideal.span {x₁}) = 0 :=
        congrArg (fun b => b.2.1) ha
      have h3 : a.1.2.2 = 0 := congrArg (fun b => (b.2.2 : R)) ha
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h2)
      refine ⟨b, Subtype.ext ?_⟩
      change ((normalComplex x₁ x₂ x₃).d 0 1).hom b = a.1
      rw [normalComplex_d0]
      exact Prod.ext h0.symm (Prod.ext hb.symm h3.symm)

/-- Over a finite coefficient ring, a scalar kernel and scalar cokernel have equal orders. -/
theorem card_scalar_kernel [Finite R] (x : R) :
    Nat.card (LinearMap.ker (scalarMap x)) = Nat.card (R ⧸ Ideal.span {x}) := by
  rw [card_ker_eq_card_coker, range_scalarMap]

/-- The zeroth normal-form order is the order of the first cyclic disk. -/
theorem normal_card0 [Finite R] (x₁ x₂ x₃ : R) :
    Nat.card ((normalComplex x₁ x₂ x₃).homology 0) = Nat.card (R ⧸ Ideal.span {x₁}) := by
  rw [Nat.card_congr (normalH0Equiv x₁ x₂ x₃).toEquiv, card_scalar_kernel]

/-- The second normal-form order includes the free coefficient ring and both adjacent disks. -/
theorem normal_card2 [Finite R] (x₁ x₂ x₃ : R) :
    Nat.card ((normalComplex x₁ x₂ x₃).homology 2) =
      Nat.card R * Nat.card (R ⧸ Ideal.span {x₂}) * Nat.card (R ⧸ Ideal.span {x₃}) := by
  rw [Nat.card_congr (normalH2Equiv x₁ x₂ x₃).toEquiv, Nat.card_prod, Nat.card_prod,
    card_scalar_kernel, mul_assoc]

/-- The third normal-form order is the order of the last cyclic disk. -/
theorem normal_card3 (x₁ x₂ x₃ : R) :
    Nat.card ((normalComplex x₁ x₂ x₃).homology 3) = Nat.card (R ⧸ Ideal.span {x₃}) :=
  Nat.card_congr (normalH3Equiv x₁ x₂ x₃).toEquiv

end NormalForm

section ScalarChange

variable {R S : Type} [CommRing R] [CommRing S]

/-- The ranks of the four normal-form terms. -/
def normalRank : ℤ → ℕ
  | .ofNat 0 => 1
  | .ofNat 1 => 3
  | .ofNat 2 => 3
  | .ofNat 3 => 1
  | .ofNat (_ + 4) => 0
  | .negSucc _ => 0

/-- Coordinates on a single free line. -/
def lineCoordinates (R : Type) [CommRing R] : R ≃ₗ[R] (Fin 1 → R) where
  toFun a := fun _ => a
  invFun a := a 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv a := by funext i; fin_cases i; rfl

/-- Coordinates on the three disk and core entries. -/
def tripleCoordinates (R : Type) [CommRing R] : (R × R × R) ≃ₗ[R] (Fin 3 → R) where
  toFun a := ![a.1, a.2.1, a.2.2]
  invFun a := (a 0, a 1, a 2)
  map_add' a b := by funext i; fin_cases i <;> rfl
  map_smul' a b := by funext i; fin_cases i <;> rfl
  left_inv _ := rfl
  right_inv a := by funext i; fin_cases i <;> rfl

/-- Coordinates on a zero module. -/
def zeroCoordinates (R : Type) [CommRing R] : PUnit ≃ₗ[R] (Fin 0 → R) where
  toFun _ := fun i => Fin.elim0 i
  invFun _ := PUnit.unit
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

/-- The integral bases on all degrees of the normal form. -/
def normalCoordinates (x₁ x₂ x₃ : R) : (n : ℤ) →
    (normalComplex x₁ x₂ x₃).X n ≃ₗ[R] (Fin (normalRank n) → R)
  | .ofNat 0 => lineCoordinates R
  | .ofNat 1 => tripleCoordinates R
  | .ofNat 2 => tripleCoordinates R
  | .ofNat 3 => lineCoordinates R
  | .ofNat (_ + 4) => zeroCoordinates R
  | .negSucc _ => zeroCoordinates R

/-- The termwise coefficient-extension equivalence in the integral bases. -/
def extendedNormalCoordinates (φ : R →+* S) (x₁ x₂ x₃ : R) (n : ℤ) :
    (scalarChangedComplex φ (normalComplex x₁ x₂ x₃)).X n ≃ₗ[S]
      (normalComplex (φ x₁) (φ x₂) (φ x₃)).X n := by
  letI : Algebra R S := φ.toAlgebra
  exact ((LinearEquiv.baseChange R S ((normalComplex x₁ x₂ x₃).X n)
    (Fin (normalRank n) → R) (normalCoordinates x₁ x₂ x₃ n)).trans
      (TensorProduct.piScalarRight R S S (Fin (normalRank n)))).trans
    (normalCoordinates (φ x₁) (φ x₂) (φ x₃) n).symm

/-- Extending the central normal form maps its differential entries through the coefficient map.
No flatness of that coefficient map is assumed. -/
def normalScalarChangeIso (φ : R →+* S) (x₁ x₂ x₃ : R) :
    scalarChangedComplex φ (normalComplex x₁ x₂ x₃) ≅
      normalComplex (φ x₁) (φ x₂) (φ x₃) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (extendedNormalCoordinates φ x₁ x₂ x₃ n).toModuleIso) ?_
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  dsimp only [scalarChangedComplex, Functor.mapHomologicalComplex]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let : Algebra R S := φ.toAlgebra
  induction a using TensorProduct.inductionOn with
  | tmul b a =>
    let b₀ : S := b
    cases i with
    | negSucc n =>
      have ha : a = 0 := Subsingleton.elim (α := PUnit) _ _
      subst ha
      simp only [TensorProduct.tmul_zero, map_zero]
    | ofNat n =>
      rcases n with _ | _ | _ | _ | n
      · have hR : (normalComplex x₁ x₂ x₃).d 0 1 = ModuleCat.ofHom (normalD0 x₁) :=
          ModuleCat.hom_ext (normalComplex_d0 x₁ x₂ x₃)
        have hS : (normalComplex (φ x₁) (φ x₂) (φ x₃)).d 0 1 =
            ModuleCat.ofHom (normalD0 (φ x₁)) :=
          ModuleCat.hom_ext (normalComplex_d0 _ _ _)
        change _ = _
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [hR, hS]
        let a₀ : R := a
        change (0, φ x₁ * (φ a₀ * b₀), 0) = (φ 0 * b₀, φ (x₁ * a₀) * b₀, φ 0 * b₀)
        simp only [map_zero, zero_mul, map_mul, mul_assoc]
      · have hR : (normalComplex x₁ x₂ x₃).d 1 2 = ModuleCat.ofHom (normalD1 x₂) :=
          ModuleCat.hom_ext (normalComplex_d1 x₁ x₂ x₃)
        have hS : (normalComplex (φ x₁) (φ x₂) (φ x₃)).d 1 2 =
            ModuleCat.ofHom (normalD1 (φ x₂)) :=
          ModuleCat.hom_ext (normalComplex_d1 _ _ _)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [hR, hS]
        let a₀ : R × R × R := a
        change (0, φ x₂ * (φ a₀.2.2 * b₀), 0) =
          (φ 0 * b₀, φ (x₂ * a₀.2.2) * b₀, φ 0 * b₀)
        simp only [map_zero, zero_mul, map_mul, mul_assoc]
      · have hR : (normalComplex x₁ x₂ x₃).d 2 3 = ModuleCat.ofHom (normalD2 x₃) :=
          ModuleCat.hom_ext (normalComplex_d2 x₁ x₂ x₃)
        have hS : (normalComplex (φ x₁) (φ x₂) (φ x₃)).d 2 3 =
            ModuleCat.ofHom (normalD2 (φ x₃)) :=
          ModuleCat.hom_ext (normalComplex_d2 _ _ _)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [hR, hS]
        let a₀ : R × R × R := a
        change φ x₃ * (φ a₀.2.2 * b₀) = φ (x₃ * a₀.2.2) * b₀
        simp only [map_mul, mul_assoc]
      · exact Subsingleton.elim (α := PUnit) _ _
      · have ha : a = 0 := Subsingleton.elim (α := PUnit) _ _
        subst ha
        simp only [TensorProduct.tmul_zero, map_zero]
  | add a b ha hb =>
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, map_add] at ha hb ⊢
    rw [ha, hb]

end ScalarChange

/-- The finite coefficient normal form has exactly the three orders used in `DiskTie`. -/
theorem finiteNormal_orders (i : ℕ) (hi : i ≠ 0) (x₁ x₂ x₃ : ℤ_[2]) :
    Nat.card ((normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology 0) =
        cycOrder i x₁ ∧
      Nat.card ((normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology 2) =
        2 ^ (i * i) * cycOrder i x₂ * cycOrder i x₃ ∧
      Nat.card ((normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology 3) =
        cycOrder i x₃ := by
  refine ⟨normal_card0 _ _ _, ?_, normal_card3 _ _ _⟩
  rw [normal_card2, card_acoef i hi]

section TwistedCompact

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Manuscript.RC53Assist.CentralKummer

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)

/-- The quadratic-twist point identification over the chosen square root. -/
def globalTwistPointEquiv :
    ((twistK W h).baseChange (KS K S)).toAffine.Point ≃+
      (W.baseChange (KS K S)).toAffine.Point := by
  classical
  exact (AddEquiv.cast (M := fun V : WeierstrassCurve (KS K S) => V.toAffine.Point)
    (twistK_map W (algebraMap K (KS K S)) h)).trans
      (twistPointEquiv two_ne_zero (W.baseChange (KS K S)) hs0 hs)

include hs hs0 in
/-- The target coordinates of the global twist point identification are nonsingular. -/
theorem globalTwistPointEquiv_nonsingular {x y : KS K S}
    (hxy : ((twistK W h).baseChange (KS K S)).toAffine.Nonsingular x y) :
    (W.baseChange (KS K S)).toAffine.Nonsingular (s⁻¹ ^ 2 * x)
      (s⁻¹ ^ 3 * y + s⁻¹ ^ 2 * (-(W.baseChange (KS K S)).a₁ / 2) * x -
        (W.baseChange (KS K S)).a₃ / 2) := by
  have hxy' : (twistK (W.baseChange (KS K S)) (algebraMap K (KS K S) h)).toAffine.Nonsingular x y :=
    (twistK_map W (algebraMap K (KS K S)) h) ▸ hxy
  convert twistPointEquiv_nonsingular two_ne_zero (W.baseChange (KS K S)) hs0 hs hxy' using 1
  simp only [sub_eq_add_neg, neg_div]

/-- The global twist identification is given by the usual change of coordinates. -/
theorem globalTwistPointEquiv_some {x y : KS K S}
    (hxy : ((twistK W h).baseChange (KS K S)).toAffine.Nonsingular x y) :
    globalTwistPointEquiv W s hs hs0 (.some x y hxy) =
      .some _ _ (globalTwistPointEquiv_nonsingular W s hs hs0 hxy) := by
  classical
  have hxy' : (twistK (W.baseChange (KS K S)) (algebraMap K (KS K S) h)).toAffine.Nonsingular x y :=
    (twistK_map W (algebraMap K (KS K S)) h) ▸ hxy
  have hcast :
      (AddEquiv.cast (M := fun V : WeierstrassCurve (KS K S) => V.toAffine.Point)
        (twistK_map W (algebraMap K (KS K S)) h)) (.some x y hxy) =
        Affine.Point.some x y hxy' :=
    (AddEquiv.cast_apply (M := fun V : WeierstrassCurve (KS K S) => V.toAffine.Point)
      (twistK_map W (algebraMap K (KS K S)) h) (.some x y hxy)).trans
        (Affine.Point.cast_some (twistK_map W (algebraMap K (KS K S)) h) hxy)
  have htarget := globalTwistPointEquiv_nonsingular W s hs hs0 hxy
  have htarget' : (W.baseChange (KS K S)).toAffine.Nonsingular (s⁻¹ ^ 2 * x)
      (s⁻¹ ^ 3 * y + s⁻¹ ^ 2 * (-(W.baseChange (KS K S)).a₁ / 2) * x +
        -(W.baseChange (KS K S)).a₃ / 2) := by
    simpa only [sub_eq_add_neg, neg_div] using htarget
  refine (congrArg (twistPointEquiv two_ne_zero (W.baseChange (KS K S)) hs0 hs) hcast).trans ?_
  simpa only [sub_eq_add_neg, neg_div] using
    twistPointEquiv_some two_ne_zero (W.baseChange (KS K S)) hs0 hs hxy' htarget'

/-- The global twist identification carries the Galois action to the quadratic-character action. -/
theorem globalTwistPointEquiv_galois (σ : GKS K S)
    (P : ((twistK W h).baseChange (KS K S)).toAffine.Point) :
    globalTwistPointEquiv W s hs hs0 (Affine.Point.map (galS K S σ).toAlgHom P) =
      ((quadChar s hs hs0 σ : ℤˣ) : ℤ) •
        Affine.Point.map (galS K S σ).toAlgHom (globalTwistPointEquiv W s hs hs0 P) := by
  classical
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def]
    simp only [map_zero, smul_zero]
  · rw [Affine.Point.map_some, globalTwistPointEquiv_some, globalTwistPointEquiv_some,
      Affine.Point.map_some]
    have h1 : (galS K S σ).toAlgHom ((W.baseChange (KS K S)).a₁) = (W.baseChange (KS K S)).a₁ :=
      AlgEquiv.commutes _ _
    have h3 : (galS K S σ).toAlgHom ((W.baseChange (KS K S)).a₃) = (W.baseChange (KS K S)).a₃ :=
      AlgEquiv.commutes _ _
    rcases galS_sqrt s hs σ with hσs | hσs
    · have hχ : quadChar s hs hs0 σ = 1 := by simp [quadChar, hσs]
      change (galS K S σ).toAlgHom s = s at hσs
      rw [hχ, Units.val_one, one_smul]
      simp only [Affine.Point.some.injEq]
      constructor
      · simp only [map_mul, map_pow, map_inv₀, hσs]
      · simp only [map_add, map_sub, map_mul, map_pow, map_inv₀, map_div₀, map_neg,
          map_ofNat, hσs, h1, h3]
    · have hχ : quadChar s hs hs0 σ = -1 := by
        simp [quadChar, hσs, neg_ne_self_of_ne_zero s hs0]
      change (galS K S σ).toAlgHom s = -s at hσs
      rw [hχ, Units.val_neg, Units.val_one, neg_one_zsmul, Affine.Point.neg_some]
      simp only [Affine.Point.some.injEq]
      constructor
      · simp only [map_mul, map_pow, map_inv₀, hσs, inv_neg, even_two, Even.neg_pow]
      · simp only [map_add, map_sub, map_mul, map_pow, map_inv₀, map_div₀, map_neg,
          map_ofNat, hσs, Affine.negY, WeierstrassCurve.baseChange,
          WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
        simp only [AlgHom.commutes]
        field_simp
        ring

/-- The same integral twist identification on finite torsion. -/
def globalTwistTorsEquiv (i : ℕ) :
    TorsS K S (twistK W h) ((2 ^ i : ℕ) : ℤ) ≃+ TorsS K S W ((2 ^ i : ℕ) : ℤ) where
  toFun P := ⟨globalTwistPointEquiv W s hs hs0 P.1, by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.1 P.2, map_zero]⟩
  invFun P := ⟨(globalTwistPointEquiv W s hs hs0).symm P.1, by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.1 P.2, map_zero]⟩
  map_add' P Q := Subtype.ext (map_add (globalTwistPointEquiv W s hs hs0) P.1 Q.1)
  left_inv P := Subtype.ext (AddEquiv.symm_apply_apply _ P.1)
  right_inv P := Subtype.ext (AddEquiv.apply_symm_apply _ P.1)

/-- The torsion comparison is equivariant for the central quadratic character. -/
theorem globalTwistTorsEquiv_galois (i : ℕ) (σ : GKS K S)
    (P : TorsS K S (twistK W h) ((2 ^ i : ℕ) : ℤ)) :
    globalTwistTorsEquiv W s hs hs0 i (σ • P) =
      ((quadChar s hs hs0 σ : ℤˣ) : ℤ) • (σ • globalTwistTorsEquiv W s hs hs0 i P) := by
  apply Subtype.ext
  exact globalTwistPointEquiv_galois W s hs hs0 σ P.1

include s hs hs0 in
/-- Full torsion over the chosen field is preserved by the quadratic twist. -/
theorem fullTorsion_twist (i : ℕ) (hFull : FullTorsion K S W (2 ^ i)) :
    FullTorsion K S (twistK W h) (2 ^ i) :=
  (Nat.card_congr (globalTwistTorsEquiv W s hs hs0 i).toEquiv).trans hFull

variable {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The actual central quadratic twist. -/
abbrev centralCurve (G : GenuineKummerData K E₀ hZ) : WeierstrassCurve K :=
  twistK G.W (hZ : K)

/-- The central twist is elliptic. -/
instance centralCurve_elliptic (G : GenuineKummerData K E₀ hZ) : (centralCurve G).IsElliptic :=
  isElliptic_twistK two_ne_zero G.W (ne_zero_of_sqrt G.s G.hs G.hs0)

/-- Full two-power torsion for the actual central twist. -/
theorem centralFullTorsion (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    FullTorsion K G.S (centralCurve G) (2 ^ i) :=
  fullTorsion_twist G.W G.s G.hs G.hs0 i (G.hFull i)

/-- The integral Selmer data of the actual central twist. -/
def compactCentralSelData (G : GenuineKummerData K E₀ hZ) : SelData ℤ_[2] :=
  tateKummerSelData G.S (centralCurve G) (centralFullTorsion G)

/-- The compact complex for the actual central twist, rather than the untwisted curve. -/
def compactCentralComplex (G : GenuineKummerData K E₀ hZ) :
    CochainComplex (ModuleCat ℤ_[2]) ℤ :=
  (selCx (compactCentralSelData G)).toCC

/-- The central compact complex is the existing compact Kummer complex of the actual twist. -/
theorem compactCentralComplex_eq (G : GenuineKummerData K E₀ hZ) :
    compactCentralComplex G =
      compactKummerComplex G.S (centralCurve G) (centralFullTorsion G) := rfl

end TwistedCompact

section CentralCoefficients

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.TwistDictionary

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The central finite character is exactly the quadratic character. -/
theorem centralChar_apply (G : GenuineKummerData K E₀ hZ) (i : ℕ) (σ : GKS K G.S) :
    centralChar i G.s G.hs G.hs0 σ = intUnitsTo (Acoef i) (quadChar G.s G.hs G.hs0 σ) := by
  simp [centralChar, alphaChar, charMul_apply, movingCharS,
    ZInQ.Manuscript.RC.HeegnerAlgebra.movingChar]

/-- The actual Tate coefficient reduction, followed by the integral twist identification. -/
def centralCoefficientReductionAdd (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    TateS K G.S (twistK G.W (hZ : K)) →+
      Mcoef K G.S G.W i (centralChar i G.s G.hs G.hs0) :=
  (oneTmul (Acoef i) (centralChar i G.s G.hs G.hs0)
    (TorsS K G.S G.W ((2 ^ i : ℕ) : ℤ))).comp
      ((globalTwistTorsEquiv G.W G.s G.hs G.hs0 i).toAddMonoidHom.comp (projLev i))

/-- The coefficient reduction is semilinear for the constant reduction map. -/
theorem centralCoefficientReductionAdd_smul (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (a : ℤ_[2]) (P : TateS K G.S (twistK G.W (hZ : K))) :
    centralCoefficientReductionAdd G i (a • P) =
      constRed i a • centralCoefficientReductionAdd G i P := by
  have hp : projLev i (a • P) = resN i a • projLev i P := rfl
  simp only [centralCoefficientReductionAdd, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [hp, map_nsmul, map_nsmul]
  have hc : constRed i a = ((resN i a : ℕ) : Acoef i) := lamToAcoef_algebraMap i a
  rw [hc, Nat.cast_smul_eq_nsmul]

/-- The coefficient reduction as a semilinear map. -/
def centralCoefficientReduction (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    TateS K G.S (twistK G.W (hZ : K)) →ₛₗ[constRed i]
      Mcoef K G.S G.W i (centralChar i G.s G.hs G.hs0) where
  toFun := centralCoefficientReductionAdd G i
  map_add' := map_add _
  map_smul' := centralCoefficientReductionAdd_smul G i

/-- The central coefficient reduction is Galois equivariant. -/
theorem centralCoefficientReduction_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K G.S) (P : TateS K G.S (twistK G.W (hZ : K))) :
    centralCoefficientReduction G i (σ • P) = σ • centralCoefficientReduction G i P := by
  change centralCoefficientReductionAdd G i (σ • P) = σ • centralCoefficientReductionAdd G i P
  simp only [centralCoefficientReductionAdd, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [projLev_smul, globalTwistTorsEquiv_galois, map_zsmul]
  exact (smul_oneTmul (Acoef i) (centralChar i G.s G.hs G.hs0) _ σ _
    (quadChar G.s G.hs G.hs0 σ) (centralChar_apply G i σ)).symm

/-- The coefficient reduction is continuous for the inverse-limit topology. -/
theorem centralCoefficientReduction_continuous (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Continuous (centralCoefficientReduction G i) :=
  (continuous_of_discreteTopology (f := fun P : Lev K G.S (twistK G.W (hZ : K)) i =>
    oneTmul (Acoef i) (centralChar i G.s G.hs G.hs0) _
      (globalTwistTorsEquiv G.W G.s G.hs G.hs0 i P))).comp (continuous_projLev i)

/-- Inflation from a support to itself is the identity. -/
theorem inflMap_self {S : Set (HeightOneSpectrum (𝓞 K))} (σ : GKS K S) :
    inflMap K (subset_refl S) σ = σ := by
  change ZInQ.Contrib.CloudB3RC53.RankCounts.resUnr K (subset_refl S) (galS K S σ) = galS K S σ
  obtain ⟨τ, hτ⟩ := ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_surjective K S (galS K S σ)
  rw [← hτ]
  exact ZInQ.Contrib.CloudB3RC53.RankCounts.resUnr_comp K (subset_refl S) τ

end CentralCoefficients

section CoefficientMaps

variable {R S : Type} [CommRing R] [CommRing S]

/-- A coefficient-semilinear map of relation-indexed complexes. -/
structure CoefficientComplexMap (π : R →+* S) (A : GCx R) (B : GCx S) where
  f : (n : ℤ) → A.X n →ₛₗ[π] B.X n
  comm : ∀ (i j : ℤ) (hij : i + 1 = j) (a : A.X i),
    f j (A.d i j hij a) = B.d i j hij (f i a)

/-- A semilinear module map viewed as a linear map into restriction of scalars. -/
def semilinearRestriction (π : R →+* S) {M : ModuleCat R} {N : ModuleCat S}
    (f : M →ₛₗ[π] N) : M ⟶ (ModuleCat.restrictScalars π).obj N :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars π).obj N)
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smulₛₗ }

/-- Coefficient extension of a semilinear map of complexes.
The degreewise map sends `b ⊗ a` to `b • f(a)`. -/
def CoefficientComplexMap.extend {π : R →+* S} {A : GCx R} {B : GCx S}
    (f : CoefficientComplexMap π A B) : scalarChangedComplex π A.toCC ⟶ B.toCC where
  f n := ((ModuleCat.extendRestrictScalarsAdj π).homEquiv (A.X n) (B.X n)).symm
    (semilinearRestriction π (f.f n))
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let : Algebra R S := π.toAlgebra
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
      let b₀ : S := b
      change (B.toCC.d i j).hom (b₀ • f.f i a) = b₀ • f.f j ((A.toCC.d i j).hom a)
      rw [map_smul, GCx.toCC_d_hom A i j hij, GCx.toCC_d_hom B i j hij, f.comm]
    | add x y hx hy =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]

/-- The extended comparison acts on pure tensors by the original coefficient map. -/
theorem CoefficientComplexMap.extend_tmul {π : R →+* S} {A : GCx R} {B : GCx S}
    (f : CoefficientComplexMap π A B) (n : ℤ)
    (b : (ModuleCat.restrictScalars π).obj (ModuleCat.of S S)) (a : A.X n) :
    let b₀ : S := b
    (f.extend.f n).hom (b ⊗ₜ[R] a) = b₀ • f.f n a := rfl

/-- Products of coefficient comparisons give the comparison at the full Selmer support. -/
def CoefficientComplexMap.pi {π : R →+* S} {ι : Type} {A : ι → GCx R} {B : ι → GCx S}
    (f : ∀ v, CoefficientComplexMap π (A v) (B v)) :
    CoefficientComplexMap π (piCx A) (piCx B) where
  f n :=
    { toFun a v := (f v).f n (a v)
      map_add' a b := funext fun v => (f v).f n |>.map_add (a v) (b v)
      map_smul' c a := funext fun v => (f v).f n |>.map_smulₛₗ c (a v) }
  comm i j hij a := funext fun v => (f v).comm i j hij (a v)

/-- Compatible coefficient comparisons of the global, local, and condition complexes
induce the comparison of the genuine Selmer cones. -/
def CoefficientComplexMap.selmer {π : R →+* S} {D : SelData R} {D' : SelData S}
    (g : CoefficientComplexMap π D.G D'.G) (u : CoefficientComplexMap π D.U D'.U)
    (l : CoefficientComplexMap π D.L D'.L)
    (hres : ∀ (i j : ℤ) (hij : i = j) (a : D.G.X i),
      l.f j (D.res.f i j hij a) = D'.res.f i j hij (g.f i a))
    (hι : ∀ (i j : ℤ) (hij : i = j) (a : D.U.X i),
      l.f j (D.ι.f i j hij a) = D'.ι.f i j hij (u.f i a)) :
    CoefficientComplexMap π (selCx D) (selCx D') where
  f n :=
    { toFun a := (g.f n a.1, u.f n a.2.1, l.f (n - 1) a.2.2)
      map_add' a b := Prod.ext ((g.f n).map_add _ _)
        (Prod.ext ((u.f n).map_add _ _) ((l.f (n - 1)).map_add _ _))
      map_smul' c a := Prod.ext ((g.f n).map_smulₛₗ _ _)
        (Prod.ext ((u.f n).map_smulₛₗ _ _) ((l.f (n - 1)).map_smulₛₗ _ _)) }
  comm i j hij a := by
    obtain ⟨a, b, c⟩ := a
    apply Prod.ext
    · exact g.comm i j hij a
    · apply Prod.ext
      · exact u.comm i j hij b
      · change l.f (j - 1) (D.res.f i (j - 1) _ a - D.ι.f i (j - 1) _ b -
          D.L.d (i - 1) (j - 1) _ c) =
          D'.res.f i (j - 1) _ (g.f i a) - D'.ι.f i (j - 1) _ (u.f i b) -
            D'.L.d (i - 1) (j - 1) _ (l.f (i - 1) c)
        rw [map_sub, map_sub, hres, hι, l.comm]

end CoefficientMaps

section ContinuousCoefficientMaps

open ZInQ.Manuscript.RC.CoefModules

variable {R S : Type} [CommRing R] [CommRing S] {π : R →+* S}
  {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]
  {N : Type} [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul S N] [ContinuousSMul G N]

/-- Pointwise coefficient reduction of continuous cochains. -/
def cochainCoefficientMap (f : M →ₛₗ[π] N) (hfc : Continuous f) (n : ℕ) :
    contCochain R G M n →ₛₗ[π] contCochain S G N n where
  toFun c := ⟨(fun g => f (cfun c g) : (Fin n → G) → N), hfc.comp c.2⟩
  map_add' a b := Subtype.ext (funext fun g => f.map_add (cfun a g) (cfun b g))
  map_smul' a b := Subtype.ext (funext fun g => f.map_smulₛₗ a (cfun b g))

/-- Pointwise reduction commutes with the inhomogeneous cochain differential. -/
theorem cochainCoefficientMap_d (f : M →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) (n : ℕ) (c : contCochain R G M n) :
    cochainCoefficientMap f hfc (n + 1) (contD R G M n c) =
      contD S G N n (cochainCoefficientMap f hfc n c) := by
  apply Subtype.ext
  funext g
  change f (cfun (contD R G M n c) g) =
    cfun (contD S G N n (cochainCoefficientMap f hfc n c)) g
  have hdR : cfun (contD R G M n c) g =
      g 0 • cfun c (fun i => g i.succ) +
        ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • cfun c (Fin.contractNth j (· * ·) g) :=
    contCochains_d_apply (k := R) (G := G) (M := M) n c g
  have hdS : cfun (contD S G N n (cochainCoefficientMap f hfc n c)) g =
      g 0 • cfun (cochainCoefficientMap f hfc n c) (fun i => g i.succ) +
        ∑ j : Fin (n + 1), (-1 : S) ^ ((j : ℕ) + 1) •
          cfun (cochainCoefficientMap f hfc n c) (Fin.contractNth j (· * ·) g) :=
    contCochains_d_apply (k := S) (G := G) (M := N) n (cochainCoefficientMap f hfc n c) g
  rw [hdR, hdS]
  simp only [map_add, map_sum, LinearMap.map_smulₛₗ, map_pow, map_neg, map_one, hf]
  rfl

/-- The coefficient comparison of the full continuous cochain complexes. -/
def continuousCoefficientComplexMap (f : M →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) :
    CoefficientComplexMap π (natCx (contCochains R G M)) (natCx (contCochains S G N)) where
  f
    | .ofNat n => cochainCoefficientMap f hfc n
    | .negSucc _ => 0
  comm i j hij a := by
    cases i with
    | negSucc n =>
      cases j with
      | ofNat m =>
        change cochainCoefficientMap f hfc m 0 = 0
        exact (cochainCoefficientMap f hfc m).map_zero
      | negSucc m => rfl
    | ofNat n =>
      cases j with
      | negSucc m => exact absurd hij (ofNat_add_one_ne_negSucc n m)
      | ofNat m =>
        simp only [Int.ofNat_eq_natCast] at hij
        have hm : m = n + 1 := by omega
        subst m
        exact cochainCoefficientMap_d f hfc hf n a

/-- Reduction sends the continuous coboundaries into the finite-level coboundaries. -/
theorem cochainCoefficientMap_mem_B1 (f : M →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) (b : contCochain R G M 1)
    (hb : b ∈ contB1 R G M) : cochainCoefficientMap f hfc 1 b ∈ contB1 S G N := by
  obtain ⟨c, rfl⟩ := mem_contB1_iff b |>.1 hb
  exact (mem_contB1_iff _).2 ⟨cochainCoefficientMap f hfc 0 c,
    (cochainCoefficientMap_d f hfc hf 0 c).symm⟩

/-- A coefficient comparison restricts to cocycle conditions once the degree-one images lie
in the target Kummer condition. -/
def cocycleCoefficientComplexMap (f : M →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a)
    (Z : Submodule R (contCochain R G M 1)) (hZ : ∀ z ∈ Z, contD R G M 1 z = 0)
    (Z' : Submodule S (contCochain S G N 1)) (hZ' : ∀ z ∈ Z', contD S G N 1 z = 0)
    (hmem : ∀ z ∈ Z, cochainCoefficientMap f hfc 1 z ∈ Z' ⊔ contB1 S G N) :
    CoefficientComplexMap π (cocycleCondition Z hZ) (cocycleCondition Z' hZ') := by
  have hcond : ∀ (n : ℕ) (c : contCochain R G M n), c ∈ condP Z n →
      cochainCoefficientMap f hfc n c ∈ condP Z' n := by
    intro n c hc
    rcases n with _ | _ | n
    · trivial
    · obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hc
      rw [map_add]
      exact Submodule.add_mem _ (hmem z hz)
        (Submodule.mem_sup_right (cochainCoefficientMap_mem_B1 f hfc hf b hb))
    · have hc0 : c = 0 := (Submodule.mem_bot R).1 hc
      rw [hc0, map_zero]
      exact Submodule.zero_mem _
  refine { f := ?_, comm := ?_ }
  · intro n
    cases n with
    | negSucc n => exact 0
    | ofNat n =>
      exact
        { toFun a := ⟨cochainCoefficientMap f hfc n a.1, hcond n a.1 a.2⟩
          map_add' a b := Subtype.ext ((cochainCoefficientMap f hfc n).map_add _ _)
          map_smul' a b := Subtype.ext ((cochainCoefficientMap f hfc n).map_smulₛₗ _ _) }
  · intro i j hij a
    cases i with
    | negSucc n =>
      cases j with
      | ofNat m =>
        apply Subtype.ext
        change cochainCoefficientMap f hfc m 0 = 0
        exact (cochainCoefficientMap f hfc m).map_zero
      | negSucc m => rfl
    | ofNat n =>
      cases j with
      | negSucc m => exact absurd hij (ofNat_add_one_ne_negSucc n m)
      | ofNat m =>
        simp only [Int.ofNat_eq_natCast] at hij
        have hm : m = n + 1 := by omega
        subst m
        apply Subtype.ext
        have hR : (((condSubCx Z hZ).toCx.d n (n + 1)).hom a).1 =
            contD R G M n a.1 := SubCx.toCx_d_apply (condSubCx Z hZ) n a
        have hS : (((condSubCx Z' hZ').toCx.d n (n + 1)).hom
            ⟨cochainCoefficientMap f hfc n a.1, hcond n a.1 a.2⟩).1 =
            contD S G N n (cochainCoefficientMap f hfc n a.1) :=
          SubCx.toCx_d_apply (condSubCx Z' hZ') n _
        change cochainCoefficientMap f hfc (n + 1)
          (((condSubCx Z hZ).toCx.d n (n + 1)).hom a).1 = _
        rw [hR]
        exact (cochainCoefficientMap_d f hfc hf n a.1).trans hS.symm

end ContinuousCoefficientMaps

section GenuineReduction

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Manuscript.RC53Assist.CentralKummer

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The coefficient module used by the genuine central finite Selmer data. -/
abbrev finiteCentralModule (G : GenuineKummerData K E₀ hZ) (i : ℕ) : Type :=
  MinS (subset_refl G.S) G.W i (centralChar i G.s G.hs G.hs0)

/-- The central coefficient reduction in the precise inflated-module conventions. -/
def inflatedCoefficientReduction (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    TateS K G.S (centralCurve G) →ₛₗ[constRed i] finiteCentralModule G i where
  toFun := centralCoefficientReduction G i
  map_add' := (centralCoefficientReduction G i).map_add
  map_smul' := (centralCoefficientReduction G i).map_smulₛₗ

/-- Inflation to the same support does not change equivariance of the coefficient reduction. -/
theorem inflatedCoefficientReduction_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K G.S) (P : TateS K G.S (centralCurve G)) :
    inflatedCoefficientReduction G i (σ • P) = σ • inflatedCoefficientReduction G i P := by
  change centralCoefficientReduction G i (σ • P) =
    inflMap K (subset_refl G.S) σ • centralCoefficientReduction G i P
  rw [inflMap_self, centralCoefficientReduction_galois]

/-- The inflated coefficient reduction is continuous. -/
theorem inflatedCoefficientReduction_continuous (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Continuous (inflatedCoefficientReduction G i) := centralCoefficientReduction_continuous G i

/-- The same coefficient reduction restricted to a decomposition group. -/
def localCoefficientReduction (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S) :
    ResMod (locMap K G.S v.1) (TateS K G.S (centralCurve G)) →ₛₗ[constRed i]
      ResMod (locMap K G.S v.1) (finiteCentralModule G i) where
  toFun := inflatedCoefficientReduction G i
  map_add' := (inflatedCoefficientReduction G i).map_add
  map_smul' := (inflatedCoefficientReduction G i).map_smulₛₗ

/-- The local reduction is equivariant for the actual localization map. -/
theorem localCoefficientReduction_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K G.S) (σ : Gloc K v.1)
    (P : ResMod (locMap K G.S v.1) (TateS K G.S (centralCurve G))) :
    localCoefficientReduction G i v (σ • P) = σ • localCoefficientReduction G i v P :=
  inflatedCoefficientReduction_galois G i (locMap K G.S v.1 σ) P

/-- The local reduction is continuous. -/
theorem localCoefficientReduction_continuous (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K G.S) : Continuous (localCoefficientReduction G i v) :=
  inflatedCoefficientReduction_continuous G i

/-- The finite central local Kummer cocycle submodule in the genuine coefficient module. -/
def finiteCentralZ (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S) :
    Submodule (Acoef i) (contCochain (Acoef i) (Gloc K v.1)
      (ResMod (locMap K G.S v.1) (finiteCentralModule G i)) 1) := by
  classical
  haveI := isElliptic_localTwist G.W (ne_zero_of_sqrt G.s G.hs G.hs0) v.1
  exact kummerZ' (Acoef i)
    (kummerIotaS (subset_refl G.S) G.W i G.s G.hs G.hs0
      (centralChar i G.s G.hs G.hs0) (G.hFull i) v)

/-- The finite central Kummer submodule consists of cocycles. -/
theorem finiteCentralZ_cocycle (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S) :
    ∀ z ∈ finiteCentralZ G i v,
      contD (Acoef i) (Gloc K v.1) (ResMod (locMap K G.S v.1) (finiteCentralModule G i)) 1 z = 0 := by
  classical
  have := isElliptic_localTwist G.W (ne_zero_of_sqrt G.s G.hs G.hs0) v.1
  exact kummerZ'_cocycle _ _
    (kummerIotaS_smul (subset_refl G.S) G.W i G.s G.hs G.hs0
      (centralChar i G.s G.hs G.hs0) (G.hFull i) v (isLocallyQuadAt_centralChar _ _ _ _ _))

open scoped Classical in
/-- Local compatibility needed to restrict the actual coefficient projection to Kummer conditions.
This is a statement about images of integral Kummer cocycles, not about Selmer orders. -/
structure CentralReductionCompatibility (G : GenuineKummerData K E₀ hZ) : Prop where
  generator_mem : ∀ (i : ℕ) (v : Places K G.S)
    (P : ((centralCurve G).baseChange (v.1.adicCompletion K)).toAffine.Point),
    cochainCoefficientMap (localCoefficientReduction G i v)
      (localCoefficientReduction_continuous G i v) 1
        (tateKummerCocycle (centralCurve G) (centralFullTorsion G) v.1 P) ∈
      finiteCentralZ G i v ⊔
        contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K G.S v.1) (finiteCentralModule G i))

open scoped Classical in
/-- The degree-one compatibility extends from Kummer generators to their entire integral span. -/
theorem CentralReductionCompatibility.span_mem (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (i : ℕ) (v : Places K G.S) :
    ∀ z ∈ tateKummerZ (centralCurve G) (centralFullTorsion G) v.1,
      cochainCoefficientMap (localCoefficientReduction G i v)
        (localCoefficientReduction_continuous G i v) 1 z ∈
      finiteCentralZ G i v ⊔
        contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K G.S v.1) (finiteCentralModule G i)) := by
  classical
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨P, rfl⟩ := hz
    exact H.generator_mem i v P
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hb

/-- The genuine finite Selmer data, with the redundant support conditionals removed. -/
def simpleCentralSelData (G : GenuineKummerData K E₀ hZ) (i : ℕ) : SelData (Acoef i) := by
  classical
  letI := acoefTop i
  haveI := acoefTop_discrete i
  exact galoisSelData K G.S (Acoef i) (finiteCentralModule G i)
    (ofCondAt K G.S (Acoef i) (finiteCentralModule G i) (fun v =>
      actualKummerAtS (subset_refl G.S) G.W i G.s G.hs G.hs0
        (centralChar i G.s G.hs G.hs0) (G.hFull i) v
          (isLocallyQuadAt_centralChar _ _ _ _ _)))

/-- Removing the support conditionals does not replace the genuine finite-level complexes. -/
theorem simpleCentralSelData_eq (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    simpleCentralSelData G i = centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i := by
  classical
  simp only [simpleCentralSelData, centralKummerSelData, kummerSelData, actualSelData,
    actualConditions]
  congr 1
  apply congrArg (ofCondAt K G.S (Acoef i) (finiteCentralModule G i))
  funext v
  simp [urOutside, v.2]

/-- The coefficient comparison on the full local cochains. -/
def fullLocalCoefficientMap (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S) :
    CoefficientComplexMap (constRed i)
      (locAt K G.S ℤ_[2] (TateS K G.S (centralCurve G)) v)
      (locAt K G.S (Acoef i) (finiteCentralModule G i) v) :=
  continuousCoefficientComplexMap (localCoefficientReduction G i v)
    (localCoefficientReduction_continuous G i v) (localCoefficientReduction_galois G i v)

open scoped Classical in
/-- The coefficient comparison on the actual local Kummer conditions. -/
def kummerLocalCoefficientMap (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (i : ℕ) (v : Places K G.S) :
    CoefficientComplexMap (constRed i)
      (tateKummerCondition (centralCurve G) (centralFullTorsion G) v.1)
      (actualKummerAtS (subset_refl G.S) G.W i G.s G.hs G.hs0
        (centralChar i G.s G.hs G.hs0) (G.hFull i) v
          (isLocallyQuadAt_centralChar _ _ _ _ _)).U := by
  classical
  exact cocycleCoefficientComplexMap (localCoefficientReduction G i v)
    (localCoefficientReduction_continuous G i v) (localCoefficientReduction_galois G i v)
    (tateKummerZ (centralCurve G) (centralFullTorsion G) v.1)
    (tateKummerZ_cocycle (centralCurve G) (centralFullTorsion G) v.1)
    (finiteCentralZ G i v) (finiteCentralZ_cocycle G i v) (H.span_mem G i v)

/-- The comparison of Selmer cones induced by the actual coefficient projections. -/
def centralCoefficientComplexMap (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (i : ℕ) :
    CoefficientComplexMap (constRed i) (selCx (compactCentralSelData G))
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)) := by
  classical
  let g : CoefficientComplexMap (constRed i) (compactCentralSelData G).G (simpleCentralSelData G i).G :=
    continuousCoefficientComplexMap (inflatedCoefficientReduction G i)
      (inflatedCoefficientReduction_continuous G i) (inflatedCoefficientReduction_galois G i)
  let l : CoefficientComplexMap (constRed i) (compactCentralSelData G).L (simpleCentralSelData G i).L :=
    CoefficientComplexMap.pi (fullLocalCoefficientMap G i)
  let u : CoefficientComplexMap (constRed i) (compactCentralSelData G).U (simpleCentralSelData G i).U :=
    CoefficientComplexMap.pi (kummerLocalCoefficientMap G H i)
  have hres : ∀ (a b : ℤ) (hab : a = b) (x : (compactCentralSelData G).G.X a),
      l.f b ((compactCentralSelData G).res.f a b hab x) =
        (simpleCentralSelData G i).res.f a b hab (g.f a x) := by
    intro a b hab x
    subst hab
    funext v
    cases a <;> rfl
  have hι : ∀ (a b : ℤ) (hab : a = b) (x : (compactCentralSelData G).U.X a),
      l.f b ((compactCentralSelData G).ι.f a b hab x) =
        (simpleCentralSelData G i).ι.f a b hab (u.f a x) := by
    intro a b hab x
    subst hab
    funext v
    cases a <;> rfl
  have f := CoefficientComplexMap.selmer g u l hres hι
  simpa only [simpleCentralSelData_eq] using f

/-- The genuine finite-level comparison from coefficient extension of the compact central complex. -/
def centralReductionMap (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (i : ℕ) :
    scalarChangedComplex (constRed i) (compactCentralComplex G) ⟶
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC :=
  (centralCoefficientComplexMap G H i).extend

/-- The cohomology identification induced by the actual reduction map, when it is a quasi-isomorphism. -/
def centralReductionHomologyIso (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (i : ℕ) [QuasiIso (centralReductionMap G H i)] (n : ℤ) :
    (scalarChangedComplex (constRed i) (compactCentralComplex G)).homology n ≅ G.selH i n :=
  asIso (HomologicalComplex.homologyMap (centralReductionMap G H i) n)

end GenuineReduction

section IntegralComparison

open NumberField IsDedekindDomain Matrix

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- An integral retained-basis model of the compact central complex, with its actual finite
coefficient comparisons. After integral cancellation the core has one free line in each of
degrees one and two. No cohomology order occurs in this input.

The integral quasi-isomorphism and the quasi-isomorphism of its canonical finite coefficient
comparison are the remaining comparison input. The latter must not be inferred merely from
rational base change or from reduction of individual Kummer cocycles. -/
structure IntegralCentralModel (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (x₁ x₂ x₃ : ℤ_[2]) where
  P : CochainComplex (ModuleCat ℤ_[2]) ℤ
  coordinates : (n : ℤ) → P.X n ≃ₗ[ℤ_[2]] (Fin (normalRank n) → ℤ_[2])
  normalization : normalComplex x₁ x₂ x₃ ≅ P
  comparison : P ⟶ compactCentralComplex G
  quasi_iso : QuasiIso comparison
  fibre_quasi_iso : ∀ i : ℕ, i ≠ 0 →
    QuasiIso (((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      comparison ≫ centralReductionMap G H i)
  disk1_ne_zero : x₁ ≠ 0
  disk2_ne_zero : x₂ ≠ 0
  disk3_ne_zero : x₃ ≠ 0

namespace IntegralCentralModel

variable {G : GenuineKummerData K E₀ hZ} {H : CentralReductionCompatibility G}
  {x₁ x₂ x₃ : ℤ_[2]}

/-- The actual change from the normal-form basis to the retained integral basis. -/
def basisComparison (M : IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
    (Fin (normalRank n) → ℤ_[2]) ≃ₗ[ℤ_[2]] (Fin (normalRank n) → ℤ_[2]) :=
  (normalCoordinates x₁ x₂ x₃ n).symm.trans
    ((HomologicalComplex.Hom.isoApp M.normalization n).toLinearEquiv.trans (M.coordinates n))

/-- The degreewise determinant-basis comparison, as an integral matrix. -/
def basisMatrix (M : IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
    Matrix (Fin (normalRank n)) (Fin (normalRank n)) ℤ_[2] :=
  LinearMap.toMatrix (Pi.basisFun ℤ_[2] _) (Pi.basisFun ℤ_[2] _)
    (M.basisComparison n).toLinearMap

/-- The determinant comparison is unimodular over the integers, not merely invertible rationally. -/
theorem basisMatrix_isUnit_det (M : IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
    IsUnit (M.basisMatrix n).det :=
  LinearEquiv.isUnit_det (M.basisComparison n) (Pi.basisFun ℤ_[2] _) (Pi.basisFun ℤ_[2] _)

/-- Every retained-basis determinant factor has central valuation zero. -/
theorem basisMatrix_valuation (M : IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
    (M.basisMatrix n).det.valuation = 0 := by
  obtain ⟨u, hu⟩ := M.basisMatrix_isUnit_det n
  rw [← hu]
  exact valuation_unit_padicInt u

/-- The canonical finite coefficient comparison of the retained integral model. -/
def fibreMap (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) :
    scalarChangedComplex (constRed i) M.P ⟶
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC :=
  ((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    M.comparison ≫ centralReductionMap G H i

/-- The comparison from the reduced core-and-disks normal form to the genuine finite complex. -/
def finiteComparison (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) :
    normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃) ⟶
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC :=
  (normalScalarChangeIso (constRed i) x₁ x₂ x₃).inv ≫
    ((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      M.normalization.hom ≫ M.fibreMap i

/-- The constructed finite comparison is a quasi-isomorphism under the integral model input. -/
theorem finiteComparison_quasiIso (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) :
    QuasiIso (M.finiteComparison i) := by
  have : QuasiIso (M.fibreMap i) := M.fibre_quasi_iso i hi
  dsimp only [finiteComparison]
  infer_instance

/-- All finite-level cohomology groups are identified by the constructed complex comparison. -/
def finiteHomologyIso (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) (n : ℤ) :
    (normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology n ≅ G.selH i n := by
  haveI := M.finiteComparison_quasiIso i hi
  exact asIso (HomologicalComplex.homologyMap (M.finiteComparison i) n)

/-- The three orders are calculated from the genuine finite-level complexes, not assumed. -/
theorem finite_orders (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) :
    Nat.card (G.selH i 0) = cycOrder i x₁ ∧
      Nat.card (G.selH i 2) = 2 ^ (i * i) * cycOrder i x₂ * cycOrder i x₃ ∧
      Nat.card (G.selH i 3) = cycOrder i x₃ := by
  obtain ⟨h0, h2, h3⟩ := finiteNormal_orders i hi x₁ x₂ x₃
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.card_congr (M.finiteHomologyIso i hi 0).toLinearEquiv.toEquiv.symm).trans h0
  · exact (Nat.card_congr (M.finiteHomologyIso i hi 2).toLinearEquiv.toEquiv.symm).trans h2
  · exact (Nat.card_congr (M.finiteHomologyIso i hi 3).toLinearEquiv.toEquiv.symm).trans h3

/-- The calibration order tie follows from the integral central model and its actual reduction. -/
theorem diskTie (M : IntegralCentralModel G H x₁ x₂ x₃) : DiskTie G x₁ x₂ x₃ where
  tie0 := ⟨1, fun i hi => (M.finite_orders i (by omega)).1⟩
  tie2 := ⟨1, fun i hi => (M.finite_orders i (by omega)).2.1⟩
  tie3 := ⟨1, fun i hi => (M.finite_orders i (by omega)).2.2⟩

/-- The arithmetic disk valuations follow once the separate arithmetic-order input is supplied. -/
theorem disk_valuations (M : IntegralCentralModel G H x₁ x₂ x₃) {tA shaA : ℕ}
    (A : DiskArith G tA shaA) :
    x₁.valuation = padicValNat 2 tA ∧ x₂.valuation = padicValNat 2 shaA ∧
      x₃.valuation = padicValNat 2 tA :=
  M.diskTie.valuations A M.disk1_ne_zero M.disk2_ne_zero M.disk3_ne_zero

end IntegralCentralModel

end IntegralComparison

section CalibrationBlock

open NumberField IsDedekindDomain Matrix
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Torsion

/-- The existing calibration block with its order tie replaced by the integral model comparison.
The rational identification, coordinate transfer, free coefficients, and arithmetic orders
remain separate inputs. -/
def kummerCoordinateBlockOfIntegralModel {K : Type} [Field K] [NumberField K]
    {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {j vL m : ℤ} {tA shaA : ℕ}
    (S : Set (HeightOneSpectrum (𝓞 K))) (hSfin : S.Finite)
    (M : Type) [AddCommGroup M] [Module (PowerSeries ℚ_[2]) M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul (PowerSeries ℚ_[2]) M] [ContinuousSMul (GKS K S) M]
    (Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M)
    (hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl))
    (I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ)
    (link : Central.IsClassFunctionalCoord DK zK wK I.coord)
    (aP bP : PowerSeries ℚ_[2])
    (ha : I.a = PowerSeries.C (m : ℚ_[2]) * aP)
    (hb : I.b = PowerSeries.C (m : ℚ_[2]) * bP)
    (haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ))
    (hbP : v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ))
    (hu₀ : v2 (central I.u₀) = 0)
    (G : GenuineKummerData K E₀ hZ) (x₁ x₂ x₃ : ℤ_[2])
    (hx₁ : central (I.δ₁ : PowerSeries ℚ_[2]) = x₁)
    (hx₂ : central (I.δ₂ : PowerSeries ℚ_[2]) = x₂)
    (hx₃ : central (I.δ₃ : PowerSeries ℚ_[2]) = x₃)
    (H : CentralReductionCompatibility G) (J : IntegralCentralModel G H x₁ x₂ x₃)
    (A : DiskArith G tA shaA) : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA where
  S := S
  hSfin := hSfin
  M := M
  Δ := Δ
  hinj := hinj
  I := I
  link := link
  aP := aP
  bP := bP
  ha := ha
  hb := hb
  haP := haP
  hbP := hbP
  hu₀ := hu₀
  G := G
  x₁ := x₁
  x₂ := x₂
  x₃ := x₃
  hx₁ := hx₁
  hx₂ := hx₂
  hx₃ := hx₃
  tie := J.diskTie
  arith := A

end CalibrationBlock

section LocalTwistNaturality

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.TwistDictionary

/-- Transport of geometric points along equality of curves. -/
def pointCurveCast {F : Type} [Field F] {B B' : WeierstrassCurve F} (e : B = B') :
    PtAlg F B ≃+ PtAlg F B' :=
  AddEquiv.cast (M := fun V : WeierstrassCurve F => PtAlg F V) e

/-- Transport of finite torsion along equality of curves. -/
def torsionCurveCast {F : Type} [Field F] {B B' : WeierstrassCurve F} (e : B = B') (n : ℕ) :
    TorsAlg F B n ≃+ TorsAlg F B' n :=
  AddEquiv.cast (M := fun V : WeierstrassCurve F => TorsAlg F V n) e

/-- Curve transport retains the coordinates of geometric points. -/
theorem pointCurveCast_some {F : Type} [Field F] {B B' : WeierstrassCurve F} (e : B = B')
    {x y : AlgebraicClosure F} (hxy : (B.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
    pointCurveCast e (ptEquiv F B (.some x y hxy)) =
      ptEquiv F B' (.some x y (e ▸ hxy)) := by
  cases e
  rfl

/-- Curve transport of torsion agrees with curve transport of its underlying point. -/
theorem torsionCurveCast_coe {F : Type} [Field F] {B B' : WeierstrassCurve F} (e : B = B')
    (n : ℕ) (P : TorsAlg F B n) :
    (torsionCurveCast e n P : PtAlg F B') = pointCurveCast e (P : PtAlg F B) := by
  cases e
  rfl

open scoped Classical in
/-- The global quadratic-twist identification commutes with the fixed decomposition embedding. -/
theorem globalTwistPointEquiv_compPt {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (P : ((twistK W h).baseChange (KS K S)).toAffine.Point) :
    compPt W v (globalTwistPointEquiv W s hs hs0 P) =
      twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
        two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
          (pointCurveCast (localTwist_eq_baseChange W h v).symm (compPt (twistK W h) v P)) := by
  classical
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def]
    simp only [map_zero]
  · rw [globalTwistPointEquiv_some, compPt_some, compPt_some, pointCurveCast_some, twistPt_some']
    congr 1
    simp only [Affine.Point.some.injEq]
    have h1 : embS K S v ((W.baseChange (KS K S)).a₁) =
        ((W.baseChange (v.adicCompletion K)).baseChange (AlgebraicClosure (v.adicCompletion K))).a₁ :=
      (embS K S v).commutes W.a₁
    have h3 : embS K S v ((W.baseChange (KS K S)).a₃) =
        ((W.baseChange (v.adicCompletion K)).baseChange (AlgebraicClosure (v.adicCompletion K))).a₃ :=
      (embS K S v).commutes W.a₃
    constructor
    · simp only [localSqrt, map_mul, map_pow, map_inv₀]
    · simp only [localSqrt, map_add, map_mul, map_pow, map_inv₀, map_div₀,
        map_neg, map_ofNat, h1, h3, sub_eq_add_neg, neg_div]
      rfl

open scoped Classical in
/-- The corresponding finite-torsion square commutes. -/
theorem globalTwistTorsEquiv_compTors {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (i : ℕ)
    (P : TorsS K S (twistK W h) ((2 ^ i : ℕ) : ℤ)) :
    compTors W (2 ^ i) v (globalTwistTorsEquiv W s hs hs0 i P) =
      twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
        two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) (2 ^ i)
          (torsionCurveCast (localTwist_eq_baseChange W h v).symm (2 ^ i)
            (compTors (twistK W h) (2 ^ i) v P)) := by
  classical
  apply Subtype.ext
  change compPt W v (globalTwistPointEquiv W s hs hs0 P.1) =
    twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
        (torsionCurveCast (localTwist_eq_baseChange W h v).symm (2 ^ i)
          (compTors (twistK W h) (2 ^ i) v P) : PtAlg _ _)
  rw [torsionCurveCast_coe, coe_compTors]
  exact globalTwistPointEquiv_compPt W s hs hs0 v P.1

end LocalTwistNaturality

section KummerPushforward

open WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
  {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m]
  {A : Type} [CommRing A] {N : Type} [AddCommGroup N] [Module A N]
  [DistribMulAction (Field.absoluteGaloisGroup F) N]
  [SMulCommClass (Field.absoluteGaloisGroup F) A N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul (Field.absoluteGaloisGroup F) N]

/-- An additive coefficient map as a semilinear map from the integer coefficients. -/
def integerCoefficientMap (ι : TorsAlg F B m →+ N) : TorsAlg F B m →ₛₗ[Int.castRingHom A] N where
  toFun := ι
  map_add' := ι.map_add
  map_smul' a b := by
    change ι (a • b) = (a : A) • ι b
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

omit [CharZero F] [DecidableEq F] [B.IsElliptic] [NeZero m]
  [DistribMulAction (Field.absoluteGaloisGroup F) N]
  [SMulCommClass (Field.absoluteGaloisGroup F) A N]
  [DiscreteTopology N] [ContinuousSMul (Field.absoluteGaloisGroup F) N] in
/-- An additive coefficient map on finite torsion is continuous. -/
theorem integerCoefficientMap_continuous (ι : TorsAlg F B m →+ N) :
    Continuous (integerCoefficientMap (A := A) ι) := continuous_of_discreteTopology

/-- Push-forward of any finite Kummer cocycle lies in the actual extended Kummer condition. -/
theorem kummerCocycleOf_pushforward_mem (ι : TorsAlg F B m →+ N)
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (a : TorsAlg F B m), ι (σ • a) = σ • ι a)
    {P : B.toAffine.Point} {Q : PtAlg F B} (hQ : m • Q = basePt F B P) :
    cochainCoefficientMap (integerCoefficientMap (A := A) ι) (integerCoefficientMap_continuous (A := A) ι) 1
      (kummerCocycleOf F B m hQ) ∈
        kummerZ' A ι ⊔ contB1 A (Field.absoluteGaloisGroup F) N := by
  have hspan : ∀ z ∈ kummerZ F B m,
      cochainCoefficientMap (integerCoefficientMap (A := A) ι) (integerCoefficientMap_continuous (A := A) ι) 1 z ∈
        kummerZ' A ι ⊔ contB1 A (Field.absoluteGaloisGroup F) N := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨P, rfl⟩ := hz
      have heq : cochainCoefficientMap (integerCoefficientMap (A := A) ι)
          (integerCoefficientMap_continuous (A := A) ι) 1 (kummerCocycle F B m P) =
            kummerCocycleIn ι (1 : A) P := by
        apply Subtype.ext
        funext g
        change ι (kummerFun F B m P (g 0)) = (1 : A) • ι (kummerFun F B m P (g 0))
        rw [one_smul]
      rw [heq]
      exact Submodule.mem_sup_left (kummerCocycleIn_mem ι 1 P)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hb
  obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.1 (kummerCocycleOf_mem_sup F B m hQ)
  rw [← hzb, map_add]
  exact Submodule.add_mem _ (hspan z hz)
    (Submodule.mem_sup_right (cochainCoefficientMap_mem_B1 (integerCoefficientMap (A := A) ι)
      (integerCoefficientMap_continuous (A := A) ι) hι b hb))

omit [CharZero F] [DecidableEq F] [B.IsElliptic] in
/-- Transport of curve equality is compatible with the Galois action on finite torsion. -/
theorem torsionCurveCast_galois {B' : WeierstrassCurve F} (e : B = B') (n : ℕ)
    (σ : Field.absoluteGaloisGroup F) (P : TorsAlg F B n) :
    torsionCurveCast e n (σ • P) = σ • torsionCurveCast e n P := by
  cases e
  rfl

omit [ContinuousSMul (Field.absoluteGaloisGroup F) N] in
/-- The Kummer cocycle span is unchanged by transporting its source curve along equality. -/
theorem kummerZ'_curveCast {B' : WeierstrassCurve F} [B'.IsElliptic] (e : B = B')
    (ι : TorsAlg F B' m →+ N) :
    kummerZ' A (ι.comp (torsionCurveCast e m).toAddMonoidHom) = kummerZ' A ι := by
  cases e
  rfl

end KummerPushforward

section ProvenCentralReduction

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Manuscript.RC53Assist.CentralKummer

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The actual local finite coefficient map with its source written as the base change
of the global central twist. -/
def localTwistIota (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S) :
    TorsAlg (v.1.adicCompletion K) ((centralCurve G).baseChange (v.1.adicCompletion K)) (2 ^ i) →+
      ResMod (locMap K G.S v.1) (finiteCentralModule G i) :=
  (kummerIotaS (subset_refl G.S) G.W i G.s G.hs G.hs0
    (centralChar i G.s G.hs G.hs0) (G.hFull i) v).comp
      (torsionCurveCast (localTwist_eq_baseChange G.W (hZ : K) v.1).symm (2 ^ i)).toAddMonoidHom

/-- The local coefficient map remains equivariant after the curve transport. -/
theorem localTwistIota_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S)
    (σ : Gloc K v.1)
    (P : TorsAlg (v.1.adicCompletion K) ((centralCurve G).baseChange (v.1.adicCompletion K)) (2 ^ i)) :
    localTwistIota G i v (σ • P) = σ • localTwistIota G i v P := by
  classical
  simp only [localTwistIota, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    torsionCurveCast_galois]
  exact kummerIotaS_smul (subset_refl G.S) G.W i G.s G.hs G.hs0
    (centralChar i G.s G.hs G.hs0) (G.hFull i) v (isLocallyQuadAt_centralChar _ _ _ _ _) σ _

open scoped Classical in
/-- The global Tate projection and the actual local Kummer coefficient map agree
through the fixed decomposition comparisons. -/
theorem localCoefficientReduction_eq (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S)
    (P : ResMod (locMap K G.S v.1) (TateS K G.S (centralCurve G))) :
    localCoefficientReduction G i v P =
      localTwistIota G i v (compTors (centralCurve G) (2 ^ i) v.1 (projLev i P)) := by
  classical
  let Q : Lev K G.S (centralCurve G) i := projLev i P
  have hQ : globalTwistTorsEquiv G.W G.s G.hs G.hs0 i Q =
      (compTorsEquiv G.W (2 ^ i) (G.hFull i) v.1).symm
        (twistTors (G.W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) (hZ : K))
          two_ne_zero (localSqrt_ne_zero G.s G.hs0 v.1) (localSqrt_sq G.s G.hs v.1) (2 ^ i)
            (torsionCurveCast (localTwist_eq_baseChange G.W (hZ : K) v.1).symm (2 ^ i)
              (compTors (centralCurve G) (2 ^ i) v.1 Q))) := by
    apply (compTorsEquiv G.W (2 ^ i) (G.hFull i) v.1).injective
    rw [AddEquiv.apply_symm_apply]
    exact globalTwistTorsEquiv_compTors G.W G.s G.hs G.hs0 v.1 i Q
  change oneTmul (Acoef i) (centralChar i G.s G.hs G.hs0) _
      (globalTwistTorsEquiv G.W G.s G.hs G.hs0 i Q) = _
  rw [hQ]
  rfl

open scoped Classical in
/-- The reduction of an integral Kummer cocycle is the finite Kummer cocycle of the
same division tower, pushed forward by the genuine local coefficient map. -/
theorem localCoefficientReduction_tateKummer (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S)
    (P : ((centralCurve G).baseChange (v.1.adicCompletion K)).toAffine.Point) :
    cochainCoefficientMap (localCoefficientReduction G i v)
      (localCoefficientReduction_continuous G i v) 1
        (tateKummerCocycle (centralCurve G) (centralFullTorsion G) v.1 P) =
      cochainCoefficientMap (integerCoefficientMap (A := Acoef i) (localTwistIota G i v))
        (integerCoefficientMap_continuous (A := Acoef i) (localTwistIota G i v)) 1
          (kummerCocycleOf (v.1.adicCompletion K) ((centralCurve G).baseChange (v.1.adicCompletion K))
            (2 ^ i) ((isDivTower_divTower _ _ P).two_pow_smul i)) := by
  classical
  apply Subtype.ext
  funext g
  change localCoefficientReduction G i v
      (tateKummerFunOf (centralCurve G) (centralFullTorsion G) v.1
        (isDivTower_divTower _ _ P) (g 0)) =
    localTwistIota G i v (kummerFunOf (v.1.adicCompletion K)
      ((centralCurve G).baseChange (v.1.adicCompletion K)) (2 ^ i)
        ((isDivTower_divTower _ _ P).two_pow_smul i) (g 0))
  rw [localCoefficientReduction_eq]
  exact congrArg (localTwistIota G i v)
    (compTors_tateKummerFunOf (centralCurve G) (centralFullTorsion G) v.1
      (isDivTower_divTower _ _ P) (g 0) i)

open scoped Classical in
/-- The local generator compatibility is proved for every genuine central datum. -/
theorem centralReductionCompatibility (G : GenuineKummerData K E₀ hZ) : CentralReductionCompatibility G where
  generator_mem i v P := by
    classical
    have := isElliptic_localTwist G.W (ne_zero_of_sqrt G.s G.hs G.hs0) v.1
    have hZ : kummerZ' (Acoef i) (localTwistIota G i v) = finiteCentralZ G i v := by
      exact kummerZ'_curveCast (A := Acoef i)
        (localTwist_eq_baseChange G.W (hZ : K) v.1).symm
          (kummerIotaS (subset_refl G.S) G.W i G.s G.hs G.hs0
            (centralChar i G.s G.hs G.hs0) (G.hFull i) v)
    rw [localCoefficientReduction_tateKummer]
    have hmem := kummerCocycleOf_pushforward_mem (A := Acoef i) (localTwistIota G i v)
      (localTwistIota_galois G i v) ((isDivTower_divTower _ _ P).two_pow_smul i)
    simpa only [hZ] using hmem

/-- The finite-level comparison with local Kummer compatibility no longer an input. -/
def canonicalCentralReductionMap (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    scalarChangedComplex (constRed i) (compactCentralComplex G) ⟶
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC :=
  centralReductionMap G (centralReductionCompatibility G) i

/-- The only remaining comparison datum uses the proved local reduction compatibility. -/
abbrev CanonicalIntegralCentralModel (G : GenuineKummerData K E₀ hZ) (x₁ x₂ x₃ : ℤ_[2]) :=
  IntegralCentralModel G (centralReductionCompatibility G) x₁ x₂ x₃

/-- The calibration order tie from the remaining integral retained-basis comparison alone. -/
theorem diskTie_of_integralCentralModel (G : GenuineKummerData K E₀ hZ) (x₁ x₂ x₃ : ℤ_[2])
    (M : CanonicalIntegralCentralModel G x₁ x₂ x₃) : DiskTie G x₁ x₂ x₃ := M.diskTie

end ProvenCentralReduction

section MatrixDisks

open Matrix

variable {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}

/-- The four terms of a core with three finite-free matrix disks. -/
def blockTerms (R : Type) [CommRing R] (m₁ m₂ m₃ : ℕ) : ℕ → ModuleCat R
  | 0 => ModuleCat.of R (Fin m₁ → R)
  | 1 => ModuleCat.of R (R × (Fin m₁ → R) × (Fin m₂ → R))
  | 2 => ModuleCat.of R (R × (Fin m₂ → R) × (Fin m₃ → R))
  | 3 => ModuleCat.of R (Fin m₃ → R)
  | _ + 4 => ModuleCat.of R PUnit

/-- The first matrix disk differential. -/
def blockD0 (B : Matrix (Fin m₁) (Fin m₁) R) :
    (Fin m₁ → R) →ₗ[R] (R × (Fin m₁ → R) × (Fin m₂ → R)) :=
  (0 : (Fin m₁ → R) →ₗ[R] R).prod (B.mulVecLin.prod 0)

/-- The middle matrix disk differential. -/
def blockD1 (B : Matrix (Fin m₂) (Fin m₂) R) :
    (R × (Fin m₁ → R) × (Fin m₂ → R)) →ₗ[R] (R × (Fin m₂ → R) × (Fin m₃ → R)) :=
  (0 : (R × (Fin m₁ → R) × (Fin m₂ → R)) →ₗ[R] R).prod
    ((B.mulVecLin.comp ((LinearMap.snd R _ _).comp (LinearMap.snd R _ _))).prod 0)

/-- The last matrix disk differential. -/
def blockD2 (B : Matrix (Fin m₃) (Fin m₃) R) :
    (R × (Fin m₂ → R) × (Fin m₃ → R)) →ₗ[R] (Fin m₃ → R) :=
  B.mulVecLin.comp ((LinearMap.snd R _ _).comp (LinearMap.snd R _ _))

/-- The matrix-disk differentials in the retained bases. -/
def blockD (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    (n : ℕ) → blockTerms R m₁ m₂ m₃ n ⟶ blockTerms R m₁ m₂ m₃ (n + 1)
  | 0 => ModuleCat.ofHom (blockD0 B₁)
  | 1 => ModuleCat.ofHom (blockD1 B₂)
  | 2 => ModuleCat.ofHom (blockD2 B₃)
  | _ + 3 => 0

/-- Consecutive matrix-disk differentials compose to zero. -/
theorem blockD_sq (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℕ) :
    blockD B₁ B₂ B₃ n ≫ blockD B₁ B₂ B₃ (n + 1) = 0 := by
  rcases n with _ | _ | _ | n
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (0, B₂.mulVecLin 0, 0) = (0 : R × (Fin m₂ → R) × (Fin m₃ → R))
    simp only [map_zero]
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change B₃.mulVecLin 0 = 0
    exact map_zero _
  · exact Limits.comp_zero
  · exact Limits.zero_comp

/-- The integral central matrix-disk normal form. Its scalar disk orders are read from determinants. -/
def blockComplex (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) : CochainComplex (ModuleCat R) ℤ :=
  (natCx (CochainComplex.of (blockTerms R m₁ m₂ m₃) (blockD B₁ B₂ B₃)
    (blockD_sq B₁ B₂ B₃))).toCC

/-- The first matrix disk in the cochain complex. -/
theorem blockComplex_d0 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    ((blockComplex B₁ B₂ B₃).d 0 1).hom = blockD0 B₁ := by
  unfold blockComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of.d, blockD, Category.comp_id]
  rfl

/-- The middle matrix disk in the cochain complex. -/
theorem blockComplex_d1 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    ((blockComplex B₁ B₂ B₃).d 1 2).hom = blockD1 B₂ := by
  unfold blockComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of.d, blockD, Category.comp_id]
  rfl

/-- The last matrix disk in the cochain complex. -/
theorem blockComplex_d2 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    ((blockComplex B₁ B₂ B₃).d 2 3).hom = blockD2 B₃ := by
  unfold blockComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of.d, blockD, Category.comp_id]
  rfl

/-- Nothing enters degree zero of the matrix-disk model. -/
theorem blockComplex_dneg (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) : ((blockComplex B₁ B₂ B₃).d (-1) 0).hom = 0 := by
  unfold blockComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  rfl

/-- Nothing exits degree three of the matrix-disk model. -/
theorem blockComplex_d3 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) : ((blockComplex B₁ B₂ B₃).d 3 4).hom = 0 := by
  unfold blockComplex
  apply LinearMap.ext
  intro a
  rw [GCx.toCC_d_hom _ _ _ (by decide)]
  simp [natCx, natD, CochainComplex.of.d, blockD, Category.comp_id]
  rfl

/-- The cycle coordinate of zeroth cohomology of the matrix-disk model. -/
def blockClass0 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    LinearMap.ker ((blockComplex B₁ B₂ B₃).sc' (-1) 0 1).g.hom →ₗ[R] LinearMap.ker B₁.mulVecLin where
  toFun a := ⟨a.1, by
    have h := a.2
    change ((blockComplex B₁ B₂ B₃).d 0 1).hom a.1 = 0 at h
    rw [blockComplex_d0] at h
    exact congrArg (fun b : R × (Fin m₁ → R) × (Fin m₂ → R) => b.2.1) h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zeroth cohomology of the matrix-disk model is the first disk kernel. -/
def blockH0Equiv (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    (blockComplex B₁ B₂ B₃).homology 0 ≃ₗ[R] LinearMap.ker B₁.mulVecLin := by
  apply homologyEquivOfClass _ (-1) 0 1 (by simp) (by simp) (blockClass0 B₁ B₂ B₃)
  · intro a
    refine ⟨⟨a.1, ?_⟩, rfl⟩
    change ((blockComplex B₁ B₂ B₃).d 0 1).hom a.1 = 0
    rw [blockComplex_d0]
    have h : B₁.mulVecLin a.1 = 0 := a.2
    change (0, B₁.mulVecLin a.1, 0) = (0 : R × (Fin m₁ → R) × (Fin m₂ → R))
    simp only [h]
    rfl
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, rfl⟩
      apply Subtype.ext
      change ((blockComplex B₁ B₂ B₃).d (-1) 0).hom b = 0
      rw [blockComplex_dneg]
      rfl
    · intro ha
      refine ⟨0, Subtype.ext ?_⟩
      change ((blockComplex B₁ B₂ B₃).d (-1) 0).hom 0 = a.1
      rw [blockComplex_dneg]
      exact (congrArg Subtype.val ha).symm

/-- The second cycle-class map of the matrix-disk normal form. -/
def blockClass2 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    LinearMap.ker ((blockComplex B₁ B₂ B₃).sc' 1 2 3).g.hom →ₗ[R]
      (R × ((Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) × LinearMap.ker B₃.mulVecLin) where
  toFun a := (a.1.1, Submodule.Quotient.mk a.1.2.1, ⟨a.1.2.2, by
    have h := a.2
    change ((blockComplex B₁ B₂ B₃).d 2 3).hom a.1 = 0 at h
    rw [blockComplex_d2] at h
    exact h⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Second cohomology is a free line, the middle disk cokernel, and the last disk kernel. -/
def blockH2Equiv (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    (blockComplex B₁ B₂ B₃).homology 2 ≃ₗ[R]
      (R × ((Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) × LinearMap.ker B₃.mulVecLin) := by
  apply homologyEquivOfClass _ 1 2 3 (by simp) (by simp) (blockClass2 B₁ B₂ B₃)
  · rintro ⟨a, b, c⟩
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨⟨(a, b', c.1), ?_⟩, rfl⟩
    change ((blockComplex B₁ B₂ B₃).d 2 3).hom (a, b', c.1) = 0
    rw [blockComplex_d2]
    exact c.2
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, rfl⟩
      have h : (Submodule.Quotient.mk (B₂.mulVecLin b.2.2) :
          (Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 ⟨b.2.2, rfl⟩
      apply Prod.ext
      · change (((blockComplex B₁ B₂ B₃).d 1 2).hom b).1 = 0
        rw [blockComplex_d1]
        rfl
      · apply Prod.ext
        · change (Submodule.Quotient.mk (((blockComplex B₁ B₂ B₃).d 1 2).hom b).2.1 :
            (Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) = 0
          rw [blockComplex_d1]
          exact h
        · apply Subtype.ext
          change (((blockComplex B₁ B₂ B₃).d 1 2).hom b).2.2 = 0
          rw [blockComplex_d1]
          rfl
    · intro ha
      have h0 : a.1.1 = 0 := congrArg Prod.fst ha
      have h2 : (Submodule.Quotient.mk a.1.2.1 :
          (Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) = 0 := congrArg (fun b => b.2.1) ha
      have h3 : a.1.2.2 = 0 := congrArg (fun b => (b.2.2 : Fin m₃ → R)) ha
      obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 h2
      refine ⟨(0, 0, b), Subtype.ext ?_⟩
      change ((blockComplex B₁ B₂ B₃).d 1 2).hom (0, 0, b) = a.1
      rw [blockComplex_d1]
      exact Prod.ext h0.symm (Prod.ext hb h3.symm)

/-- The third cycle-class map of the matrix-disk normal form. -/
def blockClass3 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    LinearMap.ker ((blockComplex B₁ B₂ B₃).sc' 2 3 4).g.hom →ₗ[R]
      ((Fin m₃ → R) ⧸ LinearMap.range B₃.mulVecLin) :=
  (LinearMap.range B₃.mulVecLin).mkQ.comp
    (LinearMap.ker ((blockComplex B₁ B₂ B₃).sc' 2 3 4).g.hom).subtype

/-- Third cohomology of the matrix-disk model is the last disk cokernel. -/
def blockH3Equiv (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    (blockComplex B₁ B₂ B₃).homology 3 ≃ₗ[R]
      ((Fin m₃ → R) ⧸ LinearMap.range B₃.mulVecLin) := by
  apply homologyEquivOfClass _ 2 3 4 (by simp) (by simp) (blockClass3 B₁ B₂ B₃)
  · intro a
    obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
    refine ⟨⟨a', ?_⟩, rfl⟩
    change ((blockComplex B₁ B₂ B₃).d 3 4).hom a' = 0
    rw [blockComplex_d3]
    rfl
  · ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨b, hb⟩
      apply (Submodule.Quotient.mk_eq_zero _).2
      have h := congrArg Subtype.val hb
      change ((blockComplex B₁ B₂ B₃).d 2 3).hom b = a.1 at h
      rw [blockComplex_d2] at h
      exact ⟨b.2.2, h⟩
    · intro ha
      obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 ha
      refine ⟨(0, 0, b), Subtype.ext ?_⟩
      change ((blockComplex B₁ B₂ B₃).d 2 3).hom (0, 0, b) = a.1
      rw [blockComplex_d2]
      exact hb

end MatrixDisks

section MatrixDiskScalarChange

open Matrix

variable {R S : Type} [CommRing R] [CommRing S] {m₁ m₂ m₃ : ℕ}

/-- The integral basis index in each degree of the matrix-disk model. -/
def blockIndex (m₁ m₂ m₃ : ℕ) : ℤ → Type
  | .ofNat 0 => Fin m₁
  | .ofNat 1 => Unit ⊕ (Fin m₁ ⊕ Fin m₂)
  | .ofNat 2 => Unit ⊕ (Fin m₂ ⊕ Fin m₃)
  | .ofNat 3 => Fin m₃
  | .ofNat (_ + 4) => Fin 0
  | .negSucc _ => Fin 0

instance blockIndexFintype (m₁ m₂ m₃ : ℕ) (n : ℤ) : Fintype (blockIndex m₁ m₂ m₃ n) :=
  match n with
  | .ofNat 0 => inferInstanceAs (Fintype (Fin m₁))
  | .ofNat 1 => inferInstanceAs (Fintype (Unit ⊕ (Fin m₁ ⊕ Fin m₂)))
  | .ofNat 2 => inferInstanceAs (Fintype (Unit ⊕ (Fin m₂ ⊕ Fin m₃)))
  | .ofNat 3 => inferInstanceAs (Fintype (Fin m₃))
  | .ofNat (_ + 4) => inferInstanceAs (Fintype (Fin 0))
  | .negSucc _ => inferInstanceAs (Fintype (Fin 0))

instance blockIndexDecidableEq (m₁ m₂ m₃ : ℕ) (n : ℤ) : DecidableEq (blockIndex m₁ m₂ m₃ n) :=
  match n with
  | .ofNat 0 => inferInstanceAs (DecidableEq (Fin m₁))
  | .ofNat 1 => inferInstanceAs (DecidableEq (Unit ⊕ (Fin m₁ ⊕ Fin m₂)))
  | .ofNat 2 => inferInstanceAs (DecidableEq (Unit ⊕ (Fin m₂ ⊕ Fin m₃)))
  | .ofNat 3 => inferInstanceAs (DecidableEq (Fin m₃))
  | .ofNat (_ + 4) => inferInstanceAs (DecidableEq (Fin 0))
  | .negSucc _ => inferInstanceAs (DecidableEq (Fin 0))

/-- Coordinates on a free line and two finite-free disk summands. -/
def mixedCoordinates (R : Type) [CommRing R] (a b : ℕ) :
    (R × (Fin a → R) × (Fin b → R)) ≃ₗ[R] ((Unit ⊕ (Fin a ⊕ Fin b)) → R) where
  toFun x := Sum.elim (fun _ => x.1) (Sum.elim x.2.1 x.2.2)
  invFun x := (x (.inl ()), fun i => x (.inr (.inl i)), fun j => x (.inr (.inr j)))
  map_add' x y := by funext i; rcases i with u | i | j <;> rfl
  map_smul' c x := by funext i; rcases i with u | i | j <;> rfl
  left_inv _ := rfl
  right_inv x := by
    funext k
    rcases k with u | i | j
    · cases u
      rfl
    · rfl
    · rfl

/-- All matrix-disk terms carry their displayed integral bases. -/
def blockCoordinates (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) : (n : ℤ) →
    (blockComplex B₁ B₂ B₃).X n ≃ₗ[R] (blockIndex m₁ m₂ m₃ n → R)
  | .ofNat 0 => LinearEquiv.refl R _
  | .ofNat 1 => mixedCoordinates R m₁ m₂
  | .ofNat 2 => mixedCoordinates R m₂ m₃
  | .ofNat 3 => LinearEquiv.refl R _
  | .ofNat (_ + 4) => zeroCoordinates R
  | .negSucc _ => zeroCoordinates R

/-- The basis equivalences after coefficient extension. -/
def extendedBlockCoordinates (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℤ) :
    (scalarChangedComplex φ (blockComplex B₁ B₂ B₃)).X n ≃ₗ[S]
      (blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ)).X n := by
  letI : Algebra R S := φ.toAlgebra
  exact ((LinearEquiv.baseChange R S ((blockComplex B₁ B₂ B₃).X n)
    (blockIndex m₁ m₂ m₃ n → R) (blockCoordinates B₁ B₂ B₃ n)).trans
      (TensorProduct.piScalarRight R S S (blockIndex m₁ m₂ m₃ n))).trans
    (blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) n).symm

/-- Reduction of a matrix differential on a pure coefficient tensor. -/
theorem matrix_map_mulVec_scalar {m : ℕ} (φ : R →+* S) (B : Matrix (Fin m) (Fin m) R)
    (a : Fin m → R) (b : S) :
    (B.map φ).mulVecLin (fun j => φ (a j) * b) = fun j => φ (B.mulVecLin a j) * b := by
  funext j
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The actual coefficient extension of the matrix-disk complex is its reduced matrix model.
The coefficient map need not be flat. -/
def blockScalarChangeIso (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    scalarChangedComplex φ (blockComplex B₁ B₂ B₃) ≅
      blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (extendedBlockCoordinates φ B₁ B₂ B₃ n).toModuleIso) ?_
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  dsimp only [scalarChangedComplex, Functor.mapHomologicalComplex]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let : Algebra R S := φ.toAlgebra
  induction a using TensorProduct.inductionOn with
  | tmul b a =>
    let b₀ : S := b
    cases i with
    | negSucc n =>
      have ha : a = 0 := Subsingleton.elim (α := PUnit) _ _
      subst ha
      simp only [TensorProduct.tmul_zero, map_zero]
    | ofNat n =>
      rcases n with _ | _ | _ | _ | n
      · have hR : (blockComplex B₁ B₂ B₃).d 0 1 = ModuleCat.ofHom (blockD0 B₁) :=
          ModuleCat.hom_ext (blockComplex_d0 B₁ B₂ B₃)
        have hS : (blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ)).d 0 1 =
            ModuleCat.ofHom (blockD0 (B₁.map φ)) := ModuleCat.hom_ext (blockComplex_d0 _ _ _)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [hR, hS]
        let a₀ : Fin m₁ → R := a
        change (0, (B₁.map φ).mulVecLin (fun j => φ (a₀ j) * b₀), 0) =
          (φ 0 * b₀, (fun j => φ (B₁.mulVecLin a₀ j) * b₀), (fun j : Fin m₂ => φ 0 * b₀))
        rw [matrix_map_mulVec_scalar]
        simp only [map_zero, zero_mul]
        rfl
      · have hR : (blockComplex B₁ B₂ B₃).d 1 2 = ModuleCat.ofHom (blockD1 B₂) :=
          ModuleCat.hom_ext (blockComplex_d1 B₁ B₂ B₃)
        have hS : (blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ)).d 1 2 =
            ModuleCat.ofHom (blockD1 (B₂.map φ)) := ModuleCat.hom_ext (blockComplex_d1 _ _ _)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [hR, hS]
        let a₀ : R × (Fin m₁ → R) × (Fin m₂ → R) := a
        change (0, (B₂.map φ).mulVecLin (fun j => φ (a₀.2.2 j) * b₀), 0) =
          (φ 0 * b₀, (fun j => φ (B₂.mulVecLin a₀.2.2 j) * b₀), (fun j : Fin m₃ => φ 0 * b₀))
        rw [matrix_map_mulVec_scalar]
        simp only [map_zero, zero_mul]
        rfl
      · have hR : (blockComplex B₁ B₂ B₃).d 2 3 = ModuleCat.ofHom (blockD2 B₃) :=
          ModuleCat.hom_ext (blockComplex_d2 B₁ B₂ B₃)
        have hS : (blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ)).d 2 3 =
            ModuleCat.ofHom (blockD2 (B₃.map φ)) := ModuleCat.hom_ext (blockComplex_d2 _ _ _)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        erw [hR, hS]
        let a₀ : R × (Fin m₂ → R) × (Fin m₃ → R) := a
        change (B₃.map φ).mulVecLin (fun j => φ (a₀.2.2 j) * b₀) =
          (fun j => φ (B₃.mulVecLin a₀.2.2 j) * b₀)
        exact matrix_map_mulVec_scalar φ B₃ a₀.2.2 b₀
      · exact Subsingleton.elim (α := PUnit) _ _
      · have ha : a = 0 := Subsingleton.elim (α := PUnit) _ _
        subst ha
        simp only [TensorProduct.tmul_zero, map_zero]
  | add a b ha hb =>
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, map_add] at ha hb ⊢
    rw [ha, hb]

end MatrixDiskScalarChange

section MatrixDiskOrders

open Matrix

variable {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}

/-- The first matrix disk computes the zeroth finite coefficient order. -/
theorem block_card0 [Finite R] (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    Nat.card ((blockComplex B₁ B₂ B₃).homology 0) =
      Nat.card ((Fin m₁ → R) ⧸ LinearMap.range B₁.mulVecLin) := by
  rw [Nat.card_congr (blockH0Equiv B₁ B₂ B₃).toEquiv, card_ker_eq_card_coker]

/-- The second finite coefficient order includes both adjacent matrix disks and the free line. -/
theorem block_card2 [Finite R] (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    Nat.card ((blockComplex B₁ B₂ B₃).homology 2) =
      Nat.card R * Nat.card ((Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) *
        Nat.card ((Fin m₃ → R) ⧸ LinearMap.range B₃.mulVecLin) := by
  rw [Nat.card_congr (blockH2Equiv B₁ B₂ B₃).toEquiv, Nat.card_prod, Nat.card_prod,
    card_ker_eq_card_coker, mul_assoc]

/-- The last matrix disk computes the third finite coefficient order. -/
theorem block_card3 (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    Nat.card ((blockComplex B₁ B₂ B₃).homology 3) =
      Nat.card ((Fin m₃ → R) ⧸ LinearMap.range B₃.mulVecLin) :=
  Nat.card_congr (blockH3Equiv B₁ B₂ B₃).toEquiv

/-- The finite coefficient order of any matrix disk is that of its determinant scalar disk. -/
theorem card_matrixDisk_cycOrder {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ_[2]) (hB : B.det ≠ 0)
    (i : ℕ) (hi : i ≠ 0) (hv : B.det.valuation ≤ i) :
    Nat.card ((Fin m → Acoef i) ⧸ LinearMap.range (B.map (constRed i)).mulVecLin) =
      cycOrder i B.det :=
  (card_coker_acoef B hB i hi hv).trans (cycOrder_eq hi hB hv).symm

/-- All three finite coefficient orders are computed from the integral disk determinants. -/
theorem finiteBlock_orders (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2])
    (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]) (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2])
    (h₁ : B₁.det ≠ 0) (h₂ : B₂.det ≠ 0) (h₃ : B₃.det ≠ 0)
    (i : ℕ) (hi : i ≠ 0) (hv₁ : B₁.det.valuation ≤ i) (hv₂ : B₂.det.valuation ≤ i)
    (hv₃ : B₃.det.valuation ≤ i) :
    Nat.card ((blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
      (B₃.map (constRed i))).homology 0) = cycOrder i B₁.det ∧
      Nat.card ((blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
        (B₃.map (constRed i))).homology 2) =
          2 ^ (i * i) * cycOrder i B₂.det * cycOrder i B₃.det ∧
      Nat.card ((blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
        (B₃.map (constRed i))).homology 3) = cycOrder i B₃.det := by
  refine ⟨?_, ?_, ?_⟩
  · rw [block_card0, card_matrixDisk_cycOrder B₁ h₁ i hi hv₁]
  · rw [block_card2, card_acoef i hi, card_matrixDisk_cycOrder B₂ h₂ i hi hv₂,
      card_matrixDisk_cycOrder B₃ h₃ i hi hv₃]
  · rw [block_card3, card_matrixDisk_cycOrder B₃ h₃ i hi hv₃]

end MatrixDiskOrders

section IntegralBlockComparison

open NumberField IsDedekindDomain Matrix

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  {m₁ m₂ m₃ : ℕ}

/-- The matrix-disk version of the remaining integral central model input.
Unlike a single scalar disk, each matrix disk can retain noncyclic finite torsion.
The scalar central values used by calibration are its three determinants.

Both comparisons are actual maps of complexes; neither field asserts a cardinality.
The finite coefficient map is fixed by the proved Tate and local Kummer reductions. -/
structure IntegralBlockCentralModel (G : GenuineKummerData K E₀ hZ)
    (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]) (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2])
    (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]) where
  P : CochainComplex (ModuleCat ℤ_[2]) ℤ
  coordinates : (n : ℤ) → P.X n ≃ₗ[ℤ_[2]] (blockIndex m₁ m₂ m₃ n → ℤ_[2])
  normalization : blockComplex B₁ B₂ B₃ ≅ P
  comparison : P ⟶ compactCentralComplex G
  quasi_iso : QuasiIso comparison
  fibre_quasi_iso : ∀ i : ℕ, i ≠ 0 →
    QuasiIso (((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      comparison ≫ canonicalCentralReductionMap G i)
  disk1_det_ne_zero : B₁.det ≠ 0
  disk2_det_ne_zero : B₂.det ≠ 0
  disk3_det_ne_zero : B₃.det ≠ 0

namespace IntegralBlockCentralModel

variable {G : GenuineKummerData K E₀ hZ}
  {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]} {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]}
  {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}

/-- The integral degreewise change from the displayed matrix model to the retained basis. -/
def basisComparison (M : IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
    (blockIndex m₁ m₂ m₃ n → ℤ_[2]) ≃ₗ[ℤ_[2]] (blockIndex m₁ m₂ m₃ n → ℤ_[2]) :=
  (blockCoordinates B₁ B₂ B₃ n).symm.trans
    ((HomologicalComplex.Hom.isoApp M.normalization n).toLinearEquiv.trans (M.coordinates n))

/-- The determinant-basis comparison as an integral matrix. -/
def basisMatrix (M : IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
    Matrix (blockIndex m₁ m₂ m₃ n) (blockIndex m₁ m₂ m₃ n) ℤ_[2] :=
  LinearMap.toMatrix (Pi.basisFun ℤ_[2] _) (Pi.basisFun ℤ_[2] _)
    (M.basisComparison n).toLinearMap

/-- The integral matrix comparison is unimodular in every degree. -/
theorem basisMatrix_isUnit_det (M : IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
    IsUnit (M.basisMatrix n).det :=
  LinearEquiv.isUnit_det (M.basisComparison n) (Pi.basisFun ℤ_[2] _) (Pi.basisFun ℤ_[2] _)

/-- The inverse determinant-line basis factor is the alternating product of these determinants. -/
def inverseDeterminantBasisFactor (M : IntegralBlockCentralModel G B₁ B₂ B₃) : ℤ_[2]ˣ :=
  (M.basisMatrix_isUnit_det 1).unit * (M.basisMatrix_isUnit_det 3).unit *
    ((M.basisMatrix_isUnit_det 0).unit)⁻¹ * ((M.basisMatrix_isUnit_det 2).unit)⁻¹

/-- The inverse determinant-line comparison has valuation zero at the integral centre. -/
theorem inverseDeterminantBasisFactor_valuation (M : IntegralBlockCentralModel G B₁ B₂ B₃) :
    (M.inverseDeterminantBasisFactor : ℤ_[2]).valuation = 0 :=
  valuation_unit_padicInt _

/-- The canonical finite comparison of the retained integral model. -/
def fibreMap (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) :
    scalarChangedComplex (constRed i) M.P ⟶
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC :=
  ((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    M.comparison ≫ canonicalCentralReductionMap G i

/-- The comparison from the reduced matrix normal form to the genuine finite complex. -/
def finiteComparison (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) :
    blockComplex (B₁.map (constRed i)) (B₂.map (constRed i)) (B₃.map (constRed i)) ⟶
      (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC :=
  (blockScalarChangeIso (constRed i) B₁ B₂ B₃).inv ≫
    ((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      M.normalization.hom ≫ M.fibreMap i

/-- The reduced matrix comparison is a quasi-isomorphism under the remaining model input. -/
theorem finiteComparison_quasiIso (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0) :
    QuasiIso (M.finiteComparison i) := by
  have : QuasiIso (M.fibreMap i) := M.fibre_quasi_iso i hi
  dsimp only [finiteComparison]
  infer_instance

/-- The map induced on every degree of cohomology, not only on the three orders. -/
def finiteHomologyIso (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0) (n : ℤ) :
    (blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
      (B₃.map (constRed i))).homology n ≅ G.selH i n := by
  haveI := M.finiteComparison_quasiIso i hi
  exact asIso (HomologicalComplex.homologyMap (M.finiteComparison i) n)

/-- The three genuine finite-level orders are calculated from the disk determinants. -/
theorem finite_orders (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0)
    (hv₁ : B₁.det.valuation ≤ i) (hv₂ : B₂.det.valuation ≤ i) (hv₃ : B₃.det.valuation ≤ i) :
    Nat.card (G.selH i 0) = cycOrder i B₁.det ∧
      Nat.card (G.selH i 2) = 2 ^ (i * i) * cycOrder i B₂.det * cycOrder i B₃.det ∧
      Nat.card (G.selH i 3) = cycOrder i B₃.det := by
  obtain ⟨h0, h2, h3⟩ := finiteBlock_orders B₁ B₂ B₃ M.disk1_det_ne_zero M.disk2_det_ne_zero
    M.disk3_det_ne_zero i hi hv₁ hv₂ hv₃
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.card_congr (M.finiteHomologyIso i hi 0).toLinearEquiv.toEquiv.symm).trans h0
  · exact (Nat.card_congr (M.finiteHomologyIso i hi 2).toLinearEquiv.toEquiv.symm).trans h2
  · exact (Nat.card_congr (M.finiteHomologyIso i hi 3).toLinearEquiv.toEquiv.symm).trans h3

/-- The calibration order tie is proved from the integral matrix model. -/
theorem diskTie (M : IntegralBlockCentralModel G B₁ B₂ B₃) : DiskTie G B₁.det B₂.det B₃.det := by
  let i₀ := B₁.det.valuation + B₂.det.valuation + B₃.det.valuation + 1
  refine ⟨⟨i₀, ?_⟩, ⟨i₀, ?_⟩, ⟨i₀, ?_⟩⟩
  · intro i hi
    exact (M.finite_orders i (by omega) (by omega) (by omega) (by omega)).1
  · intro i hi
    exact (M.finite_orders i (by omega) (by omega) (by omega) (by omega)).2.1
  · intro i hi
    exact (M.finite_orders i (by omega) (by omega) (by omega) (by omega)).2.2

/-- The three determinant valuations are the arithmetic torsion and Sha lengths
when the separate arithmetic order input is supplied. -/
theorem disk_valuations (M : IntegralBlockCentralModel G B₁ B₂ B₃) {tA shaA : ℕ}
    (A : DiskArith G tA shaA) :
    B₁.det.valuation = padicValNat 2 tA ∧ B₂.det.valuation = padicValNat 2 shaA ∧
      B₃.det.valuation = padicValNat 2 tA :=
  M.diskTie.valuations A M.disk1_det_ne_zero M.disk2_det_ne_zero M.disk3_det_ne_zero

end IntegralBlockCentralModel

/-- A matrix-disk integral comparison discharges `DiskTie` without forcing cyclic torsion. -/
theorem diskTie_of_integralBlockCentralModel (G : GenuineKummerData K E₀ hZ)
    (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]) (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2])
    (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]) (M : IntegralBlockCentralModel G B₁ B₂ B₃) :
    DiskTie G B₁.det B₂.det B₃.det := M.diskTie

end IntegralBlockComparison

end ZInQ.Contrib.RC53Assist.CalibrationIntegral
