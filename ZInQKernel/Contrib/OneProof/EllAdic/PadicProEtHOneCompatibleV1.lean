import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtHOneKernelV1
import ZInQKernel.Contrib.OneProof.EllAdic.ExtOneCountableProductV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

private noncomputable abbrev residueTower (S : Scheme.{u}) (p : ℕ) := liftedFiniteResidueProEtSheafTower S p

private noncomputable abbrev productₚ (S : Scheme.{u}) (p : ℕ) := finiteResidueProEtProduct S p

private noncomputable abbrev integralConstant (S : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ))

/-- The first cohomology at depth `n`, taken on the actual lifted finite
residue sheaf in the cohomology universe of the integral coefficient. -/
abbrev liftedFiniteResidueHOne (S : Scheme.{u}) (p n : ℕ) : Type (u+1) :=
  ((residueTower S p).obj (op n)).H 1

/-- The transition is induced by the underlying finite residue reduction. -/
noncomputable def liftedFiniteResidueHOneReduction (S : Scheme.{u}) (p n : ℕ) :
    liftedFiniteResidueHOne S p (n+1) →+ liftedFiniteResidueHOne S p n :=
  Sheaf.H.map ((residueTower S p).map (homOfLE (Nat.le_succ n)).op) 1

/-- Compatible families are the kernel of this particular difference map. -/
noncomputable def residueHOneSubShift (S : Scheme.{u}) (p : ℕ) :
    (∀ n, liftedFiniteResidueHOne S p n) →+ (∀ n, liftedFiniteResidueHOne S p n) where
  toFun x n := x n - liftedFiniteResidueHOneReduction S p n (x (n+1))
  map_zero' := by
    funext n
    simp
  map_add' x y := by
    funext n
    change (x n + y n) - liftedFiniteResidueHOneReduction S p n (x (n+1) + y (n+1)) =
      (x n - liftedFiniteResidueHOneReduction S p n (x (n+1))) +
      (y n - liftedFiniteResidueHOneReduction S p n (y (n+1)))
    rw [map_add, add_sub_add_comm]

lemma mem_residueHOneSubShift_ker (S : Scheme.{u}) (p : ℕ) (x : ∀ n, liftedFiniteResidueHOne S p n) :
    x ∈ (residueHOneSubShift S p).ker ↔
      ∀ n, liftedFiniteResidueHOneReduction S p n (x (n+1)) = x n := by
  change residueHOneSubShift S p x = 0 ↔ _
  constructor
  · intro h n
    exact (sub_eq_zero.mp (congrFun h n)).symm
  · intro h
    funext n
    exact sub_eq_zero.mpr (h n).symm

private noncomputable def productToResidueHOne (S : Scheme.{u}) (p : ℕ) :
    (productₚ S p).H 1 →+ (∀ n, liftedFiniteResidueHOne S p n) :=
  extOnePiComparison (integralConstant S) (towerObjects (residueTower S p))

private lemma productToResidueHOne_π (S : Scheme.{u}) (p : ℕ) (x : (productₚ S p).H 1) (n : ℕ) :
    productToResidueHOne S p x n = Sheaf.H.map (Pi.π (towerObjects (residueTower S p)) n) 1 x := rfl

private lemma productToResidueHOne_subShift (S : Scheme.{u}) (p : ℕ) (x : (productₚ S p).H 1) :
    productToResidueHOne S p (Sheaf.H.map (finiteResidueProEtSubShift S p) 1 x) =
      residueHOneSubShift S p (productToResidueHOne S p x) := by
  funext n
  let t := (residueTower S p).map (homOfLE (Nat.le_succ n)).op
  let a := Pi.π (towerObjects (residueTower S p)) n
  let b := Pi.π (towerObjects (residueTower S p)) (n+1)
  have hsub : Sheaf.H.map (a - b ≫ t) 1 x = Sheaf.H.map a 1 x - Sheaf.H.map (b ≫ t) 1 x := by
    have h := Sheaf.H.map_add_apply (n := 1) (a - b ≫ t) (b ≫ t) x
    rw [sub_add_cancel] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  change Sheaf.H.map a 1 (Sheaf.H.map (finiteResidueProEtSubShift S p) 1 x) =
    Sheaf.H.map a 1 x - Sheaf.H.map t 1 (Sheaf.H.map b 1 x)
  rw [← Sheaf.H.map_comp_apply (finiteResidueProEtSubShift S p) a,
    ← Sheaf.H.map_comp_apply b t]
  rw [show finiteResidueProEtSubShift S p ≫ a = a - b ≫ t from towerSubShift_π _ n]
  exact hsub

private noncomputable def productKernelToResidueHOne (S : Scheme.{u}) (p : ℕ) :
    ↥(Sheaf.H.map (finiteResidueProEtSubShift S p) 1).ker →+ ↥(residueHOneSubShift S p).ker where
  toFun x := ⟨productToResidueHOne S p x.1, by
    change residueHOneSubShift S p (productToResidueHOne S p x.1) = 0
    rw [← productToResidueHOne_subShift, show Sheaf.H.map (finiteResidueProEtSubShift S p) 1 x.1 = 0
      from x.property, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (productToResidueHOne S p)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (productToResidueHOne S p) x.1 y.1

private lemma productKernelToResidueHOne_bijective (S : Scheme.{u}) (p : ℕ)
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf (Scheme.ProEt.topology S) Ab.{u+1})] :
    Function.Bijective (productKernelToResidueHOne S p) := by
  have h : Function.Bijective (productToResidueHOne S p) :=
    extOnePiComparison_bijective (integralConstant S) (towerObjects (residueTower S p))
  constructor
  · intro x y hxy
    exact Subtype.ext (h.1 (congrArg Subtype.val hxy))
  · intro y
    obtain ⟨x, hx⟩ := h.2 y.1
    have hz : Sheaf.H.map (finiteResidueProEtSubShift S p) 1 x = 0 := by
      apply h.1
      rw [productToResidueHOne_subShift, hx, map_zero]
      exact y.property
    exact ⟨⟨x, hz⟩, Subtype.ext hx⟩

/-- The canonical homomorphism from first cohomology of the original
integral coefficient to compatible finite-depth families. It exists before
asserting exactness of countable products; that input is used for bijectivity. -/
noncomputable def ellAdicHOneToCompatibleResidues (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    S.EllAdicCohomology p 1 →+ ↥(residueHOneSubShift S p).ker :=
  (productKernelToResidueHOne S p).comp
    (extOneToNextKernel (integralConstant S) (padicCoefficientProductSequence S p))

/-- Each coordinate is induced by the literal reduction arrow, not a
separately chosen equivalence of cohomology groups. -/
lemma ellAdicHOneToCompatibleResidues_apply (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (x : S.EllAdicCohomology p 1) (n : ℕ) :
    (ellAdicHOneToCompatibleResidues S p x).1 n =
      Sheaf.H.map ((continuousResidueProEtSheafCone S p).π.app (op n)) 1 x := by
  let z : (liftedPadicCoefficientSheaf S p).H 1 := x
  let i : liftedPadicCoefficientSheaf S p ⟶ finiteResidueProEtProduct S p :=
    padicCoefficientToResidueProduct S p
  let j : finiteResidueProEtProduct S p ⟶ (residueTower S p).obj (op n) :=
    Pi.π (towerObjects (residueTower S p)) n
  let r : liftedPadicCoefficientSheaf S p ⟶ (residueTower S p).obj (op n) :=
    (continuousResidueProEtSheafCone S p).π.app (op n)
  change Sheaf.H.map j 1 (Sheaf.H.map i 1 z) = Sheaf.H.map r 1 z
  have hr : i ≫ j = r := padicCoefficientToResidueProduct_π S p n
  exact (Sheaf.H.map_comp_apply i j z).symm.trans
    (congrArg (fun k : liftedPadicCoefficientSheaf S p ⟶ (residueTower S p).obj (op n) =>
      Sheaf.H.map k 1 z) hr)

theorem ellAdicHOneToCompatibleResidues_bijective (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf (Scheme.ProEt.topology S) Ab.{u+1})] :
    Function.Bijective (ellAdicHOneToCompatibleResidues S p) :=
  (productKernelToResidueHOne_bijective S p).comp (padicProEt_H1_toProductKernel_bijective S p)

end RC53.EllAdic
