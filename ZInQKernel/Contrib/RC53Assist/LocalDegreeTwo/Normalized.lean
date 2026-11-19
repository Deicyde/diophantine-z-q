import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Conjugation
import ZInQKernel.Contrib.RC53Assist.DerivedKummer.LocalDuality
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified

/-!
# Normalized degree-two coordinates at derivative primes

The coordinate is obtained from the local Brauer invariant. Its orientation is
fixed by the cup product of the arithmetic unramified character and the Kummer
character of a uniformizer. Finite coefficient extension is performed on the
continuous cochains themselves, not on an unrelated finite complex.

The coefficient rings are the finite Frobenius rings
`(ℤ/2^iℤ)[t]/t^i`. Self-injectivity extends the scalar invariant from cocycles
to all degree-two cochains. No splitting of a module over a field is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo

open CategoryTheory Module
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open scoped TensorProduct

/-- A scalar coefficient module with trivial Galois action. -/
def ScalarCoeff (S : Type) : Type := S

instance (S : Type) [CommRing S] : AddCommGroup (ScalarCoeff S) :=
  inferInstanceAs (AddCommGroup S)

instance (S : Type) [CommRing S] : Module S (ScalarCoeff S) :=
  inferInstanceAs (Module S S)

instance (S : Type) : TopologicalSpace (ScalarCoeff S) := ⊥

instance (S : Type) : DiscreteTopology (ScalarCoeff S) := ⟨rfl⟩

instance (S : Type) [CommRing S] : ContinuousAdd (ScalarCoeff S) :=
  ⟨continuous_of_discreteTopology⟩

instance (S : Type) [CommRing S] : ContinuousConstSMul S (ScalarCoeff S) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

instance (G S : Type) [Group G] [CommRing S] : DistribMulAction G (ScalarCoeff S) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance (G S : Type) [Group G] [CommRing S] : SMulCommClass G S (ScalarCoeff S) :=
  ⟨fun _ _ _ => rfl⟩

instance (G S : Type) [Group G] [TopologicalSpace G] [CommRing S] :
    ContinuousSMul G (ScalarCoeff S) := ⟨continuous_snd⟩

/-- Forgetting the scalar coefficient tag preserves the scalar module. -/
def ScalarCoeff.equiv (S : Type) [CommRing S] : ScalarCoeff S ≃ₗ[S] S :=
  LinearEquiv.refl S S

section CoefficientExtension

variable {S R G M : Type} [CommRing S] [CommRing R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [Module S M]
  [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- Evaluation of a continuous cochain at a tuple. -/
def cochainEval {n : ℕ} (v : Fin n → G) : (contCochains R G M).X n →ₗ[R] M where
  toFun z := contFun z v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A scalar coordinate of a continuous cochain. -/
def scalarCochain {n : ℕ} (f : M →ₗ[S] S) (z : (contCochains R G M).X n) :
    (contCochains S G (ScalarCoeff S)).X n :=
  (contSubCx S G (ScalarCoeff S)).ofSub
    ⟨fun v => (show ScalarCoeff S from f (contFun z v)),
      (continuous_of_discreteTopology : Continuous (fun m : M =>
        (show ScalarCoeff S from f m))).comp ((contSubCx R G M).el z).2⟩

/-- The scalar cochain applies the coefficient functional pointwise. -/
theorem scalarCochain_eval {n : ℕ} (f : M →ₗ[S] S) (z : (contCochains R G M).X n)
    (v : Fin n → G) :
    (show S from contFun (k := S) (G := G) (M := ScalarCoeff S)
      (scalarCochain f z) v) = f (contFun z v) := rfl

/-- Scalar coordinates respect addition of cochains. -/
theorem scalarCochain_add {n : ℕ} (f : M →ₗ[S] S)
    (z w : (contCochains R G M).X n) :
    scalarCochain f (z + w) = scalarCochain f z + scalarCochain f w := by
  apply contCochains_ext
  intro v
  exact map_add f _ _

/-- Scalar coordinates of the zero cochain vanish. -/
theorem scalarCochain_zero {n : ℕ} (f : M →ₗ[S] S) :
    scalarCochain f (0 : (contCochains R G M).X n) = 0 := by
  apply contCochains_ext
  intro v
  exact map_zero f

variable {ι : Type} [Fintype ι] (b : Basis ι S M)

/-- Finite coefficient decomposition of a scalar functional on cochains. -/
theorem scalarCochain_basis_expansion {n : ℕ} (f : M →ₗ[S] S)
    (z : (contCochains R G M).X n) :
    scalarCochain f z = ∑ j, f (b j) • scalarCochain (b.coord j) z := by
  apply contCochains_ext
  intro v
  change f (contFun z v) = (show S from cochainEval (R := S) (M := ScalarCoeff S) v
    (∑ j, f (b j) • scalarCochain (b.coord j) z))
  rw [map_sum]
  simp only [map_smul]
  change f (contFun z v) = ∑ j, f (b j) * b.coord j (contFun z v)
  conv_lhs => rw [← b.sum_repr (contFun z v)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, Basis.coord_apply, mul_comm]

variable (c : (contCochains S G (ScalarCoeff S)).X 2 →ₗ[S] S)

/-- Applying the scalar invariant in every finite coefficient coordinate. -/
def coefficientValue (z : (contCochains R G M).X 2) : M :=
  ∑ j, c (scalarCochain (b.coord j) z) • b j

/-- Every scalar functional reads the same invariant of the corresponding
scalar-valued cochain. -/
theorem coefficientValue_functional (f : M →ₗ[S] S)
    (z : (contCochains R G M).X 2) :
    f (coefficientValue b c z) = c (scalarCochain f z) := by
  rw [coefficientValue, map_sum, scalarCochain_basis_expansion b, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- In a chosen basis the vector invariant is the scalar invariant of each
coordinate. -/
theorem coefficientValue_coord (j : ι) (z : (contCochains R G M).X 2) :
    b.coord j (coefficientValue b c z) = c (scalarCochain (b.coord j) z) :=
  coefficientValue_functional b c (b.coord j) z

variable [SMulCommClass R S M]

/-- Finite coefficient extension is linear over the full coefficient ring,
not merely over the residue scalars. -/
def coefficientCoordinate : (contCochains R G M).X 2 →ₗ[R] M where
  toFun := coefficientValue b c
  map_add' z w := by
    apply b.repr.injective
    ext j
    change b.coord j (coefficientValue b c (z + w)) =
      b.coord j (coefficientValue b c z + coefficientValue b c w)
    rw [map_add, coefficientValue_coord, coefficientValue_coord, coefficientValue_coord,
      scalarCochain_add, map_add]
  map_smul' r z := by
    apply b.repr.injective
    ext j
    let f : M →ₗ[S] S :=
      { toFun := fun m => b.coord j (r • m)
        map_add' := fun x y => by rw [smul_add, map_add]
        map_smul' := fun a m => by rw [smul_comm r a, map_smul]; rfl }
    change b.coord j (coefficientValue b c (r • z)) = f (coefficientValue b c z)
    rw [coefficientValue_coord, coefficientValue_functional]
    congr 1

variable (htriv : ∀ (g : G) (m : M), g • m = m)

omit [SMulCommClass R S M] in
include htriv in
/-- A scalar coordinate commutes with the differential in degree one. -/
theorem scalarCochain_d12 (f : M →ₗ[S] S) (a : (contCochains R G M).X 1) :
    scalarCochain f (((contCochains R G M).d 1 2).hom a) =
      ((contCochains S G (ScalarCoeff S)).d 1 2).hom (scalarCochain f a) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
  rw [hv]
  change f (contFun (((contCochains R G M).d 1 2).hom a) ![v 0, v 1]) = _
  rw [contFun_d12, contFun_d12]
  change f (v 0 • contFun a (fun _ => v 1) - contFun a (fun _ => v 0 * v 1) +
      contFun a (fun _ => v 0)) =
    f (contFun a (fun _ => v 1)) - f (contFun a (fun _ => v 0 * v 1)) +
      f (contFun a (fun _ => v 0))
  rw [htriv, map_add, map_sub]

omit [SMulCommClass R S M] in
include htriv in
/-- A scalar coordinate commutes with the differential in degree two. -/
theorem scalarCochain_d23 (f : M →ₗ[S] S) (z : (contCochains R G M).X 2) :
    scalarCochain f (((contCochains R G M).d 2 3).hom z) =
      ((contCochains S G (ScalarCoeff S)).d 2 3).hom (scalarCochain f z) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  rw [hv]
  change f (contFun (((contCochains R G M).d 2 3).hom z) ![v 0, v 1, v 2]) = _
  rw [contFun_d23, contFun_d23]
  change f (v 0 • contFun z ![v 1, v 2] - contFun z ![v 0 * v 1, v 2] +
      contFun z ![v 0, v 1 * v 2] - contFun z ![v 0, v 1]) =
    f (contFun z ![v 1, v 2]) - f (contFun z ![v 0 * v 1, v 2]) +
      f (contFun z ![v 0, v 1 * v 2]) - f (contFun z ![v 0, v 1])
  rw [htriv, map_sub, map_add, map_sub]

omit [Fintype ι] [SMulCommClass R S M] in
/-- Scalar coordinates in a finite basis detect equality of cochains. -/
theorem cochain_eq_of_scalar_coordinates {n : ℕ} {z w : (contCochains R G M).X n}
    (h : ∀ j, scalarCochain (b.coord j) z = scalarCochain (b.coord j) w) : z = w := by
  apply contCochains_ext
  intro v
  apply b.repr.injective
  ext j
  exact congrArg (fun a => (show S from contFun (k := S) (G := G)
    (M := ScalarCoeff S) a v)) (h j)

/-- Reconstructing a cochain from its finite scalar coordinates. -/
def expandCochain {n : ℕ}
    (a : ι → (contCochains S G (ScalarCoeff S)).X n) : (contCochains R G M).X n :=
  (contSubCx R G M).ofSub
    ⟨fun v => ∑ j, ScalarCoeff.equiv S
        (contFun (k := S) (G := G) (M := ScalarCoeff S) (a j) v) • b j,
      continuous_finsetSum _ fun j _ =>
        (continuous_of_discreteTopology : Continuous (fun s : ScalarCoeff S =>
          ScalarCoeff.equiv S s • b j)).comp ((contSubCx S G (ScalarCoeff S)).el (a j)).2⟩

omit [SMulCommClass R S M] in
/-- A scalar coordinate of the reconstruction is the original cochain. -/
theorem scalarCochain_expand {n : ℕ}
    (a : ι → (contCochains S G (ScalarCoeff S)).X n) (j : ι) :
    scalarCochain (b.coord j) (expandCochain (R := R) b a) = a j := by
  classical
  apply contCochains_ext
  intro v
  apply (ScalarCoeff.equiv S).injective
  change b.coord j (∑ k, ScalarCoeff.equiv S
    (contFun (k := S) (G := G) (M := ScalarCoeff S) (a k) v) • b k) =
      ScalarCoeff.equiv S (contFun (k := S) (G := G) (M := ScalarCoeff S) (a j) v)
  simp [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]

include htriv in
/-- The scalar coordinate induces the full finite-coefficient degree-two
coordinate, including both kernel exactness and surjectivity. -/
theorem coefficientCoordinate_isCoordinate
    (hc : LocalDegreeTwoCoordinate (M := ScalarCoeff S) c) :
    LocalDegreeTwoCoordinate (coefficientCoordinate (R := R) b c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply b.repr.injective
    ext j
    change b.coord j (coefficientValue b c (((contCochains R G M).d 1 2).hom a)) =
      b.coord j (0 : M)
    rw [map_zero, coefficientValue_coord, scalarCochain_d12 htriv]
    exact hc.1 _
  · intro z hz hcz
    have hzj : ∀ j, ((contCochains S G (ScalarCoeff S)).d 2 3).hom
        (scalarCochain (b.coord j) z) = 0 := by
      intro j
      rw [← scalarCochain_d23 htriv, hz, scalarCochain_zero]
    have hczj : ∀ j, c (scalarCochain (b.coord j) z) = 0 := by
      intro j
      rw [← coefficientValue_coord]
      change b.coord j (coefficientCoordinate b c z) = 0
      rw [hcz, map_zero]
    choose a ha using fun j => hc.2.1 _ (hzj j) (hczj j)
    refine ⟨expandCochain b a, cochain_eq_of_scalar_coordinates b fun j => ?_⟩
    rw [scalarCochain_d12 htriv, scalarCochain_expand, ha]
  · intro m
    choose z hz hzm using fun j => hc.2.2 (show ScalarCoeff S from b.coord j m)
    refine ⟨expandCochain b z, ?_, ?_⟩
    · apply cochain_eq_of_scalar_coordinates b
      intro j
      rw [scalarCochain_d23 htriv, scalarCochain_expand, hz, scalarCochain_zero]
    · apply b.repr.injective
      ext j
      change b.coord j (coefficientValue b c (expandCochain b z)) = b.coord j m
      rw [coefficientValue_coord, scalarCochain_expand]
      exact hzm j

variable [Algebra S R] [IsScalarTower S R M]

/-- The scalar tame-symbol orientation is preserved by extension to the full
coefficient module. -/
theorem coefficientCoordinate_normalized (u κ : G → S)
    (hc : LocalDegreeTwoNormalized (M := ScalarCoeff S) c u κ) :
    LocalDegreeTwoNormalized (coefficientCoordinate (R := R) b c)
      (fun g => algebraMap S R (u g)) (fun g => algebraMap S R (κ g)) := by
  intro m z hz
  apply b.repr.injective
  ext j
  change b.coord j (coefficientValue b c z) = b.coord j m
  rw [coefficientValue_coord]
  apply hc (show ScalarCoeff S from b.coord j m) (scalarCochain (b.coord j) z)
  intro g h
  change b.coord j (evalTwo R M g h z) = (u g * κ h) * b.coord j m
  rw [hz, ← map_mul, algebraMap_smul, map_smul, smul_eq_mul]

end CoefficientExtension

/-- Scalar multiplication as a biadditive pairing. -/
def scalarPairing (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] :
    ScalarCoeff (ZMod n) →+ M →+ M where
  toFun a :=
    { toFun := fun m => ScalarCoeff.equiv (ZMod n) a • m
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  map_zero' := by ext m; exact zero_smul (ZMod n) m
  map_add' a b := by ext m; exact add_smul _ _ m

section TameSymbol

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n]

/-- The arithmetic unramified character, read on the separable closure. -/
def unramifiedCharacter (g : AbsoluteGaloisGroup F) : ZMod n :=
  urCharN F n ((absoluteGaloisGroupRestrictEquiv F).symm g)

/-- The unramified character is additive. -/
theorem unramifiedCharacter_mul (g h : AbsoluteGaloisGroup F) :
    unramifiedCharacter n (g * h) = unramifiedCharacter n g + unramifiedCharacter n h := by
  rw [unramifiedCharacter, map_mul, urCharN_mul]
  rfl

/-- The unramified character is continuous. -/
theorem unramifiedCharacter_continuous : Continuous (unramifiedCharacter (F := F) n) :=
  (continuous_urCharN (K := F) (n := n)).comp (absoluteGaloisGroupRestrictEquiv F).symm.continuous

/-- The unramified character as a scalar-valued continuous one-cocycle. -/
def unramifiedCocycle : Z1 (AbsoluteGaloisGroup F) (ScalarCoeff (ZMod n)) :=
  ⟨fun g => (ScalarCoeff.equiv (ZMod n)).symm (unramifiedCharacter n g),
    mem_Z1_iff.mpr ⟨(continuous_of_discreteTopology : Continuous
        (ScalarCoeff.equiv (ZMod n)).symm).comp (unramifiedCharacter_continuous n),
      fun g h => by
        change unramifiedCharacter n (g * h) = unramifiedCharacter n h + unramifiedCharacter n g
        rw [unramifiedCharacter_mul, add_comm]⟩⟩

/-- The associated rational-circle character. -/
def unramifiedCircleCharacter : Additive (AbsoluteGaloisGroup F) →+ AddCircle (1 : ℚ) :=
  (ZMod.toRatAddCircle n).comp
    { toFun := fun g => unramifiedCharacter n g.toMul
      map_zero' := by
        change urCharN F n ((absoluteGaloisGroupRestrictEquiv F).symm 1) = 0
        rw [map_one, urCharN_inertia (inertiaSubgroup F).one_mem]
      map_add' := fun g h => unramifiedCharacter_mul n g.toMul h.toMul }

/-- The rational-circle character has open kernel. -/
theorem unramifiedCircleCharacter_open :
    IsOpen ((unramifiedCircleCharacter (F := F) n).ker : Set (Additive (AbsoluteGaloisGroup F))) := by
  have hzero : IsOpen ({0} : Set (ZMod n)) := isOpen_discrete _
  have hcont : Continuous (fun g : Additive (AbsoluteGaloisGroup F) =>
      unramifiedCharacter n g.toMul) :=
    (unramifiedCharacter_continuous n).comp continuous_toMul
  have heq : ((unramifiedCircleCharacter (F := F) n).ker : Set (Additive (AbsoluteGaloisGroup F))) =
      (fun g => unramifiedCharacter n g.toMul) ⁻¹' {0} := by
    ext g
    simp [unramifiedCircleCharacter, AddMonoidHom.mem_ker, ZMod.toRatAddCircle_eq_zero]
  rw [heq]
  exact hzero.preimage hcont

/-- The carry of the circle character is the integral defect of the canonical
residue representatives. -/
theorem unramified_characterCarry (g h : AbsoluteGaloisGroup F) :
    (n : ℤ) * characterCarry (unramifiedCircleCharacter n) g h =
      (unramifiedCharacter n g).val + (unramifiedCharacter n h).val -
        (unramifiedCharacter n (g * h)).val := by
  have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hrep (g : AbsoluteGaloisGroup F) :
      (AddCircle.equivIco 1 0 (unramifiedCircleCharacter n (Additive.ofMul g)) : ℚ) =
        (unramifiedCharacter n g).val / n := by
    change (AddCircle.equivIco 1 0 (ZMod.toRatAddCircle n (unramifiedCharacter n g)) : ℚ) = _
    rw [ZMod.toRatAddCircle_apply]
    apply AddCircle.equivIco_coe_of_mem
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one hn]
    exact_mod_cast ZMod.val_lt (unramifiedCharacter n g)
  have hc := intCast_characterCarry (unramifiedCircleCharacter n) g h
  rw [hrep, hrep, hrep] at hc
  have hq : (n : ℚ) * characterCarry (unramifiedCircleCharacter n) g h =
      (unramifiedCharacter n g).val + (unramifiedCharacter n h).val -
        (unramifiedCharacter n (g * h)).val := by
    rw [hc]
    field_simp
  exact_mod_cast hq

variable {n} (a : Fˣ) (β : (SeparableClosure F)ˣ)
  (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)

/-- The unramified character cupped with the Kummer character of the chosen
root, through scalar multiplication. -/
def unramifiedKummerCup : Z2 (AbsoluteGaloisGroup F) (KummerCoeff F n) :=
  ZInQ.Contrib.CloudB3RC53.Duality.cupZ (scalarPairing n (KummerCoeff F n))
    (fun g x y => by rw [hμ g y, hμ g _]; rfl)
    (unramifiedCocycle n) ⟨kummerCocycle hβ, kummerCocycle_mem_Z1 hβ⟩

/-- The cup has the usual inhomogeneous formula with the unramified character
in the first argument. -/
theorem unramifiedKummerCup_apply (g h : AbsoluteGaloisGroup F) :
    (unramifiedKummerCup a β hβ hμ : AbsoluteGaloisGroup F × AbsoluteGaloisGroup F →
      KummerCoeff F n) (g, h) = (unramifiedCharacter n g).val • kummerCocycle hβ h := by
  change unramifiedCharacter n g • (g • kummerCocycle hβ h) = _
  rw [hμ]
  conv_lhs => rw [← ZMod.natCast_zmod_val (unramifiedCharacter n g)]
  exact Nat.cast_smul_eq_nsmul (ZMod n) _ _

/-- An explicit continuous primitive comparing the Kummer cup with the carry
class. The conjugated root is used to preserve the positive orientation. -/
def cupCarryPrimitive (g : AbsoluteGaloisGroup F) : UnitsCoeff F :=
  (unramifiedCharacter n g).val • (g • (Additive.ofMul β : UnitsCoeff F))

/-- The comparison primitive is continuous. -/
theorem cupCarryPrimitive_continuous : Continuous (cupCarryPrimitive (n := n) β) := by
  exact (continuous_of_discreteTopology : Continuous (fun p : ZMod n × UnitsCoeff F =>
    p.1.val • p.2)).comp
      ((unramifiedCharacter_continuous n).prodMk (continuous_id.smul continuous_const))

/-- The coefficient inclusion of the cup and the coboundary of the primitive
sum to the positively oriented carry cocycle. -/
theorem cupCarryPrimitive_identity (g h : AbsoluteGaloisGroup F) :
    d1 (AbsoluteGaloisGroup F) (UnitsCoeff F) (cupCarryPrimitive (n := n) β) (g, h) +
      kummerCoeffIncl F n
        ((unramifiedKummerCup a β hβ hμ : AbsoluteGaloisGroup F × AbsoluteGaloisGroup F →
          KummerCoeff F n) (g, h)) =
      characterCarry (unramifiedCircleCharacter n) g h •
        (baseUnitsEquivInvariants F (Additive.ofMul a) : UnitsCoeff F) := by
  let B : UnitsCoeff F := Additive.ofMul β
  let A : UnitsCoeff F := baseUnitsEquivInvariants F (Additive.ofMul a)
  have hnB : n • B = A := by
    apply Additive.toMul.injective
    change β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a
    exact hβ
  have hfix : g • (h • B - B) = h • B - B := by
    rw [← kummerCoeffIncl_kummerCocycle hβ h, ← kummerCoeffIncl_equivariant, hμ]
  have hdiff : (g * h) • B - g • B = h • B - B := by
    rw [mul_smul, ← smul_sub]
    exact hfix
  have hngh : n • ((g * h) • B) = A := by
    rw [smul_comm, hnB]
    exact (FixedPoints.mem_addSubgroup _ _ _).mp
      (baseUnitsEquivInvariants F (Additive.ofMul a)).2 (g * h)
  rw [unramifiedKummerCup_apply, map_nsmul, kummerCoeffIncl_kummerCocycle, ← hdiff]
  change g • ((unramifiedCharacter n h).val • (h • B)) -
      (unramifiedCharacter n (g * h)).val • ((g * h) • B) +
      (unramifiedCharacter n g).val • (g • B) +
      (unramifiedCharacter n g).val • ((g * h) • B - g • B) =
        characterCarry (unramifiedCircleCharacter n) g h • A
  rw [smul_comm, ← mul_smul, nsmul_sub]
  simp only [← natCast_zsmul]
  calc
    _ = ((unramifiedCharacter n g).val + (unramifiedCharacter n h).val -
        (unramifiedCharacter n (g * h)).val : ℤ) • ((g * h) • B) := by
      rw [sub_smul, add_smul]
      abel
    _ = ((n : ℤ) * characterCarry (unramifiedCircleCharacter n) g h) • ((g * h) • B) := by
      rw [unramified_characterCarry]
    _ = characterCarry (unramifiedCircleCharacter n) g h • A := by
      rw [mul_comm, mul_zsmul, natCast_zsmul, hngh]

/-- The Kummer cup maps to the positively oriented carry class in the Brauer
coefficient module. -/
theorem unramifiedKummerCup_carry :
    explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n) (kummerCoeffInclHom F n)
        continuous_of_discreteTopology (H2pi _ _ (unramifiedKummerCup a β hβ hμ)) =
      H2pi (AbsoluteGaloisGroup F) (UnitsCoeff F)
        (characterCarryCocycle (unramifiedCircleCharacter n)
          (unramifiedCircleCharacter_open n) (baseUnitsEquivInvariants F (Additive.ofMul a))) := by
  change explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n) (kummerCoeffInclHom F n)
      continuous_of_discreteTopology (unramifiedKummerCup a β hβ hμ : H2 _ _) =
    (characterCarryCocycle (unramifiedCircleCharacter n)
      (unramifiedCircleCharacter_open n) (baseUnitsEquivInvariants F (Additive.ofMul a)) : H2 _ _)
  rw [explicitCoeff2_mk]
  apply H2pi_eq_iff.mpr
  apply mem_B2_iff.mpr
  refine ⟨fun g => -cupCarryPrimitive (n := n) β g,
    (cupCarryPrimitive_continuous (n := n) β).neg, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have hid := cupCarryPrimitive_identity a β hβ hμ g h
  simp only [Pi.sub_apply, cocyclesMap2_apply, characterCarryCocycle_apply]
  change d1 (AbsoluteGaloisGroup F) (UnitsCoeff F) (-cupCarryPrimitive (n := n) β) (g, h) =
    kummerCoeffIncl F n
      ((unramifiedKummerCup a β hβ hμ : AbsoluteGaloisGroup F × AbsoluteGaloisGroup F →
        KummerCoeff F n) (g, h)) -
      characterCarry (unramifiedCircleCharacter n) g h •
        (baseUnitsEquivInvariants F (Additive.ofMul a) : UnitsCoeff F)
  rw [map_neg, Pi.neg_apply, eq_sub_of_add_eq hid, neg_sub]

/-- The cup of the arithmetic unramified character and the Kummer character
of a uniformizer has invariant `1/n`. -/
theorem unramifiedKummerCup_invariant (ha : IsUniformizer F a) :
    invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
      (H2pi _ _ (unramifiedKummerCup a β hβ hμ))) =
        ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
  change invMap F (unitsRepH2Equiv F
    (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n) (kummerCoeffInclHom F n)
      continuous_of_discreteTopology (H2pi _ _ (unramifiedKummerCup a β hβ hμ)))) = _
  rw [unramifiedKummerCup_carry]
  change invMap F (unitsRepH2Equiv F
    (characterCarryCocycle (unramifiedCircleCharacter n)
      (unramifiedCircleCharacter_open n) (baseUnitsEquivInvariants F (Additive.ofMul a)) : H2 _ _)) = _
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective
    (commutator ((Field.absoluteGaloisGroup F))).topologicalClosure (artinMap F a)
  rw [invMap_characterCarryCocycle_of_mk_eq_artinMap _ _ a σ hσ]
  change ZMod.toRatAddCircle n
    (urCharN F n ((absoluteGaloisGroupRestrictEquiv F).symm
      (absoluteGaloisGroupRestrictEquiv F σ))) = _
  rw [(absoluteGaloisGroupRestrictEquiv F).symm_apply_apply,
    urCharN_frobenius (isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer F ha σ hσ)]
  simpa using ZMod.toRatAddCircle_natCast n 1

end TameSymbol

section ScalarCups

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (n : ℕ) [NeZero n] (u κ : G → ZMod n) (hu : Continuous u) (hκ : Continuous κ)

/-- The scalar two-cochain `(g,h) ↦ u(g)κ(h)`. -/
def scalarCup : (contCochains (ZMod n) G (ScalarCoeff (ZMod n))).X 2 :=
  mkCochain2 (fun p => (ScalarCoeff.equiv (ZMod n)).symm (u p.1 * κ p.2))
    ((continuous_of_discreteTopology : Continuous (fun p : ZMod n × ZMod n =>
      (ScalarCoeff.equiv (ZMod n)).symm (p.1 * p.2))).comp
        ((hu.comp continuous_fst).prodMk (hκ.comp continuous_snd)))

omit [NeZero n] in
/-- Evaluation of the scalar cup. -/
theorem scalarCup_eval (g h : G) :
    evalTwo (ZMod n) (ScalarCoeff (ZMod n)) g h (scalarCup n u κ hu hκ) =
      (ScalarCoeff.equiv (ZMod n)).symm (u g * κ h) := rfl

omit [NeZero n] in
/-- The scalar cup of additive characters is a continuous two-cocycle. -/
theorem scalarCup_cycle (huadd : ∀ g h, u (g * h) = u g + u h)
    (hκadd : ∀ g h, κ (g * h) = κ g + κ h) :
    ((contCochains (ZMod n) G (ScalarCoeff (ZMod n))).d 2 3).hom
      (scalarCup n u κ hu hκ) = 0 := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  rw [hv, contFun_d23]
  apply (ScalarCoeff.equiv (ZMod n)).injective
  change u (v 1) * κ (v 2) - u (v 0 * v 1) * κ (v 2) +
    u (v 0) * κ (v 1 * v 2) - u (v 0) * κ (v 1) = 0
  rw [huadd, hκadd]
  ring

end ScalarCups

section ScalarInvariant

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  (η : ZMod n ≃+ KummerCoeff F n)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)

/-- The coefficient and Galois-group dictionary for scalar degree-two
cohomology and Kummer degree-two cohomology. -/
def scalarKummerEquiv :
    H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) ≃+
      H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) :=
  explicitMap2Equiv (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))
    (AbsoluteGaloisGroup F) (KummerCoeff F n) (absoluteGaloisGroupRestrictEquiv F).symm
    ((ScalarCoeff.equiv (ZMod n)).toAddEquiv.trans η)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun g x => by rw [hμ]; rfl)

/-- The actual local invariant of a scalar degree-two class. -/
def scalarInvariant : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) →+ AddCircle (1 : ℚ) :=
  (invMap F).toAddMonoidHom.comp
    ((ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n).comp
      (scalarKummerEquiv η hμ).toAddMonoidHom)

omit [NeZero n] in
/-- Scalar invariants lie in the exact `n`-torsion subgroup of the rational
circle. -/
theorem scalarInvariant_torsion
    (q : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))) :
    n • scalarInvariant η hμ q = 0 := by
  have hkill : ∀ x : ScalarCoeff (ZMod n), n • x = 0 := by
    intro x
    apply (ScalarCoeff.equiv (ZMod n)).injective
    rw [map_nsmul, map_zero]
    simp
  rw [← map_nsmul, nsmul_H2_eq_zero hkill, map_zero]

/-- The scalar degree-two invariant, with values in `ℤ/nℤ` rather than
`(1/n)ℤ/ℤ`. -/
def scalarH2Value : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) →+ ZMod n :=
  (ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv n).toAddMonoidHom.comp
    ((scalarInvariant η hμ).codRestrict (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) n)
      (fun q => AddSubgroup.torsionBy.nsmul_iff.mpr (scalarInvariant_torsion η hμ q)))

/-- Converting the scalar value back to the rational circle recovers the
actual Brauer invariant. -/
theorem scalarH2Value_invariant
    (q : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))) :
    ZMod.toRatAddCircle n (scalarH2Value η hμ q) = scalarInvariant η hμ q :=
  ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv_toRat n _

/-- Injectivity of the Kummer--Brauer map is the precise arithmetic
injectivity input; no degree-two coefficient isomorphism is assumed. -/
theorem scalarH2Value_injective
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n)) :
    Function.Injective (scalarH2Value η hμ) := by
  intro q q' h
  apply (scalarKummerEquiv η hμ).injective
  apply hKB
  apply (invMap F).injective
  change scalarInvariant η hμ q = scalarInvariant η hμ q'
  rw [← scalarH2Value_invariant, ← scalarH2Value_invariant, h]

variable (a : Fˣ) (β : (SeparableClosure F)ˣ)
  (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)

/-- The fundamental scalar class determined by the unramified Kummer cup. -/
def scalarFundamentalClass : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) :=
  (scalarKummerEquiv η hμ).symm (H2pi _ _ (unramifiedKummerCup a β hβ hμ))

/-- The fundamental scalar class has coordinate one. -/
theorem scalarFundamentalClass_value (ha : IsUniformizer F a) :
    scalarH2Value η hμ (scalarFundamentalClass η hμ a β hβ) = 1 := by
  apply ZMod.toRatAddCircle_injective n
  rw [scalarH2Value_invariant]
  change invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
    (scalarKummerEquiv η hμ ((scalarKummerEquiv η hμ).symm
      (H2pi _ _ (unramifiedKummerCup a β hβ hμ))))) = _
  rw [(scalarKummerEquiv η hμ).apply_symm_apply, unramifiedKummerCup_invariant a β hβ hμ ha]
  simpa using (ZMod.toRatAddCircle_natCast n 1).symm

include hβ in
/-- The scalar invariant is onto because the normalized uniformizer cup
supplies its generator. -/
theorem scalarH2Value_surjective (ha : IsUniformizer F a) :
    Function.Surjective (scalarH2Value η hμ) := by
  intro x
  refine ⟨x.val • scalarFundamentalClass η hμ a β hβ, ?_⟩
  rw [map_nsmul, scalarFundamentalClass_value η hμ a β hβ ha]
  simp

/-- The tame Kummer character, in the chosen primitive-root coordinate. -/
def tameKummerCharacter (g : (Field.absoluteGaloisGroup F)) : ZMod n :=
  η.symm (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F g))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [NeZero n] in
/-- The Kummer character is continuous. -/
theorem tameKummerCharacter_continuous : Continuous (tameKummerCharacter η a β hβ) :=
  (continuous_of_discreteTopology : Continuous η.symm).comp
    (((mem_Z1_iff.mp (kummerCocycle_mem_Z1 hβ)).1).comp (absoluteGaloisGroupRestrictEquiv F).continuous)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [NeZero n] in
include hμ in
/-- With fixed roots of unity the Kummer character is additive. -/
theorem tameKummerCharacter_mul (g h : (Field.absoluteGaloisGroup F)) :
    tameKummerCharacter η a β hβ (g * h) =
      tameKummerCharacter η a β hβ g + tameKummerCharacter η a β hβ h := by
  have hk := (mem_Z1_iff.mp (kummerCocycle_mem_Z1 hβ)).2
    (absoluteGaloisGroupRestrictEquiv F g) (absoluteGaloisGroupRestrictEquiv F h)
  change η.symm (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F (g * h))) = _
  rw [map_mul, hk, hμ, map_add, add_comm]
  rfl

/-- The scalar unramified--Kummer cup as a cochain on the actual local
Galois group. -/
def normalizedScalarCup :
    (contCochains (ZMod n) (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))).X 2 :=
  scalarCup n (urCharN F n) (tameKummerCharacter η a β hβ)
    (continuous_urCharN (K := F) (n := n)) (tameKummerCharacter_continuous η a β hβ)

include hμ in
/-- The normalized scalar cup is a two-cocycle. -/
theorem normalizedScalarCup_cycle :
    ((contCochains (ZMod n) (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))).d 2 3).hom
      (normalizedScalarCup η a β hβ) = 0 :=
  scalarCup_cycle n _ _ _ _ (urCharN_mul (K := F) (n := n))
    (tameKummerCharacter_mul η hμ a β hβ)

/-- The coefficient dictionary identifies the scalar cup with the actual
Kummer cup, fixing the orientation at the level of cocycle representatives. -/
theorem scalarKummerEquiv_cup :
    scalarKummerEquiv η hμ
      (kerToH2 ⟨normalizedScalarCup η a β hβ, normalizedScalarCup_cycle η hμ a β hβ⟩) =
        H2pi _ _ (unramifiedKummerCup a β hβ hμ) := by
  rw [scalarKummerEquiv, explicitMap2Equiv_apply]
  change explicitMap2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))
      (AbsoluteGaloisGroup F) (KummerCoeff F n) (absoluteGaloisGroupRestrictEquiv F).symm
      ((ScalarCoeff.equiv (ZMod n)).toAddEquiv.trans η).toAddMonoidHom
      continuous_of_discreteTopology _
      (H2pi _ _ ⟨_, mem_Z2_of_d_eq_zero _ (normalizedScalarCup_cycle η hμ a β hβ)⟩) = _
  erw [explicitMap2_mk]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  rw [cocyclesMap2_apply, unramifiedKummerCup_apply]
  change η (unramifiedCharacter n g * η.symm
      (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F
        ((absoluteGaloisGroupRestrictEquiv F).symm h)))) =
    (unramifiedCharacter n g).val • kummerCocycle hβ h
  rw [(absoluteGaloisGroupRestrictEquiv F).apply_symm_apply]
  have hη (x y : ZMod n) : η (x * y) = x • η y :=
    (η.toAddMonoidHom.toZModLinearMap n).map_smul x y
  rw [hη, η.apply_symm_apply]
  conv_lhs => rw [← ZMod.natCast_zmod_val (unramifiedCharacter n g)]
  exact Nat.cast_smul_eq_nsmul (ZMod n) _ _

/-- The scalar cocycle with formula `u(g)κ(h)` has invariant `1/n`. -/
theorem normalizedScalarCup_invariant (ha : IsUniformizer F a) :
    scalarInvariant η hμ
      (kerToH2 ⟨normalizedScalarCup η a β hβ, normalizedScalarCup_cycle η hμ a β hβ⟩) =
        ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
  change invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
    (scalarKummerEquiv η hμ _)) = _
  rw [scalarKummerEquiv_cup]
  exact unramifiedKummerCup_invariant a β hβ hμ ha

/-- The local scalar invariant restricted to the two-cocycles of the actual
continuous cochain complex. -/
def scalarCycleValue :
    LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom →ₗ[ZMod n] ZMod n :=
  ((scalarH2Value η hμ).comp
    (kerToH2 (k := ZMod n) (G := Field.absoluteGaloisGroup F)
      (M := ScalarCoeff (ZMod n)))).toZModLinearMap n

/-- Self-injectivity of the residue ring extends the scalar invariant to
all degree-two cochains. -/
theorem scalarCoordinate_extension_exists :
    ∃ c : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).X 2 →ₗ[ZMod n] ZMod n,
      ∀ z : LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d 2 3).hom,
        c (z : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).X 2) = scalarCycleValue η hμ z := by
  have : Module.Injective (ZMod n) (ZMod n) :=
    ZInQ.Contrib.CloudB3RC53.SelmerDuality.selfInjective_of_frobeniusForm
      (ZMod.toRatAddCircle n) (fun x hx => by
        have h := hx 1
        rw [mul_one, ZMod.toRatAddCircle_eq_zero] at h
        exact h)
  exact Module.Injective.out
    (LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom).subtype Subtype.val_injective (scalarCycleValue η hμ)

/-- A cochain-level scalar coordinate extending the actual local invariant.
Its value on cocycles is independent of the chosen extension. -/
def scalarCoordinate :
    (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).X 2 →ₗ[ZMod n] ZMod n :=
  Classical.choose (scalarCoordinate_extension_exists η hμ)

/-- On cycles the cochain coordinate is exactly the local Brauer invariant
read in `ℤ/nℤ`. -/
theorem scalarCoordinate_cycles
    (z : LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom) :
    scalarCoordinate η hμ (z : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).X 2) = scalarH2Value η hμ (kerToH2 z) :=
  Classical.choose_spec (scalarCoordinate_extension_exists η hμ) z

include hβ in
/-- The actual scalar coordinate kills coboundaries, detects their kernel
on cocycles, and is onto. The only arithmetic injectivity hypothesis is the
Kummer--Brauer injection. -/
theorem scalarCoordinate_isCoordinate
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n))
    (ha : IsUniformizer F a) :
    LocalDegreeTwoCoordinate (M := ScalarCoeff (ZMod n)) (scalarCoordinate η hμ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hd : ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).d 2 3).hom
        (((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d 1 2).hom x) = 0 := by
      have h := congrArg (fun f => ModuleCat.Hom.hom f x)
        ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d_comp_d 1 2 3)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    change scalarCoordinate η hμ
      (((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).d 1 2).hom x) = (0 : ZMod n)
    have he := scalarCoordinate_cycles η hμ ⟨_, hd⟩
    rw [he]
    have hq : kerToH2 ⟨_, hd⟩ = 0 := (kerToH2_eq_zero_iff ⟨_, hd⟩).mpr ⟨x, rfl⟩
    rw [hq, map_zero]
  · intro z hz hcz
    change scalarCoordinate η hμ z = (0 : ZMod n) at hcz
    apply (kerToH2_eq_zero_iff ⟨z, hz⟩).mp
    apply scalarH2Value_injective η hμ hKB
    rw [map_zero, ← scalarCoordinate_cycles η hμ ⟨z, hz⟩]
    exact hcz
  · intro m
    obtain ⟨q, hq⟩ := scalarH2Value_surjective η hμ a β hβ ha
      (ScalarCoeff.equiv (ZMod n) m)
    obtain ⟨z, hz⟩ := kerToH2_surjective
      (k := ZMod n) (G := Field.absoluteGaloisGroup F) (M := ScalarCoeff (ZMod n)) q
    refine ⟨z, z.2, ?_⟩
    change scalarCoordinate η hμ
      (z : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).X 2) = ScalarCoeff.equiv (ZMod n) m
    rw [scalarCoordinate_cycles, hz, hq]

/-- The scalar coordinate is oriented by the actual unramified--Kummer
cup, with no nonzero normalization factor left unspecified. -/
theorem scalarCoordinate_normalized (ha : IsUniformizer F a) :
    LocalDegreeTwoNormalized (M := ScalarCoeff (ZMod n)) (scalarCoordinate η hμ)
      (urCharN F n) (tameKummerCharacter η a β hβ) := by
  have ht : scalarCoordinate η hμ (normalizedScalarCup η a β hβ) = 1 := by
    calc
      _ = scalarH2Value η hμ
          (kerToH2 ⟨normalizedScalarCup η a β hβ, normalizedScalarCup_cycle η hμ a β hβ⟩) :=
        scalarCoordinate_cycles η hμ _
      _ = 1 := by
        apply ZMod.toRatAddCircle_injective n
        rw [scalarH2Value_invariant, normalizedScalarCup_invariant η hμ a β hβ ha]
        simpa using (ZMod.toRatAddCircle_natCast n 1).symm
  intro m z hz
  have he : z = ScalarCoeff.equiv (ZMod n) m • normalizedScalarCup η a β hβ := by
    apply contCochains_ext
    intro v
    have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
    rw [hv]
    change evalTwo (ZMod n) (ScalarCoeff (ZMod n)) (v 0) (v 1) z =
      evalTwo (ZMod n) (ScalarCoeff (ZMod n)) (v 0) (v 1)
        (ScalarCoeff.equiv (ZMod n) m • normalizedScalarCup η a β hβ)
    rw [hz, map_smul]
    apply (ScalarCoeff.equiv (ZMod n)).injective
    change (urCharN F n (v 0) * tameKummerCharacter η a β hβ (v 1)) *
        ScalarCoeff.equiv (ZMod n) m =
      ScalarCoeff.equiv (ZMod n) m *
        (urCharN F n (v 0) * tameKummerCharacter η a β hβ (v 1))
    ring
  change scalarCoordinate η hμ z = ScalarCoeff.equiv (ZMod n) m
  rw [he, map_smul, ht]
  exact mul_one _

end ScalarInvariant

section LocalCoefficients

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M : Type} [CommRing R] [Algebra (ZMod n) R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M] [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M] [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  {ι : Type} [Fintype ι] (b : Basis ι (ZMod n) M)
  (η : ZMod n ≃+ KummerCoeff F n)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)

/-- The full coefficient-valued local degree-two coordinate, obtained by
finite coefficient extension of the actual scalar Brauer invariant. -/
def normalizedCoefficientCoordinate :
    (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M :=
  coefficientCoordinate b (scalarCoordinate η hμ)

/-- The produced coordinate has the two required properties at the actual
local Galois group. -/
theorem normalizedCoefficientCoordinate_spec
    (htriv : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n))
    (a : Fˣ) (β : (SeparableClosure F)ˣ)
    (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)
    (ha : IsUniformizer F a) :
    LocalDegreeTwoCoordinate (normalizedCoefficientCoordinate (R := R) b η hμ) ∧
      LocalDegreeTwoNormalized (normalizedCoefficientCoordinate (R := R) b η hμ)
        (fun g => algebraMap (ZMod n) R (urCharN F n g))
        (fun g => algebraMap (ZMod n) R (tameKummerCharacter η a β hβ g)) :=
  ⟨coefficientCoordinate_isCoordinate (R := R) b (scalarCoordinate η hμ) htriv
      (scalarCoordinate_isCoordinate η hμ a β hβ hKB ha),
    coefficientCoordinate_normalized (R := R) b (scalarCoordinate η hμ) _ _
      (scalarCoordinate_normalized η hμ a β hβ ha)⟩

end LocalCoefficients

section StageAlgebra

variable {n : ℕ} [NeZero n] {T : Type} [AddCommGroup T]

/-- Extending a rank-two residue coefficient module to an arbitrary
coefficient algebra. -/
def coefficientTensorEquiv (A : Type) [CommRing A] [Algebra (ZMod n) A]
    (φ : T ≃+ ZMod n × ZMod n) :
    (A ⊗[ℤ] T) ≃ₗ[A] A × A :=
  (LinearEquiv.baseChange ℤ A T (ZMod n × ZMod n) φ.toIntLinearEquiv).trans
    ((TensorProduct.prodRight ℤ A A (ZMod n) (ZMod n)).trans
      ((ZInQ.Manuscript.RC.CoefModules.mulZModEquiv A n).prodCongr
        (ZInQ.Manuscript.RC.CoefModules.mulZModEquiv A n)))

/-- Residue scalar multiplication commutes with the coefficient-ring
multiplication on every residue coefficient module. -/
theorem residueScalarComm (R M : Type) [CommRing R] [AddCommGroup M]
    [Module R M] [Module (ZMod n) M] : SMulCommClass R (ZMod n) M := by
  refine ⟨fun r s m => ?_⟩
  rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul (ZMod n),
    Nat.cast_smul_eq_nsmul (ZMod n)]
  exact smul_comm r s.val m

/-- The canonical residue module structure is compatible with extension
of scalars to the full coefficient ring. -/
theorem residueScalarTower (R M : Type) [CommRing R] [Algebra (ZMod n) R]
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] :
    IsScalarTower (ZMod n) R M := by
  refine ⟨fun s r m => ?_⟩
  rw [Algebra.smul_def]
  rw [ZInQ.Manuscript.RC.CoefModules.algebraMap_zmod_eq_val R n s, mul_smul,
    Nat.cast_smul_eq_nsmul R]
  conv_rhs => rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul (ZMod n)]

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) (q : HeightOneSpectrum (𝓞 K))

omit [W.IsElliptic] [NeZero i] in
/-- The actual localized coefficient module is killed by the stage
power of two, independently of any local duality assertion. -/
theorem localizedMcoef_nsmul (m : ResMod (locMap K S q) (Mcoef K S W i α)) :
    (2 ^ i) • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (Acoef i)]
  have hzero : ((2 ^ i : ℕ) : Acoef i) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, acoef_two_pow_eq_zero]
  rw [hzero]
  exact zero_smul (Acoef i) m

/-- A finite residue basis of the actual localized stage module. The
basis is constructed from elliptic torsion and the polynomial power basis. -/
theorem localizedMcoef_basis
    [Module (ZMod (2 ^ i)) (ResMod (locMap K S q) (Mcoef K S W i α))]
    (hW : FullTorsion K S W (2 ^ i)) :
    Nonempty (Basis (Fin i ⊕ Fin i) (ZMod (2 ^ i))
      (ResMod (locMap K S q) (Mcoef K S W i α))) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  obtain ⟨φ⟩ := torsS_addEquiv_prod W hW
  let eA : Mcoef K S W i α ≃ₗ[Acoef i] Acoef i × Acoef i :=
    (CoefMod.equiv (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))).symm.trans
      (coefficientTensorEquiv (Acoef i) φ)
  let e : ResMod (locMap K S q) (Mcoef K S W i α) ≃+ Acoef i × Acoef i := eA.toAddEquiv
  let eS := LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap (2 ^ i)) e.bijective
  let pb : PowerBasis (ZMod (2 ^ i)) (Acoef i) :=
    AdjoinRoot.powerBasis' (Polynomial.monic_X_pow i)
  have hdim : pb.dim = i := Polynomial.natDegree_X_pow i
  let bA : Basis (Fin i) (ZMod (2 ^ i)) (Acoef i) := pb.basis.reindex (finCongr hdim)
  exact ⟨(bA.prod bA).map eS.symm⟩

end StageAlgebra

section CharacterDictionary

variable {F : Type} [Field F] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Fixed algebraic roots of unity give the actual trivial action on the
Kummer coefficients of the separable closure. -/
theorem kummerCoefficients_fixed
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F),
      ζ ^ n = 1 → g ζ = ζ)
    (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n) : g • x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.val_injective
  let z : SeparableClosure F := (x.toMul : (SeparableClosure F)ˣ)
  change (g z : AlgebraicClosure F) = (z : AlgebraicClosure F)
  have hz : z ^ n = 1 := by
    have h := (mem_rootsOfUnity n _).mp x.toMul.2
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : (SeparableClosure F)ˣ => (u : SeparableClosure F)) h
  have hza : (z : AlgebraicClosure F) ^ n = 1 := by exact_mod_cast hz
  have he := coe_absoluteGaloisGroupRestrictEquiv_apply (K := F)
    ((absoluteGaloisGroupRestrictEquiv F).symm g) z
  rw [(absoluteGaloisGroupRestrictEquiv F).apply_symm_apply] at he
  exact he.trans (hμ _ _ hza)

variable (a : Fˣ) (β : (SeparableClosure F)ˣ)
  (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)

omit [NeZero n] in
include hβ in
/-- The chosen separable root, read in the algebraic closure, has the same
power equation. -/
theorem algebraicRoot_pow :
    ((β : SeparableClosure F) : AlgebraicClosure F) ^ n =
      algebraMap F (AlgebraicClosure F) (a : F) := by
  have hs : (β : SeparableClosure F) ^ n = algebraMap F (SeparableClosure F) (a : F) := by
    calc
      _ = ((β ^ n : (SeparableClosure F)ˣ) : SeparableClosure F) := by
        rw [Units.val_pow_eq_pow_val]
      _ = ((Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a :
          (SeparableClosure F)ˣ) : SeparableClosure F) :=
        congrArg (fun u : (SeparableClosure F)ˣ => (u : SeparableClosure F)) hβ
      _ = algebraMap F (SeparableClosure F) (a : F) := rfl
  have hv : algebraMap (SeparableClosure F) (AlgebraicClosure F) (β : SeparableClosure F) =
      ((β : SeparableClosure F) : AlgebraicClosure F) := rfl
  have ht : (algebraMap (SeparableClosure F) (AlgebraicClosure F) (β : SeparableClosure F)) ^ n =
      algebraMap F (AlgebraicClosure F) (a : F) := by
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply] using
      congrArg (algebraMap (SeparableClosure F) (AlgebraicClosure F)) hs
  exact (congrArg (fun z : AlgebraicClosure F => z ^ n) hv).symm.trans ht

/-- Reading a nonzero root in the algebraic closure preserves nonvanishing. -/
theorem algebraicRoot_ne_zero : ((β : SeparableClosure F) : AlgebraicClosure F) ≠ 0 :=
  fun h => β.ne_zero (Subtype.val_injective h)

omit [NeZero n] in
/-- The actual Kummer cocycle and the algebraic-closure ratio agree. -/
theorem kummerCocycle_algebraicValue (g : Gal(AlgebraicClosure F/F)) :
    (((kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F g)).toMul :
      (SeparableClosure F)ˣ) : AlgebraicClosure F) =
        ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal
          ((β : SeparableClosure F) : AlgebraicClosure F) g := by
  let s : SeparableClosure F ≃ₐ[F] SeparableClosure F := absoluteGaloisGroupRestrictEquiv F g
  rw [toMul_kummerCocycle]
  change ((Units.map (s : SeparableClosure F →* SeparableClosure F) β * β⁻¹ :
    (SeparableClosure F)ˣ) : AlgebraicClosure F) = _
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass]
  change (algebraMap (SeparableClosure F) (AlgebraicClosure F))
      (s (β : SeparableClosure F) * (β : SeparableClosure F)⁻¹) = _
  rw [map_mul]
  have hs : (s (β : SeparableClosure F) : AlgebraicClosure F) =
      g ((β : SeparableClosure F) : AlgebraicClosure F) :=
    coe_absoluteGaloisGroupRestrictEquiv_apply (K := F) g (β : SeparableClosure F)
  change (s (β : SeparableClosure F) : AlgebraicClosure F) *
      ((β : SeparableClosure F) : AlgebraicClosure F)⁻¹ = _
  rw [hs]
  rfl

/-- A residue coefficient equivalence reads every value as a power of its
chosen primitive root. -/
theorem kummerEquiv_algebraicPower (η : ZMod n ≃+ KummerCoeff F n) (x : ZMod n) :
    (((η x).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x,
    show ((x.val : ℕ) : ZMod n) = x.val • (1 : ZMod n) by simp, map_nsmul]
  simp

/-- The character used in the invariant construction is the exact tame
Kummer logarithm used by the degree-one coordinates. -/
theorem tameKummerCharacter_eq_log (η : ZMod n ≃+ KummerCoeff F n)
    {σ : Field.absoluteGaloisGroup F}
    (hζ : IsPrimitiveRoot (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal
      ((β : SeparableClosure F) : AlgebraicClosure F) σ) n)
    (hη : (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal
        ((β : SeparableClosure F) : AlgebraicClosure F) σ)
    (g : Field.absoluteGaloisGroup F) :
    tameKummerCharacter η a β hβ g =
      kummerLog (algebraicRoot_pow a β hβ) (algebraicRoot_ne_zero β) hζ g := by
  symm
  apply (kummerLog_eq_iff (algebraicRoot_pow a β hβ) (algebraicRoot_ne_zero β) hζ g _).mpr
  rw [← hη, ← kummerEquiv_algebraicPower η]
  change (((η (η.symm (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F g)))).toMul :
    (SeparableClosure F)ˣ) : AlgebraicClosure F) = _
  rw [η.apply_symm_apply]
  exact kummerCocycle_algebraicValue a β hβ g

end CharacterDictionary

/-- A uniformizer, a tame root, and compatible arithmetic Frobenius and
inertia generators. This contains no cohomological coordinate hypothesis. -/
structure TameOrientation (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n] where
  uniformizer : Fˣ
  uniformizer_is : IsUniformizer F uniformizer
  root : AlgebraicClosure F
  root_pow : root ^ n = algebraMap F (AlgebraicClosure F) (uniformizer : F)
  root_ne_zero : root ≠ 0
  frobenius : Gal(AlgebraicClosure F/F)
  frobenius_is : IsArithFrobeniusLift F frobenius
  frobenius_fix : frobenius root = root
  inertia : Gal(AlgebraicClosure F/F)
  inertia_mem : inertia ∈ inertiaSubgroup F
  primitive : IsPrimitiveRoot
    (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal root inertia) n

namespace TameOrientation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n] (D : TameOrientation F n)

/-- The arithmetic unramified character in the chosen orientation. -/
def unramified (_D : TameOrientation F n) : Gal(AlgebraicClosure F/F) → ZMod n := urCharN F n

/-- The exact tame Kummer character of the chosen uniformizer root. -/
def kummer : Gal(AlgebraicClosure F/F) → ZMod n :=
  kummerLog D.root_pow D.root_ne_zero D.primitive

/-- The degree-one coordinates are oriented as the finite and singular
axes: `(1,0)` at Frobenius and `(0,1)` at inertia. -/
theorem character_values [Fact (1 < n)] :
    D.unramified D.frobenius = 1 ∧ D.unramified D.inertia = 0 ∧
      D.kummer D.frobenius = 0 ∧ D.kummer D.inertia = 1 :=
  ⟨urCharN_frobenius D.frobenius_is, urCharN_inertia D.inertia_mem,
    kummerLog_of_fix D.root_pow D.root_ne_zero D.primitive D.frobenius_fix,
    kummerLog_self D.root_pow D.root_ne_zero D.primitive⟩

end TameOrientation

section Existence

open _root_.ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M : Type} [CommRing R] [Algebra (ZMod n) R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M] [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M] [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  {ι : Type} [Fintype ι] (b : Basis ι (ZMod n) M)

include b in
/-- The normalized local degree-two coordinate exists for the actual local
Galois group and any finite free residue coefficient module. The tame symbol
and surjectivity are proved; only Kummer--Brauer injectivity is supplied. -/
theorem exists_normalizedLocalCoordinate
    (hn : n.Coprime (ringChar 𝓀[F]))
    (htriv : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F), ζ ^ n = 1 → g ζ = ζ)
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n)) :
    ∃ (D : TameOrientation F n)
      (c₂ : (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod n) R (D.unramified g))
        (fun g => algebraMap (ZMod n) R (D.kummer g)) := by
  have hnF : IsUnit (n : F) := isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_coprime_ringChar hn)
  have : NeZero (n : SeparableClosure F) := ⟨hnF.natCast_ne_zero_of_algebra⟩
  obtain ⟨π, hπ⟩ := exists_isUniformizer F
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map hnF π
  let βbar : AlgebraicClosure F := (β : SeparableClosure F)
  have hβbar : βbar ^ n = algebraMap F (AlgebraicClosure F) (π : F) := algebraicRoot_pow π β hβ
  have hβ0 : βbar ≠ 0 := algebraicRoot_ne_zero β
  have hπv : (normalizedValuation F π).toAdd = 1 := by
    rw [(isUniformizer_def π).mp hπ, toAdd_ofAdd]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure F) n
  let ζu : (SeparableClosure F)ˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hζu : IsPrimitiveRoot ζu n := hζ.isUnit_unit (NeZero.ne n)
  let η : ZMod n ≃+ KummerCoeff F n := hζu.zmodEquivRootsOfUnity
  have hη1 : ((η 1).toMul : (SeparableClosure F)ˣ) = ζu := by
    simpa using hζu.coe_zmodEquivRootsOfUnity_apply_natCast 1
  let ζbar : rootsOfUnity n (AlgebraicClosure F) :=
    restrictRootsOfUnity (algebraMap (SeparableClosure F) (AlgebraicClosure F)) n (η 1).toMul
  have hζbar : ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      algebraMap (SeparableClosure F) (AlgebraicClosure F) (ζu : SeparableClosure F) := by
    change algebraMap (SeparableClosure F) (AlgebraicClosure F)
      (((η 1).toMul : (SeparableClosure F)ˣ) : SeparableClosure F) = _
    rw [hη1]
  obtain ⟨σ, hσ⟩ := tameChar_surjective hn hβbar hβ0 π.ne_zero hπv ζbar
  have hσval : kummerVal βbar σ.1 = ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) := by
    simpa only [coe_tameChar] using congrArg
      (fun x : rootsOfUnity n (AlgebraicClosure F) => ((x : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) hσ
  have hζuf : IsPrimitiveRoot (ζu : SeparableClosure F) n := by
    change IsPrimitiveRoot ((hζ.isUnit (NeZero.ne n)).unit : SeparableClosure F) n
    rw [IsUnit.unit_spec]
    exact hζ
  have hζσ : IsPrimitiveRoot (kummerVal βbar σ.1) n := by
    rw [hσval, hζbar]
    exact hζuf.map_of_injective (algebraMap (SeparableClosure F) (AlgebraicClosure F)).injective
  have hησ : (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      kummerVal βbar σ.1 := by
    have hval : ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
        (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) := rfl
    exact hval.symm.trans hσval.symm
  obtain ⟨φ, hφ, hφβ⟩ := exists_frobeniusLift_fix hn hβbar hβ0 π.ne_zero hπv
  let D : TameOrientation F n :=
    { uniformizer := π
      uniformizer_is := hπ
      root := βbar
      root_pow := hβbar
      root_ne_zero := hβ0
      frobenius := φ
      frobenius_is := hφ
      frobenius_fix := hφβ
      inertia := σ.1
      inertia_mem := σ.2
      primitive := hζσ }
  let hμs := kummerCoefficients_fixed hμ
  obtain ⟨hc, hnorm⟩ := normalizedCoefficientCoordinate_spec (R := R) b η hμs htriv hKB π β hβ hπ
  refine ⟨D, normalizedCoefficientCoordinate (R := R) b η hμs, hc, ?_⟩
  intro m z hz
  apply hnorm m z
  intro g h
  have hl : tameKummerCharacter η π β hβ h = D.kummer h :=
    tameKummerCharacter_eq_log π β hβ η hζσ hησ h
  exact (hz g h).trans (congrArg (fun x : ZMod n =>
    (algebraMap (ZMod n) R (D.unramified g) * algebraMap (ZMod n) R x) • m) hl.symm)

end Existence

section DerivativeStage

open NumberField IsDedekindDomain _root_.ValuativeRel
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (q : HeightOneSpectrum (𝓞 K))

/-- The normalized degree-two coordinate at an odd derivative stage prime,
for the actual localized stage coefficient module. The full-torsion,
derivative-action and fixed-root inputs have their exact arithmetic types. -/
theorem exists_stageCoordinate (h2 : (2 : 𝓞 K) ∉ q.asIdeal)
    (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q) (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hKB : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.adicCompletion K) (2 ^ i))) :
    ∃ (D : TameOrientation (q.adicCompletion K) (2 ^ i))
      (c₂ : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
          ResMod (locMap K S q) (Mcoef K S W i α)),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.unramified g))
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.kummer g)) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  let M := ResMod (locMap K S q) (Mcoef K S W i α)
  letI : Module (ZMod (2 ^ i)) M := AddCommGroup.zmodModule (localizedMcoef_nsmul W i α q)
  letI : SMulCommClass (Acoef i) (ZMod (2 ^ i)) M := residueScalarComm (Acoef i) M
  letI : IsScalarTower (ZMod (2 ^ i)) (Acoef i) M := residueScalarTower (Acoef i) M
  letI : DistribMulAction (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (DistribMulAction (Gloc K q) M)
  letI : SMulCommClass (Field.absoluteGaloisGroup (q.adicCompletion K)) (Acoef i) M :=
    inferInstanceAs (SMulCommClass (Gloc K q) (Acoef i) M)
  letI : ContinuousSMul (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (ContinuousSMul (Gloc K q) M)
  obtain ⟨b⟩ := localizedMcoef_basis W i α q hW
  have hp : (ringChar 𝓀[q.adicCompletion K]).Prime :=
    (CharP.char_is_prime_or_zero 𝓀[q.adicCompletion K] _).resolve_right
      (CharP.char_ne_zero_of_finite 𝓀[q.adicCompletion K] _)
  have hnd : ¬ ringChar 𝓀[q.adicCompletion K] ∣ 2 := by
    rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hn : (2 ^ i).Coprime (ringChar 𝓀[q.adicCompletion K]) :=
    Nat.Coprime.pow_left i ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  obtain ⟨D, c₂, hc, hnorm⟩ := exists_normalizedLocalCoordinate (R := Acoef i) b hn htriv hμ hKB
  exact ⟨D, c₂, hc, hnorm⟩

end DerivativeStage

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo
