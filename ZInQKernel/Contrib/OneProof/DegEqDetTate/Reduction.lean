import ZInQKernel.Contrib.OneProof.CharPolyIndepOfEllAlgClosed
import ZInQKernel.Contrib.OneProof.DegEqDetTate.Algebra
import ZInQKernel.Contrib.OneProof.DegEqDetTate.TateIndex
import ZInQKernel.Contrib.OneProof.H.TailQ

/-!
# deg-det, part 1: `DegEqDetTate` from `DegHomogPoly` and `DegLadicIsogeny` / `SepDegKernel`

Task deg-det (2026-11-16), report `docs/research/deg-det.md`, scratch `scratch/deg-det/`.

charpoly-ell reduced the open field `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` to the printed leaf
`CharPolyEll.DegEqDetTate` (`deg φ = det T_ℓ(φ)` over the function-field degree `CharPolyEll.degEnd`) and the
open field `HomFreeFiniteAlgClosed`. This file proves `DegEqDetTate` from

* `DegHomogPoly` (**LEAF**, printed form): the degree is a homogeneous polynomial function of degree `2g` on
  `End(A)` (Mumford §19; the input from the theorem of the cube and Riemann–Roch);
* `DegLadicIsogeny` (**GLUE**, open): `|det V_ℓ(ψ)|_ℓ = |deg ψ|_ℓ` for an isogeny `ψ`, `ℓ ≠ char k` (the
  count of `ker ψ` on `ℓ`-power torsion; see the report for its further reduction);
* `HomFreeFiniteAlgClosed` (open field of the same bundle; only `End(A)` finite over `ℤ` is used),

and the algebra of Mumford's proof (`DegEqDetTate/Algebra.lean`, `det_eq_deg_abstract`). The multiplicativity
of `degEnd` on isogenies (tower law of function fields) is proved here.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open scoped TensorProduct

noncomputable section

namespace ZInQ.Contrib.OneProof.DegDet

open ZInQ.Contrib.OneProof.CharPolyEll

/-! ## 1. The two statements -/

/-- **LEAF (printed form): the degree is a homogeneous polynomial function of degree `2g` on `End(A)`.**
D. Mumford, *Abelian varieties* (1970), §19 (UNVERIFIED locator: the statement, used in the proof of §19
Thm 4, that `deg : End(X) → ℤ` is a homogeneous polynomial function of degree `2g`, from §16 and the theorem
of the cube; also Milne, *Abelian varieties* (2008 notes), §12, UNVERIFIED). `k` is algebraically closed, as
throughout the book. Stated for every finite family `e₁, …, e_r ∈ End(A)`: `x ↦ deg(∑ xᵢ eᵢ)` is given by a
homogeneous rational polynomial of degree `2 dim A`; this is the printed statement read in coordinates (a
polynomial function on the free `ℤ`-module `End(A)` restricts to one on any family). `deg` is the genuine
function-field degree `CharPolyEll.degEnd` (`0` for non-isogenies, Mumford's convention). -/
def DegHomogPoly : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (r : ℕ) (e : Fin r → PkgI3.AbVar.End A),
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, ((degEnd (∑ i, x i • e i) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) N

/-- **GLUE (open): `|det V_ℓ(ψ)|_ℓ = |deg ψ|_ℓ` for an isogeny `ψ` and `ℓ ≠ char k`.** In Mumford's proof
(§19 Thm 4) this is the comparison of `deg ψ` with the order of `ker ψ ∩ A[ℓ^∞]`: the `ℓ`-part of `deg ψ`
is the `ℓ`-part of `#ker ψ(k)` (the inseparable degree is a power of `char k`, the separable degree is the
number of points of a fibre), and `#(ker ψ ∩ A[ℓ^∞]) = |det T_ℓ ψ|_ℓ⁻¹` (elementary divisors of `T_ℓ ψ`,
`A[ℓⁿ] ≅ (ℤ/ℓⁿ)^{2g}`). It is a consequence of the printed `DegEqDetTate`; it is listed as glue because its
proof needs no polynomial structure of `deg` (report §4). Same `V_ℓ`, basis convention and `degEnd` as
`DegEqDetTate`. -/
def DegLadicIsogeny : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → PkgI3.AbVar.IsIsogenyMor ψ.hom →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        ‖(LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ])).det‖ =
          ‖(degEnd ψ : ℚ_[ℓ])‖

/-! ## 2. `degEnd` is multiplicative on isogenies -/

section Mul

variable {k : Type} [Field k]

attribute [local instance] isIntegral_left

/-- A surjective morphism of irreducible schemes maps the generic point to the generic point. -/
theorem map_genericPoint {X Y : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (hf : Function.Surjective f) : f (genericPoint X) = genericPoint Y := by
  have h1 := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ_of_surjective hf, closure_univ] at h1
  exact h1.eq (genericPoint_spec Y)

/-- The stalk at a point equal to the generic point of an integral scheme is a field. -/
theorem isField_stalk {X : Scheme} [IsIntegral X] (x : X) (hx : x = genericPoint X) :
    IsField (X.presheaf.stalk x) := by
  subst hx
  exact Field.toIsField X.functionField

/-- Tower law for stalk maps between stalks that are fields. -/
theorem finrank_stalk_tower {X : Scheme} (x y z : X) (hx : IsField (X.presheaf.stalk x))
    (hy : IsField (X.presheaf.stalk y)) (hz : IsField (X.presheaf.stalk z))
    (s1 : X.presheaf.stalk z ⟶ X.presheaf.stalk y) (s2 : X.presheaf.stalk y ⟶ X.presheaf.stalk x) :
    @Module.finrank (X.presheaf.stalk z) (X.presheaf.stalk x) _ _ (s1 ≫ s2).hom.toAlgebra.toModule =
      @Module.finrank (X.presheaf.stalk z) (X.presheaf.stalk y) _ _ s1.hom.toAlgebra.toModule *
        @Module.finrank (X.presheaf.stalk y) (X.presheaf.stalk x) _ _ s2.hom.toAlgebra.toModule := by
  letI : Field (X.presheaf.stalk z) := hz.toField
  letI : Field (X.presheaf.stalk y) := hy.toField
  letI a1 : Algebra (X.presheaf.stalk z) (X.presheaf.stalk y) := s1.hom.toAlgebra
  letI a2 : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) := s2.hom.toAlgebra
  letI a3 : Algebra (X.presheaf.stalk z) (X.presheaf.stalk x) := (s1 ≫ s2).hom.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk z) (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  exact (Module.finrank_mul_finrank (X.presheaf.stalk z) (X.presheaf.stalk y)
    (X.presheaf.stalk x)).symm

/-- Transport of the stalk-map degree along a point equal to the generic point. -/
theorem finrank_stalkMap_transport {X : Scheme} [IsIntegral X] (g : X ⟶ X) (y : X)
    (hy : y = genericPoint X) :
    @Module.finrank (X.presheaf.stalk (g y)) (X.presheaf.stalk y) _ _
        (g.stalkMap y).hom.toAlgebra.toModule =
      @Module.finrank (X.presheaf.stalk (g (genericPoint X))) (X.presheaf.stalk (genericPoint X)) _ _
        (g.stalkMap (genericPoint X)).hom.toAlgebra.toModule := by
  subst hy
  rfl

/-- An endomorphism of nonzero degree is an isogeny. -/
theorem isIsogenyMor_of_degEnd_ne_zero {A : PkgI3.AbVar k} {ψ : PkgI3.AbVar.End A}
    (h : degEnd ψ ≠ 0) : PkgI3.AbVar.IsIsogenyMor ψ.hom := by
  classical
  by_contra hn
  apply h
  unfold degEnd
  rw [if_neg hn]

/-- **`deg(ψχ) = deg ψ · deg χ` for isogenies** (tower law of function fields). -/
theorem degEnd_mul_of_isIsogeny {A : PkgI3.AbVar k} (ψ χ : PkgI3.AbVar.End A)
    (hψ : PkgI3.AbVar.IsIsogenyMor ψ.hom) (hχ : PkgI3.AbVar.IsIsogenyMor χ.hom) :
    degEnd (ψ * χ) = degEnd ψ * degEnd χ := by
  classical
  have hmul : (ψ * χ).hom.left = χ.hom.left ≫ ψ.hom.left := rfl
  have := hψ.1
  have := hψ.2
  have := hχ.1
  have := hχ.2
  have hc : PkgI3.AbVar.IsIsogenyMor (ψ * χ).hom := by
    refine ⟨?_, ?_⟩ <;> rw [hmul] <;> infer_instance
  set X := A.X.left
  set e0 := genericPoint X
  have hχe0 : χ.hom.left e0 = e0 := map_genericPoint _ hχ.2.surj
  have hψe0 : ψ.hom.left e0 = e0 := map_genericPoint _ hψ.2.surj
  have hψχe0 : ψ.hom.left (χ.hom.left e0) = e0 := by rw [hχe0, hψe0]
  unfold degEnd
  rw [if_pos hc, if_pos hψ, if_pos hχ]
  change @Module.finrank (X.presheaf.stalk ((χ.hom.left ≫ ψ.hom.left) e0)) (X.presheaf.stalk e0) _ _
      ((χ.hom.left ≫ ψ.hom.left).stalkMap e0).hom.toAlgebra.toModule = _
  have key := finrank_stalk_tower e0 (χ.hom.left e0) (ψ.hom.left (χ.hom.left e0))
    (isField_stalk e0 rfl) (isField_stalk _ hχe0) (isField_stalk _ hψχe0)
    (ψ.hom.left.stalkMap (χ.hom.left e0)) (χ.hom.left.stalkMap e0)
  rw [← Scheme.Hom.stalkMap_comp, finrank_stalkMap_transport ψ.hom.left (χ.hom.left e0) hχe0] at key
  exact key

end Mul

/-! ## 3. The reduction -/

/-- **`DegEqDetTate` from `DegHomogPoly`, `DegLadicIsogeny` and `End(A)` finite over `ℤ`.** -/
theorem degEqDetTate_of_degHomogPoly (hP : DegHomogPoly) (hL : DegLadicIsogeny)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : DegEqDetTate := by
  intro k _ _ A ψ ℓ _ hℓ I _ _ b
  classical
  obtain ⟨-, hfin, -, -⟩ := hH k A A
  obtain ⟨R, hR, hRψ⟩ := IsIntegral.of_finite ℤ ψ
  obtain ⟨g, N, -, hN, hpoly⟩ := hP k A R.natDegree (fun i => ψ ^ (i : ℕ))
  rw [← rho_apply b ψ]
  refine det_eq_deg_abstract ψ degEnd R hR (by rw [aeval_def]; exact hRψ) (2 * g) N hN hpoly
    (degEnd_one A) (fun χ φ hχ hφ => degEnd_mul_of_isIsogeny χ φ
      (isIsogenyMor_of_degEnd_ne_zero hχ) (isIsogenyMor_of_degEnd_ne_zero hφ)) (rho b) ?_
  intro χ hχ
  rw [rho_apply]
  exact hL k A χ ℓ hℓ (isIsogenyMor_of_degEnd_ne_zero hχ) I b

/-- **`CharPolyIndepOfEllAlgClosed` from `DegHomogPoly`, `DegLadicIsogeny` and
`HomFreeFiniteAlgClosed`** (with charpoly-ell's `charPolyIndepOfEllAlgClosed_of_degEqDetTate`). -/
theorem charPolyIndepOfEllAlgClosed_of_degHomogPoly (hP : DegHomogPoly) (hL : DegLadicIsogeny)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  charPolyIndepOfEllAlgClosed_of_degEqDetTate (degEqDetTate_of_degHomogPoly hP hL hH) hH

/-! ## 4. `DegLadicIsogeny` from the separable degree and Mumford's torsion count -/

/-- **LEAF (printed form): the degree of an isogeny is `#ker` times a power of the characteristic exponent.**
D. Mumford, *Abelian varieties* (1970), §4 and §7 (UNVERIFIED locators: for an isogeny `f`, `ker f` is a
finite group of order `deg_s f`, and `deg_i f` is a power of `p = char k`); also Milne, *Abelian varieties*
(2008 notes), §7 (UNVERIFIED). `k` algebraically closed; the kernel is taken on the points over
`k̄ = AlgebraicClosure k` (the points carrying `T_ℓ` in the kernel; `k → k̄` is an isomorphism since `k` is
algebraically closed, so these are Mumford's closed points); `ringExpChar k` is `1` in characteristic `0` and
`p` in characteristic `p`. `deg` is the genuine function-field degree `degEnd`. -/
def SepDegKernel : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A),
    PkgI3.AbVar.IsIsogenyMor ψ.hom →
      Finite (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) ψ).ker ∧
        ∃ e : ℕ, degEnd ψ =
          Nat.card (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) ψ).ker * ringExpChar k ^ e

theorem coprime_ringExpChar_pow {k : Type} [Field k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓk : (ℓ : k) ≠ 0)
    (e : ℕ) : ℓ.Coprime (ringExpChar k ^ e) := by
  obtain ⟨q, hq⟩ : ∃ q, ringExpChar k = q := ⟨_, rfl⟩
  rw [hq]
  have h : ExpChar k q := ringExpChar.of_eq hq
  cases h with
  | zero => simp
  | prime hp =>
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_primes hℓ.out hp]
    rintro rfl
    exact hℓk (CharP.cast_eq_zero k ℓ)

/-- **`DegLadicIsogeny` from `SepDegKernel` and `mumfordTorsionAlgClosed`.** `|det T_ℓ ψ|_ℓ = |#ker ψ|_ℓ`
(`TateIndex.norm_det_map_eq`, elementary divisors, with `#A[ℓⁿ] = ℓ^{2gn}`) and
`|deg ψ|_ℓ = |#ker ψ|_ℓ` (the inseparable part is prime to `ℓ`). -/
theorem degLadicIsogeny_of_sepDegKernel (hS : SepDegKernel) (hM : AvSplit.MumfordTorsionAlgClosed) :
    DegLadicIsogeny := by
  intro k _ _ A ψ ℓ _ hℓ hiso I _ _ b
  classical
  obtain ⟨hfin, e, hdeg⟩ := hS k A ψ hiso
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  have hT := AvSplit.torsionStructure_of_mumford hM k
  have hcard : ∀ n : ℕ, Nat.card (T5Torsion.TateFree.tb ℓ (Additive (A.Pt (AlgebraicClosure k))) n) =
      ℓ ^ (n * (2 * g)) := by
    intro n
    obtain ⟨e', -⟩ := hT (ObjBridge.toGrp A) g (ℓ ^ n) hg
      (pow_pos (Fact.out : ℓ.Prime).pos n) (by push_cast; exact pow_ne_zero _ hℓ)
    rw [← Nat.card_congr (T5Torsion.TateFree.torsionEquivTb A ℓ n), Nat.card_congr e', Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
  set φ : Additive (A.Pt (AlgebraicClosure k)) →+ Additive (A.Pt (AlgebraicClosure k)) :=
    MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) ψ) with hφ
  let eK : φ.ker ≃ (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) ψ).ker :=
    { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
      invFun := fun x => ⟨Additive.ofMul x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite φ.ker := Finite.of_equiv _ eK.symm
  have key := TateIndex.norm_det_map_eq (2 * g) hcard φ
  haveI : Module.Free ℤ_[ℓ] (A.T ℓ) :=
    Module.Free.of_equiv (T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard).some.symm
  haveI : Module.Finite ℤ_[ℓ] (A.T ℓ) :=
    Module.Finite.equiv (T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard).some.symm
  rw [LinearMap.det_toMatrix b, LinearMap.det_baseChange]
  change ‖((LinearMap.det (PkgI3.AbVar.homT (ℓ := ℓ) ψ) : ℤ_[ℓ]) : ℚ_[ℓ])‖ = _
  rw [← PadicInt.norm_def]
  change ‖LinearMap.det (PkgI3.Tate.map φ)‖ = _
  rw [key, hdeg, Nat.card_congr eK, Nat.cast_mul, norm_mul,
    show ‖((ringExpChar k ^ e : ℕ) : ℚ_[ℓ])‖ = 1 from
      Padic.norm_natCast_eq_one_iff.mpr (coprime_ringExpChar_pow ℓ hℓ e), _root_.mul_one,
    PadicInt.norm_def, PadicInt.coe_natCast]

/-- **`DegEqDetTate` from two printed leaves and two open fields** (no glue left open). -/
theorem degEqDetTate_of_printed (hP : DegHomogPoly) (hS : SepDegKernel)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    DegEqDetTate :=
  degEqDetTate_of_degHomogPoly hP (degLadicIsogeny_of_sepDegKernel hS hM) hH

/-- **`CharPolyIndepOfEllAlgClosed` from the printed leaves `DegHomogPoly`, `SepDegKernel` and the open
fields `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`.** -/
theorem charPolyIndepOfEllAlgClosed_of_printed (hP : DegHomogPoly) (hS : SepDegKernel)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  charPolyIndepOfEllAlgClosed_of_degEqDetTate (degEqDetTate_of_printed hP hS hM hH) hH

end ZInQ.Contrib.OneProof.DegDet
