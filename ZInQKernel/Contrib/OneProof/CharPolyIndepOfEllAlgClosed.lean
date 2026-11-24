import ZInQKernel.Contrib.AVB1.AlgClosed

/-!
# charpoly-ell: `CharPolyIndepOfEllAlgClosed` from `deg φ = det T_ℓ(φ)`

Task charpoly-ell (2026-11-16), report `docs/research/charpoly-ell.md`, scratch `scratch/charpoly-ell/`.

Mumford, *Abelian varieties* (1970), §19, Theorem 4 has two assertions about `φ ∈ End(X)`, `X` an abelian
variety over an algebraically closed field `k` and `ℓ ≠ char k`: `deg φ = det T_ℓ(φ)`, and the characteristic
polynomial of `T_ℓ(φ)` has integer coefficients independent of `ℓ`. The open field
`ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` is (a specialization of) the second. This file proves it from

* `DegEqDetTate` (new leaf): the first assertion, over the genuine degree `degEnd` (the degree
  `[K(A) : ψ^* K(A)]` of the function-field extension for a finite surjective `ψ`, `0` otherwise);
* `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (open field, Mumford §19 Thm 3), of which only
  `Module.Finite ℤ (End A)` is used (so that `φ` is integral over `ℤ`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open scoped TensorProduct

noncomputable section

namespace ZInQ.Contrib.OneProof.CharPolyEll

/-! ## 1. Pure algebra -/

section Algebra

variable {F : Type*} [Field F] [CharZero F]

/-- A polynomial over a field of characteristic `0` taking integer values at all integers has rational
coefficients (Lagrange interpolation at `0, 1, …, natDegree`). -/
theorem exists_rat_of_int_values (C : F[X]) (f : ℤ → ℤ) (hf : ∀ n : ℤ, C.eval (n : F) = f n) :
    ∃ Q : ℚ[X], Q.map (algebraMap ℚ F) = C := by
  classical
  set s : Finset ℕ := Finset.range (C.natDegree + 1) with hs
  have hinjQ : Set.InjOn (fun i : ℕ => (i : ℚ)) ↑s := fun a _ b _ h => by simp only at h; exact_mod_cast h
  set Q : ℚ[X] := Lagrange.interpolate s (fun i : ℕ => (i : ℚ)) (fun i : ℕ => ((f i : ℤ) : ℚ))
    with hQ
  refine ⟨Q, ?_⟩
  have hdegQ : Q.degree < s.card := Lagrange.degree_interpolate_lt _ hinjQ
  have hdegC : C.degree < s.card := by
    rw [hs, Finset.card_range]
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_self _)
  set t : Finset F := s.image (fun i : ℕ => (i : F)) with ht
  have htcard : t.card = s.card :=
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq t
  · rw [htcard]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ hdegC)
    rw [Polynomial.degree_map]
    exact hdegQ
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have h := Lagrange.eval_interpolate_at_node (fun i : ℕ => ((f i : ℤ) : ℚ)) hinjQ hi
    rw [Polynomial.eval_map, Polynomial.eval₂_at_natCast,
      show Polynomial.eval (i : ℚ) Q = ((f i : ℤ) : ℚ) from h, map_intCast]
    have := hf (i : ℤ)
    push_cast at this
    exact this.symm

/-- A monic rational polynomial whose image is the characteristic polynomial of a matrix annihilated by a
monic integer polynomial has integer coefficients. -/
theorem exists_int_of_rat {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I F) (Q : ℚ[X])
    (hQ : Q.map (algebraMap ℚ F) = M.charpoly) (R : ℤ[X]) (hR : R.Monic) (hRM : aeval M R = 0) :
    ∃ Z : ℤ[X], Z.Monic ∧ Z.map (Int.castRingHom ℚ) = Q := by
  classical
  have hQm : Q.Monic := by
    have h1 : (Q.map (algebraMap ℚ F)).Monic := hQ ▸ Matrix.charpoly_monic M
    rw [Polynomial.Monic, Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ F).injective] at h1
    exact (algebraMap ℚ F).injective (h1.trans (map_one _).symm)
  set Ω := AlgebraicClosure F
  set M' : Matrix I I Ω := (algebraMap F Ω).mapMatrix M with hM'def
  have hM' : M'.charpoly = Q.map (algebraMap ℚ Ω) := by
    rw [hM'def, RingHom.mapMatrix_apply, Matrix.charpoly_map, ← hQ, Polynomial.map_map]
    congr 1
  have hRM' : aeval M' R = 0 := by
    have h := Polynomial.aeval_algHom_apply ((algebraMap F Ω).mapMatrix.toIntAlgHom) M R
    rw [hRM, map_zero] at h
    exact h
  have hroot : ∀ x : Ω, (Q.map (algebraMap ℚ Ω)).IsRoot x → IsIntegral ℤ x := by
    intro x hx
    rw [← hM', ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hx
    have h1 := spectrum.subset_polynomial_aeval M' (R.map (algebraMap ℤ Ω)) ⟨x, hx, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hRM', spectrum.mem_iff, sub_zero] at h1
    have h2 : eval x (R.map (algebraMap ℤ Ω)) = 0 := by
      by_contra hne
      exact h1 ((isUnit_iff_ne_zero.mpr hne).map _)
    exact ⟨R, hR, by rw [Polynomial.eval₂_eq_eval_map]; exact h2⟩
  have hcoeff : ∀ n, IsIntegral ℤ (Q.coeff n) := by
    intro n
    have hlc : IsIntegral ℤ (Q.map (algebraMap ℚ Ω)).leadingCoeff := by
      rw [(hQm.map _).leadingCoeff]; exact isIntegral_one
    have h := Polynomial.isIntegral_coeff_of_factors (R := ℤ) (Q.map (algebraMap ℚ Ω)) hlc
      (IsAlgClosed.splits _) hroot n
    rw [Polynomial.coeff_map] at h
    exact (isIntegral_algHom_iff ((algebraMap ℚ Ω).toIntAlgHom) (algebraMap ℚ Ω).injective).mp h
  have hlifts : Q ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (hcoeff n)
    exact ⟨y, hy⟩
  obtain ⟨Z, hZ, -, hZm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hQm
  exact ⟨Z, hZm, hZ⟩

/-- The characteristic polynomial of a matrix over a field of characteristic `0` that takes integer values at
all integers and is annihilated by a monic integer polynomial is the image of a monic integer polynomial. -/
theorem charpoly_eq_map_int {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I F) (f : ℤ → ℤ)
    (hf : ∀ n : ℤ, M.charpoly.eval (n : F) = f n) (R : ℤ[X]) (hR : R.Monic) (hRM : aeval M R = 0) :
    ∃ Z : ℤ[X], Z.Monic ∧ Z.map (Int.castRingHom F) = M.charpoly ∧ ∀ n : ℤ, Z.eval n = f n := by
  obtain ⟨Q, hQ⟩ := exists_rat_of_int_values M.charpoly f hf
  obtain ⟨Z, hZm, hZ⟩ := exists_int_of_rat M Q hQ R hR hRM
  have hmap : Z.map (Int.castRingHom F) = M.charpoly := by
    rw [← hQ, ← hZ, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨Z, hZm, hmap, fun n => ?_⟩
  have h1 := hf n
  rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_intCast, eq_intCast] at h1
  exact_mod_cast h1

/-- Two integer polynomials with the same values at all integers are equal. -/
theorem int_poly_ext {P Z : ℤ[X]} (h : ∀ n : ℤ, P.eval n = Z.eval n) : P = Z :=
  Polynomial.eq_of_infinite_eval_eq P Z (by
    have : {x : ℤ | P.eval x = Z.eval x} = Set.univ := Set.eq_univ_of_forall h
    rw [this]; exact Set.infinite_univ)

end Algebra

/-! ## 2. The degree of an endomorphism and the new leaf -/

section AbVar

open PkgI3 PkgI3.AbVar

variable {k : Type} [Field k]

/-- The underlying scheme of an abelian variety is integral (it is geometrically integral over a field). -/
theorem isIntegral_left (A : PkgI3.AbVar k) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

attribute [local instance] isIntegral_left

/-- **The degree of an endomorphism** (Mumford, *Abelian varieties*, §4 and §19, UNVERIFIED locators): for
`ψ : A → A` finite and surjective (an isogeny), `deg ψ = [K(A) : ψ^* K(A)]`, the degree of the extension of
function fields; `deg ψ = 0` if `ψ` is not an isogeny. Here `K(A)` is the stalk of `A` at its generic point `η`
(Mathlib's `Scheme.functionField`), and `ψ^*` is the stalk map `𝒪_{A, ψ(η)} → 𝒪_{A, η}`; for surjective `ψ`,
`ψ(η) = η`, so the source is `K(A)` as well. -/
def degEnd {A : PkgI3.AbVar k} (ψ : PkgI3.AbVar.End A) : ℕ := by
  classical
  exact if PkgI3.AbVar.IsIsogenyMor ψ.hom then
    letI := (ψ.hom.left.stalkMap (genericPoint A.X.left)).hom.toAlgebra
    Module.finrank (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left)))
      (A.X.left.presheaf.stalk (genericPoint A.X.left))
  else 0

/-- **LEAF (Mumford §19 Thm 4, first assertion; printed form).** D. Mumford, *Abelian varieties* (1970), §19,
Theorem 4 (UNVERIFIED locator; `k` algebraically closed throughout the book): for `φ ∈ End(X)` and
`ℓ ≠ char k`, `deg φ = det(T_ℓ φ)`. Stated on `V_ℓ = ℚ_ℓ ⊗ T_ℓ` in an arbitrary finite basis (equal to the
determinant on the free `ℤ_ℓ`-module `T_ℓ`), with `deg` the genuine degree `degEnd`. -/
def DegEqDetTate : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ])).det =
          (degEnd ψ : ℚ_[ℓ])

/-! ## 3. `End A → End(T_ℓ A)` is a ring homomorphism -/

variable (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ` as a ring homomorphism `End(A) → End_{ℤ_ℓ}(T_ℓ A)`. -/
def homTRingHom : PkgI3.AbVar.End A →+* Module.End ℤ_[ℓ] (A.T ℓ) where
  toFun f := PkgI3.AbVar.homT f
  map_one' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    change Additive.ofMul (Additive.toMul (x.1 n) ≫ (1 : PkgI3.AbVar.End A).hom) = x.1 n
    rw [show (1 : PkgI3.AbVar.End A).hom = 𝟙 _ from rfl, Category.comp_id]
    rfl
  map_mul' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    change Additive.ofMul (Additive.toMul (x.1 n) ≫ (f * g).hom) =
      Additive.ofMul ((Additive.toMul (x.1 n) ≫ g.hom) ≫ f.hom)
    rw [show (f * g).hom = g.hom ≫ f.hom from rfl, Category.assoc]
  map_zero' := (PkgI3.AbVar.tateHom ℓ A A).map_zero
  map_add' := (PkgI3.AbVar.tateHom ℓ A A).map_add

variable {A ℓ}

/-- The matrix of `V_ℓ(f)` in a basis `b`, as a ring homomorphism. -/
def rho {I : Type} [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    PkgI3.AbVar.End A →+* Matrix I I ℚ_[ℓ] :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp
    ((Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)).toRingHom.comp (homTRingHom A ℓ))

theorem rho_apply {I : Type} [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ))
    (f : PkgI3.AbVar.End A) :
    rho b f = LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact LinearMap.toMatrixAlgEquiv_apply' _ _ _ _

omit [Fact ℓ.Prime] in
/-- A ring endomorphism equal to the identity makes `R` an `R`-module of rank `1`. -/
theorem finrank_toAlgebra_id {R : CommRingCat} [StrongRankCondition R] (e : R ⟶ R) (he : e = 𝟙 R) :
    @Module.finrank R R _ _ e.hom.toAlgebra.toModule = 1 := by
  subst he
  exact Module.finrank_self R

omit [Fact ℓ.Prime] in
/-- Sanity check of `degEnd`: the identity has degree `1`. -/
theorem degEnd_one (A : PkgI3.AbVar k) : degEnd (1 : PkgI3.AbVar.End A) = 1 := by
  have h1 : PkgI3.AbVar.IsIsogenyMor (1 : PkgI3.AbVar.End A).hom :=
    ⟨by change IsFinite (𝟙 A.X.left); infer_instance,
      by change Surjective (𝟙 A.X.left); infer_instance⟩
  have hs : (1 : PkgI3.AbVar.End A).hom.left.stalkMap (genericPoint A.X.left) =
      𝟙 (A.X.left.presheaf.stalk (genericPoint A.X.left)) :=
    Scheme.Hom.stalkMap_id A.X.left _
  have : StrongRankCondition (A.X.left.presheaf.stalk (genericPoint A.X.left)) :=
    inferInstanceAs (StrongRankCondition A.X.left.functionField)
  unfold degEnd
  split_ifs
  · exact finrank_toAlgebra_id _ hs

/-- Sanity check of the leaf: at `ψ = 1` both sides are `1`. -/
theorem degEqDetTate_one (A : PkgI3.AbVar k) {I : Type} [Fintype I]
    [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) (1 : PkgI3.AbVar.End A)).baseChange
      ℚ_[ℓ])).det = (degEnd (1 : PkgI3.AbVar.End A) : ℚ_[ℓ]) := by
  rw [degEnd_one, ← rho_apply, map_one, Matrix.det_one, Nat.cast_one]

end AbVar

/-! ## 4. The reduction -/

/-- **`CharPolyIndepOfEllAlgClosed` from `deg φ = det T_ℓ(φ)` and `End(A)` finite over `ℤ`.** -/
theorem charPolyIndepOfEllAlgClosed_of_degEqDetTate (hD : DegEqDetTate)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed := by
  intro k _ _ A φ
  classical
  obtain ⟨-, hfin, -, -⟩ := hH k A A
  have hint : IsIntegral ℤ φ := IsIntegral.of_finite ℤ φ
  obtain ⟨R, hR, hRφ⟩ := hint
  have hRφ' : aeval φ R = 0 := by rw [Polynomial.aeval_def]; exact hRφ
  set f : ℤ → ℤ := fun n => (degEnd ((n : PkgI3.AbVar.End A) - φ) : ℤ) with hf
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        ∃ Z : ℤ[X], Z.Monic ∧ Z.map (Int.castRingHom ℚ_[ℓ]) =
          (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly ∧
          ∀ n : ℤ, Z.eval n = f n := by
    intro ℓ _ hℓ I _ _ b
    rw [← rho_apply b φ]
    refine charpoly_eq_map_int _ f ?_ R hR ?_
    · intro n
      have hsc : Matrix.scalar I (n : ℚ_[ℓ]) - rho b φ = rho b ((n : PkgI3.AbVar.End A) - φ) := by
        rw [map_sub, map_intCast, map_intCast]
      rw [Matrix.eval_charpoly, hsc, rho_apply, hD k A _ ℓ hℓ I b, hf]
      push_cast
      rfl
    · have h := Polynomial.aeval_algHom_apply ((rho b).toIntAlgHom) φ R
      rw [hRφ', map_zero] at h
      exact h
  by_cases hex : ∃ Z : ℤ[X], Z.Monic ∧ ∀ n : ℤ, Z.eval n = f n
  · obtain ⟨P, hPm, hP⟩ := hex
    refine ⟨P, hPm, ?_⟩
    intro ℓ _ hℓ I _ _ b
    obtain ⟨Z, -, hZ, hZf⟩ := key ℓ hℓ I b
    rw [← hZ, int_poly_ext (fun n => (hP n).trans (hZf n).symm)]
  · refine ⟨1, Polynomial.monic_one, ?_⟩
    intro ℓ _ hℓ I _ _ b
    obtain ⟨Z, hZm, -, hZf⟩ := key ℓ hℓ I b
    exact absurd ⟨Z, hZm, hZf⟩ hex

end ZInQ.Contrib.OneProof.CharPolyEll

