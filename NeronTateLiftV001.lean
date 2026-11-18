import NeronGenericFibreV001

/-!
# Compatible integral systems over a Tate-module element

For a separated group model `(N, e)` over `O` with generic-fibre map `Φ : N(w) → A(Ω)`, an element
`t = (xₙ)` of `T_ℓ(A) = lim A(Ω)[ℓⁿ]` whose components all lie in the image of `Φ` lifts to a
unique compatible system of `w`-sections `sₙ` (`s₀ = 1`, `sₙ₊₁ ^ ℓ = sₙ`, `Φ sₙ = xₙ`). Uniqueness
and the compatibility relations come from injectivity and multiplicativity of `Φ`; no
commutativity of `N` is assumed. The image hypothesis on the components is exactly what the
étale-neighbourhood extension theorem supplies for points with unramified coordinate fields.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonObj

namespace NeronInvariantTorsion

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
variable {A : PkgI3.AbVar K} {N : Over (Spec (CommRingCat.of O))}
  (e : (Over.pullback (jO O)).obj N ≅ A.X)

open scoped Obj in
/-- **Integral compatible systems over `T_ℓ`.** -/
theorem exists_unique_compatible_sections [GrpObj N] [IsSeparated N.hom]
    (hgen : letI : GrpObj ((Over.pullback (jO O)).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω)))
    (himage : ∀ n, ∃ s : specW O w hw ⟶ N,
      genericFibre O w hw e s = Additive.toMul (t.1 n)) :
    ∃ s : ℕ → (specW O w hw ⟶ N), s 0 = 1 ∧ (∀ n, s (n + 1) ^ ℓ = s n) ∧
      (∀ n, genericFibre O w hw e (s n) = Additive.toMul (t.1 n)) ∧
      ∀ s' : ℕ → (specW O w hw ⟶ N),
        (∀ n, genericFibre O w hw e (s' n) = Additive.toMul (t.1 n)) → s' = s := by
  choose s hs using himage
  have hinj := genericFibre_injective O w hw e
  have hpow : ∀ (u : specW O w hw ⟶ N) (m : ℕ),
      genericFibre O w hw e (u ^ m) = genericFibre O w hw e u ^ m :=
    fun u m => map_pow (genericFibreHom O w hw e hgen) u m
  refine ⟨s, ?_, ?_, hs, ?_⟩
  · apply hinj
    rw [hs 0, genericFibre_one O w hw e hgen, t.2.1]
    rfl
  · intro n
    apply hinj
    rw [hpow, hs (n + 1), hs n, ← t.2.2 n]
    rfl
  · intro s' hs'
    funext n
    exact hinj ((hs' n).trans (hs n).symm)

end NeronInvariantTorsion
