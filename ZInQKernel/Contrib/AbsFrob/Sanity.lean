import ZInQKernel.Contrib.AbsFrob.Basic

/-! # Sanity checks for the absolute Frobenius (task frob-contrib)

* `fr_naturality'`: the hypothesis `hY` of `AbsFrobDef.fr_naturality` is redundant (it follows from
  `hX` through `f`); this is the same statement with `hY` derived.
* `fr_Spec_zmod`: on `Spec 𝔽_p` the absolute Frobenius is the identity (Fermat).
* `fr_Spec_polynomial_ne_id`: on `Spec 𝔽_p[T]` it is not the identity (`T ↦ T ^ p`), so `fr` is
  not the identity in disguise.
-/

noncomputable section

namespace AbsFrobDef

open CategoryTheory AlgebraicGeometry

universe u

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
/-- `p = 0` on `Y` if `p = 0` on `X` and `Y → X`. -/
theorem natCast_of_hom' {X Y : Scheme.{u}} (f : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0) :
    (p : Γ(Y, ⊤)) = 0 := by
  have := congrArg f.appTop.hom hX
  rwa [map_natCast, map_zero] at this

/-- `fr_naturality` without the redundant hypothesis on `Y`. -/
theorem fr_naturality' {X Y : Scheme.{u}} (f : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0) :
    f ≫ fr p X hX = fr p Y (natCast_of_hom' p f hX) ≫ f :=
  fr_naturality p f hX _

/-- The absolute Frobenius of `Spec 𝔽_p` is the identity. -/
theorem fr_Spec_zmod :
    fr p (Spec (.of (ZMod p))) (natCast_Spec p (.of (ZMod p)) (ZMod.natCast_self p)) = 𝟙 _ := by
  rw [fr_Spec p _ (ZMod.natCast_self p)]
  have : powHom p (ZMod p) (ZMod.natCast_self p) = RingHom.id _ :=
    RingHom.ext fun x => ZMod.pow_card x
  rw [this, ← Spec.map_id]
  rfl

/-- The absolute Frobenius of `Spec 𝔽_p[T]` is not the identity. -/
theorem fr_Spec_polynomial_ne_id :
    fr p (Spec (.of (Polynomial (ZMod p))))
        (natCast_Spec p (.of (Polynomial (ZMod p))) (CharP.cast_eq_zero (Polynomial (ZMod p)) p))
      ≠ 𝟙 _ := by
  intro h
  rw [fr_Spec p _ (CharP.cast_eq_zero (Polynomial (ZMod p)) p), ← Spec.map_id, Spec.map_inj] at h
  have h1 := congrArg (fun φ => φ.hom Polynomial.X) h
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply] at h1
  rw [powHom_apply] at h1
  have h2 := congrArg Polynomial.natDegree h1
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h2
  exact hp.out.one_lt.ne' h2

end AbsFrobDef
