import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsTorusKernel
import Mathlib.Algebra.Order.Group.Nat

/-! The ℓ-power torsion of a split torus is Zariski dense when ℓ is invertible. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open ZInQ.HeightSplit ZInQ.SemiAbDescend
open scoped BigOperators

namespace SZRaynaud

variable {k : Type} [Field k] [IsAlgClosed k] {r ℓ : ℕ}

private abbrev TorusPrimary (k : Type) [Field k] (r ℓ : ℕ) :=
  CommGroup.primaryComponent (Fin r → kˣ) ℓ

private def torusMonomial (a : Fin r →₀ ℕ) : TorusPrimary k r ℓ →* k where
  toFun t := ∏ i, (t.1 i : k) ^ a i
  map_one' := by simp
  map_mul' x y := by
    change (∏ i, (((x.1 i) * (y.1 i) : kˣ) : k) ^ a i) = _
    simp only [Units.val_mul, mul_pow, Finset.prod_mul_distrib]

private theorem torusMonomial_injective (hℓ : 1 < ℓ) (hk : (ℓ : k) ≠ 0) :
    Function.Injective (torusMonomial (k := k) (r := r) (ℓ := ℓ)) := by
  classical
  intro a b h
  ext j
  let n := max (a j) (b j) + 1
  have hn : max (a j) (b j) < ℓ ^ n :=
    (Nat.lt_succ_self _).trans_le (Nat.le_of_lt (Nat.lt_pow_self hℓ))
  let : NeZero ((ℓ ^ n : ℕ) : k) := ⟨by simpa only [Nat.cast_pow] using pow_ne_zero n hk⟩
  let : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (by omega)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k (ℓ ^ n)
  have hζnz : ζ ≠ 0 := (hζ.isUnit (NeZero.ne _)).ne_zero
  let t : Fin r → kˣ := Function.update 1 j (Units.mk0 ζ hζnz)
  have ht : t ^ ℓ ^ n = 1 := by
    funext i
    change t i ^ ℓ ^ n = 1
    by_cases hij : i = j
    · subst i
      apply Units.ext
      simpa [t] using hζ.pow_eq_one
    · simp [t, Function.update_of_ne hij]
  let x : TorusPrimary k r ℓ := ⟨t, CommGroup.mem_primaryComponent.mpr ⟨n, ht⟩⟩
  have eval (c : Fin r →₀ ℕ) : torusMonomial c x = ζ ^ c j := by
    change (∏ i, (t i : k) ^ c i) = _
    rw [Finset.prod_eq_single j]
    · simp [t]
    · intro i _ hij
      simp [t, Function.update_of_ne hij]
    · simp
  have he := DFunLike.congr_fun h x
  rw [eval a, eval b] at he
  refine pow_injOn_Iio_orderOf (x := ζ) ?_ ?_ he
  · exact hζ.eq_orderOf ▸ (le_max_left _ _).trans_lt hn
  · exact hζ.eq_orderOf ▸ (le_max_right _ _).trans_lt hn

/-- A polynomial vanishing on every ℓ-power torsion tuple is zero. -/
theorem mvPolynomial_eq_zero_of_primary_torus (hℓ : 1 < ℓ) (hk : (ℓ : k) ≠ 0)
    (P : MvPolynomial (Fin r) k)
    (hP : ∀ t : TorusPrimary k r ℓ, MvPolynomial.eval (fun i => (t.1 i : k)) P = 0) :
    P = 0 := by
  classical
  have hli := (linearIndependent_monoidHom (TorusPrimary k r ℓ) k).comp _
    (torusMonomial_injective hℓ hk)
  have hcoeff := (linearIndependent_iff'.mp hli) P.support P.coeff
  have heval : ∑ a ∈ P.support, P.coeff a • (torusMonomial a : TorusPrimary k r ℓ → k) = 0 := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hP t
    rw [MvPolynomial.eval_eq'] at h
    exact h
  ext a
  change P.coeff a = 0
  by_cases ha : a ∈ P.support
  · exact hcoeff heval a ha
  · exact not_not.mp (fun h => ha (MvPolynomial.mem_support_iff.mpr h))

omit [IsAlgClosed k] in
private theorem eval_torus_polynomial (x : Fin r → kˣ) (P : MvPolynomial (Fin r) k) :
    torusLift x (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) P) =
      MvPolynomial.eval (fun i => (x i : k)) P := by
  change (IsLocalization.liftAlgHom _ : TorusRing k r →ₐ[k] k) _ = _
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change MvPolynomial.aeval (fun i => (x i : k)) P = _
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  rfl

/-- The points of a split torus with ℓ-power order are Zariski dense. -/
theorem denseRange_torus_primary_points (hℓ : 1 < ℓ) (hk : (ℓ : k) ≠ 0) :
    DenseRange (fun t : TorusPrimary k r ℓ =>
      Spec.map (CommRingCat.ofHom (torusLift (K := k) t.1).toRingHom) (IsLocalRing.closedPoint k)) := by
  let f (t : TorusPrimary k r ℓ) :=
    Spec.map (CommRingCat.ofHom (torusLift (K := k) t.1).toRingHom) (IsLocalRing.closedPoint k)
  change Dense (Set.range f)
  have hzero : PrimeSpectrum.vanishingIdeal (Set.range f) = ⊥ := by
    apply eq_bot_iff.mpr
    intro q hq
    let p : MvPolynomial (Fin r) k := ∏ i, MvPolynomial.X i
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (Submonoid.powers p) q
    have hq0 (t : TorusPrimary k r ℓ) : torusLift (K := k) t.1 q = 0 := by
      have hmem := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hq (f t) ⟨t, rfl⟩
      change torusLift (K := k) t.1 q ∈ (IsLocalRing.closedPoint k).asIdeal at hmem
      have hk0 : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
        (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
      simpa only [hk0, Ideal.mem_bot] using hmem
    have ha : a = 0 := mvPolynomial_eq_zero_of_primary_torus hℓ hk a (fun t => by
      have he := congrArg (torusLift (K := k) t.1) hd
      change torusLift (K := k) t.1 (q * algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) d) =
        torusLift (K := k) t.1 (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) a) at he
      rw [map_mul, hq0 t, zero_mul, eval_torus_polynomial] at he
      exact he.symm)
    have hu : IsUnit (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) d) :=
      IsLocalization.map_units (TorusRing k r) d
    rw [ha, map_zero] at hd
    exact Ideal.mem_bot.mpr ((mul_eq_zero.mp hd).resolve_right hu.ne_zero)
  rw [dense_iff_closure_eq]
  change closure (Set.range f : Set (PrimeSpectrum (TorusRing k r))) = Set.univ
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hzero]
  exact PrimeSpectrum.zeroLocus_bot

end SZRaynaud

#print axioms SZRaynaud.mvPolynomial_eq_zero_of_primary_torus
#print axioms SZRaynaud.denseRange_torus_primary_points
