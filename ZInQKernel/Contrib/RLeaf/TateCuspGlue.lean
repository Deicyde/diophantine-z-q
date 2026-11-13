import ZInQKernel.Contrib.RLeaf.X1RationalCusp
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-!
# t40-tate: `TateCuspLaurent` from a torsion point on an elliptic curve over `ℚ((t))`

`TateCuspLaurent` (task rleaf-elliptic, `X1RationalCusp.lean`) asks, for each `N > 0`, for a
point `P` of exact order `N` on `E_j / \overline{ℚ(j)}` and a `ℚ`-embedding
`ℚ(j)(x(P)) → ℚ((t))` under which `j` is not a power series.

This file isolates the analytic input as `TateLaurentTorsion`: for every `N ≥ 2` some elliptic
curve over `ℚ((t))`, with `j`-invariant not a power series, has a `ℚ((t))`-rational point of exact
order `N` (the Tate curve `E_q`, `q = t^N`, with the point `u = t` of Tate's parametrization
`ℚ((t))^× / q^ℤ ≅ E_q(ℚ((t)))`).
-/

namespace ZInQ.RLeaf

open Classical in
/-- **A torsion point of exact order `N` over `ℚ((t))` on a curve with non-integral `j`.**
For every `N ≥ 2` there is an elliptic curve `W` over `ℚ((t))` whose `j`-invariant is not a
power series in `t`, with a `ℚ((t))`-rational point of exact order `N`.

Source: the Tate curve `E_q` over `ℚ((t))` with `q = t^N`; Tate's parametrization
`ℚ((t))^× / q^ℤ ≅ E_q(ℚ((t)))` is a group isomorphism (Tate 1995; Silverman, *Advanced topics in
the arithmetic of elliptic curves*, Thm. V.3.1, UNVERIFIED number), so the class of `t` has exact
order `N`, and `j(E_q) = 1/q + 744 + ⋯` (loc. cit. V.3.1(c)). Published theorem. -/
def TateLaurentTorsion : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ (W : WeierstrassCurve (LaurentSeries ℚ)) (_ : W.IsElliptic)
    (P : W.toAffine.Point), addOrderOf P = N ∧
      W.j ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)

namespace TateCuspGlue

open Polynomial LeafModCurves WeierstrassCurve

/-- An algebraic closure of `ℚ((t))`. -/
abbrev Lb := AlgebraicClosure (LaurentSeries ℚ)

instance : CharZero Lb := algebraRat.charZero Lb

/-! ### A Laurent series which is not a power series is transcendental over `ℚ` -/

theorem aeval_ne_zero {J : LaurentSeries ℚ}
    (hJ : J ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)) {p : ℚ[X]} (hp : p ≠ 0) :
    aeval J p ≠ 0 := by
  have hJ0 : J ≠ 0 := fun h => hJ ⟨0, by rw [h, map_zero]⟩
  have hv : ¬ Valued.v J ≤ 1 := fun h => by
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe ℚ J).mp h
    exact hJ ⟨F, hF⟩
  have hu : Valued.v J⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hv))
  obtain ⟨U, hU⟩ := (LaurentSeries.val_le_one_iff_eq_coe ℚ J⁻¹).mp hu
  have hU0 : PowerSeries.constantCoeff U = 0 := by
    by_contra h
    obtain ⟨V, hV⟩ := (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)).exists_right_inv
    apply hJ
    refine ⟨V, ?_⟩
    have h1 : HahnSeries.ofPowerSeries ℤ ℚ U * HahnSeries.ofPowerSeries ℤ ℚ V = 1 := by
      rw [← map_mul, hV, map_one]
    rw [hU] at h1
    calc HahnSeries.ofPowerSeries ℤ ℚ V = J * (J⁻¹ * HahnSeries.ofPowerSeries ℤ ℚ V) := by
          rw [← mul_assoc, mul_inv_cancel₀ hJ0, one_mul]
      _ = J := by rw [h1, mul_one]
  intro h
  let : Invertible J := invertibleOfNonzero hJ0
  have h2 := eval₂_reverse_mul_pow (algebraMap ℚ (LaurentSeries ℚ)) J p
  rw [aeval_def] at h
  rw [h, invOf_eq_inv] at h2
  have h3 : eval₂ (algebraMap ℚ (LaurentSeries ℚ)) J⁻¹ p.reverse = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · exact absurd (pow_eq_zero_iff'.mp h4).1 hJ0
  rw [← hU] at h3
  have h5 : HahnSeries.ofPowerSeries ℤ ℚ (eval₂ PowerSeries.C U p.reverse) = 0 := by
    rw [hom_eval₂]
    convert h3 using 2
    exact RingHom.ext_rat _ _
  rw [map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective] at h5
  have h6 := congrArg PowerSeries.constantCoeff h5
  rw [hom_eval₂, hU0, eval₂_at_zero, coeff_zero_reverse, map_zero] at h6
  have h7 : (PowerSeries.constantCoeff.comp PowerSeries.C : ℚ →+* ℚ) = RingHom.id ℚ :=
    RingHom.ext_rat _ _
  rw [h7, RingHom.id_apply] at h6
  exact hp (leadingCoeff_eq_zero.mp h6)

/-- The `ℚ`-embedding `ℚ(j) → ℚ((t))`, `j ↦ J`, for `J` not a power series. -/
noncomputable def phi (J : LaurentSeries ℚ) (hJ : J ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)) :
    Qj →+* LaurentSeries ℚ :=
  RatFunc.liftRingHom (aeval J).toRingHom fun p hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_ne_zero hJ (nonZeroDivisors.ne_zero hp))

theorem phi_X (J : LaurentSeries ℚ) (hJ : J ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)) :
    phi J hJ RatFunc.X = J := by
  have := RatFunc.liftRingHom_apply_div (aeval J).toRingHom (fun p hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_ne_zero hJ (nonZeroDivisors.ne_zero hp))) X 1
  calc phi J hJ RatFunc.X
      = phi J hJ (algebraMap ℚ[X] Qj X / algebraMap ℚ[X] Qj 1) := by
        rw [map_one, div_one, RatFunc.algebraMap_X]
    _ = J := by rw [phi, this]; simp

theorem phi_rat (J : LaurentSeries ℚ) (hJ : J ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ))
    (c : ℚ) : phi J hJ (algebraMap ℚ Qj c) = HahnSeries.C c := by
  exact RingHom.congr_fun (RingHom.ext_rat ((phi J hJ).comp (algebraMap ℚ Qj)) HahnSeries.C) c

/-! ### Points along an injective field homomorphism and along equalities of curves -/

theorem xCoord_mapAlong {F K : Type*} [Field F] [Field K] {W : WeierstrassCurve F} (f : F →+* K)
    (P : W.toAffine.Point) :
    xCoord (P.mapAlong f f.injective) = f (xCoord P) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [xCoord, Affine.Point.mapAlong]
  · rfl

theorem exists_cast {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) (P : W₁.toAffine.Point) :
    ∃ Q : W₂.toAffine.Point, addOrderOf Q = addOrderOf P ∧ xCoord Q = xCoord P := by
  subst h; exact ⟨P, rfl, rfl⟩

/-! ### The core: lifting a point of exact order `N` from `\overline{ℚ((t))}` to `\overline{ℚ(j)}` -/

open Classical in
theorem core (φ : Qj →+* LaurentSeries ℚ)
    (hφQ : ∀ c : ℚ, φ (algebraMap ℚ Qj c) = HahnSeries.C c)
    (hφX : φ RatFunc.X ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ))
    (φb : Kbar →+* Lb)
    (hφb : ∀ a, φb (algebraMap Qj Kbar a) = algebraMap (LaurentSeries ℚ) Lb (φ a))
    (N : ℕ) (hN : 0 < N) (Q : (EjBar.map φb).toAffine.Point) (hQ : addOrderOf Q = N)
    (hx : xCoord Q ∈ Set.range (algebraMap (LaurentSeries ℚ) Lb)) :
    ∃ (P : EjBar.toAffine.Point) (ψ : fieldX1 P →+* LaurentSeries ℚ),
      addOrderOf P = N ∧ (∀ c : ℚ, ψ (X1Belyi.ratHom (fieldX1 P) c) = HahnSeries.C c) ∧
      ψ (algebraMap Qj (fieldX1 P) RatFunc.X) ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ) := by
  let f : EjBar.toAffine.Point →+ (EjBar.map φb).toAffine.Point :=
    AddMonoidHom.mk' (Affine.Point.mapAlong φb φb.injective)
      (Affine.Point.mapAlong_add φb φb.injective)
  have hf : Function.Injective f := Affine.Point.mapAlong_injective φb φb.injective
  -- torsion counting
  obtain ⟨e₁⟩ := t36_torsionStructure Kbar EjBar N hN
  obtain ⟨e₂⟩ := t36_torsionStructure Lb (EjBar.map φb) N hN
  have hc₁ := X1Belyi.nTors_card Kbar EjBar N hN e₁
  have hc₂ := X1Belyi.nTors_card Lb (EjBar.map φb) N hN e₂
  haveI : Finite (X1Belyi.nTors (EjBar.map φb) N) := by
    have : NeZero N := ⟨hN.ne'⟩
    exact Finite.of_equiv _ e₂.toEquiv.symm
  let g : X1Belyi.nTors EjBar N → X1Belyi.nTors (EjBar.map φb) N := fun P =>
    ⟨f P.1, by
      show N • f P.1 = 0
      rw [← map_nsmul, show N • P.1 = 0 from P.2, map_zero]⟩
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (hf (congrArg Subtype.val hab))
  have hgb := hg.bijective_of_nat_card_le (by rw [hc₁, hc₂])
  have hQmem : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  obtain ⟨⟨P, hPmem⟩, hP⟩ := hgb.2 ⟨Q, hQmem⟩
  have hfP : f P = Q := congrArg Subtype.val hP
  have hPord : addOrderOf P = N := by
    rw [← addOrderOf_injective f hf P, hfP, hQ]
  have hxP : φb (xCoord P) ∈ Set.range (algebraMap (LaurentSeries ℚ) Lb) := by
    rw [← xCoord_mapAlong φb P]
    change xCoord (f P) ∈ _
    rw [hfP]; exact hx
  -- the embedding of `K_N = ℚ(j)(x(P))`
  let E : IntermediateField Qj Kbar :=
    { Subfield.comap φb (algebraMap (LaurentSeries ℚ) Lb).fieldRange with
      algebraMap_mem' := fun a => ⟨φ a, (hφb a).symm⟩ }
  have hle : fieldX1 P ≤ E :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxP)
  have key : ∀ z : fieldX1 P, ∃ w : LaurentSeries ℚ,
      algebraMap (LaurentSeries ℚ) Lb w = φb (z : Kbar) := fun z => by
    obtain ⟨w, hw⟩ := hle z.2
    exact ⟨w, hw⟩
  choose ψf hψf using key
  have inj := (algebraMap (LaurentSeries ℚ) Lb).injective
  let ψ : fieldX1 P →+* LaurentSeries ℚ :=
    { toFun := ψf
      map_one' := inj (by rw [hψf]; simp)
      map_mul' := fun a b => inj (by rw [map_mul, hψf, hψf, hψf]; simp)
      map_zero' := inj (by rw [hψf]; simp)
      map_add' := fun a b => inj (by rw [map_add, hψf, hψf, hψf]; simp) }
  have hψ : ∀ a : Qj, ψ (algebraMap Qj (fieldX1 P) a) = φ a := fun a =>
    inj (by
      show algebraMap _ _ (ψf _) = _
      rw [hψf, ← hφb]; rfl)
  refine ⟨P, ψ, hPord, fun c => ?_, ?_⟩
  · show ψ (algebraMap Qj (fieldX1 P) (algebraMap ℚ Qj c)) = _
    rw [hψ, hφQ]
  · rw [hψ]; exact hφX

end TateCuspGlue

end ZInQ.RLeaf
