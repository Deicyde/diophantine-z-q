import ZInQKernel.Contrib.RLeaf.BelyiX1

/-!
# rleaf-elliptic: the leaf T39 follows from the leaf T40

`X1Belyi.X1ConstantField` (leaf T39: `ℚ` is algebraically closed in `K_N = ℚ(j)(x(P))`, Igusa) is a
consequence of `X1Belyi.X1RationalCusp` (leaf T40: `K_N` has a place of degree 1 over `ℚ`). A
field with a degree-one place has constant field `ℚ`: an element `x` algebraic over `ℚ` is integral
over the valuation ring `w` (which contains `ℚ` and is integrally closed), so `x ∈ w`; its residue
is some `c ∈ ℚ`; and if `x ≠ c`, then `(x - c)⁻¹` is again algebraic, hence in `w`, while
`x - c ∈ 𝔪_w`, a contradiction (the standard argument, e.g. Stichtenoth, *Algebraic function
fields*, Cor. 3.6.5 for degree-one places, UNVERIFIED number).

So T39 leaves the leaf list. With T36 and T37 proved (`BelyiX1.lean`), the x1-belyi bundle
`X1Belyi.X1Leaves` needs only T38 and T40 (`x1Leaves_of_t38_t40`), and so does
`LeafModCurves.X1ModelExists` (`x1ModelExists_of_t38_t40`).
-/

namespace ZInQ.RLeaf

open Polynomial

/-- **A field with a degree-one place has constant field `ℚ`.** -/
theorem constantFieldIsQ_of_hasRationalPlace (F : Type) [Field F] [Algebra LeafModCurves.Qj F]
    (h : X1Belyi.HasRationalPlace F) : X1Belyi.ConstantFieldIsQ F := by
  obtain ⟨w, -, hQw, hres⟩ := h
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap LeafModCurves.Qj F).injective
  -- an element algebraic over `ℚ` lies in `w`
  have hint : ∀ z : F, (∃ f : ℚ[X], f ≠ 0 ∧ f.eval₂ (X1Belyi.ratHom F) z = 0) → z ∈ w := by
    rintro z ⟨f, hf0, hfz⟩
    let φ0 : ℚ →+* w := (X1Belyi.ratHom F).codRestrict w.toSubring hQw
    have hgm : (f * C f.leadingCoeff⁻¹).Monic := Polynomial.monic_mul_leadingCoeff_inv hf0
    have hgz : (f * C f.leadingCoeff⁻¹).eval₂ (X1Belyi.ratHom F) z = 0 := by
      rw [Polynomial.eval₂_mul, hfz, zero_mul]
    have hI : IsIntegral w z := by
      refine ⟨(f * C f.leadingCoeff⁻¹).map φ0, hgm.map φ0, ?_⟩
      rw [Polynomial.eval₂_map]
      have hc : (algebraMap w F).comp φ0 = X1Belyi.ratHom F := RingHom.ext fun _ => rfl
      rw [hc]; exact hgz
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
    rw [← hb]; exact b.2
  have hrat : algebraMap ℚ F = X1Belyi.ratHom F := RingHom.ext_rat _ _
  have halg : ∀ z : F, IsAlgebraic ℚ z ↔
      ∃ f : ℚ[X], f ≠ 0 ∧ f.eval₂ (X1Belyi.ratHom F) z = 0 := by
    intro z
    simp only [IsAlgebraic, Polynomial.aeval_def, hrat]
  intro x hx
  obtain ⟨c, hc⟩ := hres x (hint x hx)
  by_cases hy0 : x - X1Belyi.ratHom F c = 0
  · exact ⟨c, (sub_eq_zero.mp hy0).symm⟩
  exfalso
  have hyalg : IsAlgebraic ℚ (x - X1Belyi.ratHom F c) := by
    rw [← hrat]
    exact ((halg x).mpr hx).sub (isAlgebraic_algebraMap c)
  have hyinv : (x - X1Belyi.ratHom F c)⁻¹ ∈ w := hint _ ((halg _).mp hyalg.inv)
  rw [ValuationSubring.mem_nonunits_iff] at hc
  have h2 := (w.valuation_le_one_iff _).mpr hyinv
  have h3 : w.valuation ((x - X1Belyi.ratHom F c) * (x - X1Belyi.ratHom F c)⁻¹) < 1 := by
    rw [map_mul]
    calc w.valuation (x - X1Belyi.ratHom F c) * w.valuation (x - X1Belyi.ratHom F c)⁻¹
        ≤ w.valuation (x - X1Belyi.ratHom F c) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hc
  rw [mul_inv_cancel₀ hy0, map_one] at h3
  exact lt_irrefl _ h3

/-- **T39 from T40** (glue): `X1RationalCusp → X1ConstantField`. -/
theorem x1ConstantField_of_x1RationalCusp (h : X1Belyi.X1RationalCusp) :
    X1Belyi.X1ConstantField := fun N P hN hP =>
  constantFieldIsQ_of_hasRationalPlace _ (h N P hN hP)

/-- The x1-belyi bundle from T38 and T40 alone (T36, T37 proved; T39 from T40). -/
theorem x1Leaves_of_t38_t40 (hC : X1Belyi.CurveOfFunctionFieldQ)
    (hR : X1Belyi.X1RationalCusp) : X1Belyi.X1Leaves :=
  x1Leaves_of hC (x1ConstantField_of_x1RationalCusp hR) hR

/-- `X1ModelExists` from T38 and T40 alone. -/
theorem x1ModelExists_of_t38_t40 (hC : X1Belyi.CurveOfFunctionFieldQ)
    (hR : X1Belyi.X1RationalCusp) : LeafModCurves.X1ModelExists :=
  x1ModelExists_of hC (x1ConstantField_of_x1RationalCusp hR) hR

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.constantFieldIsQ_of_hasRationalPlace
#print axioms ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp
#print axioms ZInQ.RLeaf.x1Leaves_of_t38_t40
#print axioms ZInQ.RLeaf.x1ModelExists_of_t38_t40
