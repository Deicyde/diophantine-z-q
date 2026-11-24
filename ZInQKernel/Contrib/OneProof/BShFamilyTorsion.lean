import ZInQKernel.Contrib.OneProof.BShFamilyLattice

/-! ON THE SPOT (provenance (c)): multiplication on the x-coordinates and
the criterion for two affine sections to agree modulo sign. -/

noncomputable section

namespace BShFamily

open UpperHalfPlane PeriodPair T5Glue X1Igusa X1Igusa.Weber WeierstrassCurve BShTraces
open LeafModCurves Polynomial

/-- The x-coordinate of a multiple of an affine point when the multiple is
affine. This expression is defined over the same field as the x-coordinate. -/
def mulX {F : Type*} [Field F] (E : WeierstrassCurve F) (n : ℤ) (x : F) : F :=
  (E.Φ n).eval x / (E.ΨSq n).eval x

theorem map_mulX {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (W : WeierstrassCurve F) (n : ℤ) (x : F) :
    f (mulX W n x) = mulX (W.map f) n (f x) := by
  simp only [mulX, map_div₀, map_Φ, map_ΨSq, eval_map, eval₂_at_apply]

/-- At a generic parameter the division ratios compute multiplication on
every section whose multiple remains affine. -/
theorem mulX_pointwise (τ : ℍ) (h₂ : (pp τ).g₂ ≠ 0) (h₃ : (pp τ).g₃ ≠ 0)
    (n : ℤ) {w : ℂ} (hw : w ∉ (pp τ).lattice) (hn : (n : ℂ) * w ∉ (pp τ).lattice) :
    let E := curveG ((pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2)
    (E.ΨSq n).eval (normX τ w) ≠ 0 ∧
      mulX E n (normX τ w) = normX τ ((n : ℂ) * w) := by
  dsimp only
  let L := pp τ
  let E := curveG (L.g₂ ^ 3 / L.g₃ ^ 2)
  let hΔ := discNeZero_pp τ
  obtain ⟨u, hu₂⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / L.g₃) two_pos
  have hu : u ≠ 0 := by
    rintro rfl
    exact div_ne_zero h₂ h₃ (by simpa using hu₂.symm)
  obtain ⟨e, he⟩ := exists_addEquiv_xCoord L.weierstrassCurve E _
    (curveC_smul L h₂ h₃ u hu₂ hu)
  let toPt : ℂ →+ L.weierstrassCurve.toAffine.Point :=
    ⟨⟨L.toPoint hΔ, L.toPoint_zero hΔ⟩, (L.isUniformization_toPoint hΔ).1⟩
  have hx (z : ℂ) (hz : z ∉ L.lattice) :
      ∃ x y, ∃ hns : E.toAffine.Nonsingular x y,
        e (toPt z) = Affine.Point.some x y hns ∧ x = normX τ z := by
    have hn : toPt z ≠ 0 := fun h => hz ((toPoint_eq_zero_iff L hΔ z).mp h)
    have hc := he (toPt z) hn
    have hc' : xCoord (toPt z) = L.weierstrassP z := by
      change xCoord (L.toPoint hΔ z) = _
      rw [L.toPoint_of_notMem hΔ hz]
      rfl
    rw [hc'] at hc
    cases h : e (toPt z) with
    | zero => exact (hn (e.map_eq_zero_iff.mp h)).elim
    | some x y hns =>
      refine ⟨x, y, hns, rfl, ?_⟩
      rw [h] at hc
      change x = u ^ 2 * L.weierstrassP z + 0 at hc
      rw [add_zero, hu₂] at hc
      exact hc
  obtain ⟨x, y, hns, h, hx₀⟩ := hx w hw
  obtain ⟨x', y', hns', h', hx₁⟩ := hx ((n : ℂ) * w) hn
  have hmul : n • Affine.Point.some x y hns = Affine.Point.some x' y' hns' := by
    rw [← h, ← h', ← map_zsmul, ← map_zsmul]
    simp [zsmul_eq_mul]
  have hn' : (E.ΨSq n).eval x ≠ 0 := by
    rw [ne_eq, eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ hns,
      zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero, hmul]
    exact Affine.Point.some_ne_zero hns'
  change (E.ΨSq n).eval (normX τ w) ≠ 0 ∧
    mulX E n (normX τ w) = normX τ ((n : ℂ) * w)
  rw [← hx₀, ← hx₁]
  exact ⟨hn', (div_eq_iff hn').mpr (E.mul_eval_ΨSq_eq_eval_Φ_of_zsmul hns hns' hmul).symm⟩

/-- Equality of two affine normalized x-coordinates implies equality of
their classes up to sign. -/
theorem periods_of_normX_eq (τ : ℍ) (h₂ : (pp τ).g₂ ≠ 0) (h₃ : (pp τ).g₃ ≠ 0)
    {z w : ℂ} (hz : z ∉ (pp τ).lattice) (hw : w ∉ (pp τ).lattice)
    (he : normX τ z = normX τ w) :
    z - w ∈ (pp τ).lattice ∨ z + w ∈ (pp τ).lattice := by
  let L := pp τ
  let hΔ := discNeZero_pp τ
  have h : L.weierstrassP z = L.weierstrassP w :=
    mul_left_cancel₀ (div_ne_zero h₂ h₃) he
  let toPt : ℂ →+ L.weierstrassCurve.toAffine.Point :=
    ⟨⟨L.toPoint hΔ, L.toPoint_zero hΔ⟩, (L.isUniformization_toPoint hΔ).1⟩
  have e : L.derivWeierstrassP z ^ 2 = L.derivWeierstrassP w ^ 2 := by
    rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, h]
  have aux {v : ℂ} (hv : v ∉ L.lattice) (hx : L.weierstrassP z = L.weierstrassP v)
      (hy : L.derivWeierstrassP z = L.derivWeierstrassP v) : z - v ∈ L.lattice := by
    apply (toPoint_eq_zero_iff L hΔ _).mp
    change toPt (z - v) = 0
    rw [map_sub, sub_eq_zero]
    change L.toPoint hΔ z = L.toPoint hΔ v
    rw [L.toPoint_of_notMem hΔ hz, L.toPoint_of_notMem hΔ hv]
    exact Affine.Point.some.injEq .. |>.mpr ⟨hx, by rw [hy]⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with e | e
  · exact Or.inl (aux hw h e)
  · have hn : -w ∉ L.lattice := by simpa
    have hx : L.weierstrassP z = L.weierstrassP (-w) := by rwa [L.weierstrassP_neg]
    have hy : L.derivWeierstrassP z = L.derivWeierstrassP (-w) := by rwa [L.derivWeierstrassP_neg]
    exact Or.inr (by simpa only [sub_neg_eq_add] using aux hn hx hy)

/-- Nonzero sections coming from different prime superlattices have
different normalized x-coordinates. -/
theorem line_eq_of_coordinates_eq {p : ℕ} (hp : p.Prime) (τ : ℍ)
    (h₂ : (pp τ).g₂ ≠ 0) (h₃ : (pp τ).g₃ ≠ 0)
    {i j : Line p} {k l : Multiple p}
    (h : normX τ ((k.val.val : ℂ) * generator p i τ) =
      normX τ ((l.val.val : ℂ) * generator p j τ)) : i = j := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let s := (k.val.val : ℂ) * generator p i τ
  let t := (l.val.val : ℂ) * generator p j τ
  have hs := multiple_notMem hp.pos i τ k
  have ht := multiple_notMem hp.pos j τ l
  have hm (a : Line p) (b : Multiple p) :
      (b.val.val : ℂ) * generator p a τ ∈ (enlarged hp.pos a τ).lattice := by
    have hh := representative_mem (cosets hp.pos a τ) b.val
    rw [representative_eq, neg_mul] at hh
    exact neg_mem_iff.mp hh
  have hle (a : Line p) : (pp τ).lattice ≤ (enlarged hp.pos a τ).lattice :=
    lattice_le (cosets hp.pos a τ) 0 (by rw [representative_eq]; simp)
  have hs' : s ∈ (enlarged hp.pos j τ).lattice := by
    rcases periods_of_normX_eq τ h₂ h₃ hs ht h with h | h
    · convert (enlarged hp.pos j τ).lattice.add_mem (hle j h) (hm j l) using 1
      exact (sub_add_cancel s t).symm
    · convert (enlarged hp.pos j τ).lattice.sub_mem (hle j h) (hm j l) using 1
      exact (add_sub_cancel_right s t).symm
  obtain ⟨a, _, ha⟩ := prime_torsion_lattice_unique hp τ s hs (multiple_killed hp.pos i τ k.val)
  exact (ha _ (hm i k)).trans (ha _ hs').symm

#print axioms map_mulX
#print axioms mulX_pointwise
#print axioms periods_of_normX_eq
#print axioms line_eq_of_coordinates_eq

end BShFamily
