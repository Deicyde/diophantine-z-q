
/-! # frob-pieces: `GoodRedCofinite` from spreading out (task frob-pieces)

Appended (by `scratch/frob-pieces/build.sh`) to a verbatim copy of
`scratch/alg-frob-red/AlgFrobRed.lean`. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AbSchemeSpreadsOut` (LEAF candidate, published: spreading out an abelian variety to an
abelian scheme).** An abelian variety `A` over a number field `L ⊆ ℚ̄` extends to an abelian
scheme (I2's `IsAbelianScheme`: a group object, proper, smooth, geometrically connected) over a
finitely generated subring `R = ℤ[s] ⊆ L`, with generic fibre isomorphic to `A` as a group object.
Source: `L = colim R` over finitely generated subrings; the scheme, group law and axioms descend to
some `R` (EGA IV₃ 8.8.2), as do properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8);
geometric connectedness of the fibres holds over a nonempty open of `Spec R` (EGA IV₃ 9.7.7;
alternatively, Zariski connectedness, EGA III 4.3, for the proper smooth model over the normal
`R`), and shrinking `R` to `R[1/f]` keeps it finitely generated. Locators UNVERIFIED. Same input as
neron-lg's glue N1-g1 `AbVarSpreadsOut`, plus geometric connectedness of the fibres. -/
def AbSchemeSpreadsOut : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ (s : Finset L) (𝒜 : Grp (Over (Spec (.of (Subring.closure (s : Set L)))))),
      PkgI2.IsAbelianScheme 𝒜 ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (Subring.closure (s : Set L)) L)))).mapGrp.obj 𝒜 ≅ ObjBridge.toGrp A)

/-- A nonzero integer prime to `p` is a unit in `O_w` for `w ∣ p`. -/
theorem isUnit_intCast_of_coprime {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) {y : ℤ}
    (hpy : ¬ p ∣ y.natAbs) : IsUnit (y : Ow L v) := by
  by_contra hnu
  have hym : (y : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  have hcop : IsCoprime (p : ℤ) y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hp).2 hpy
    simpa [Int.gcd] using this
  obtain ⟨u, w, huw⟩ := hcop
  have h1 : ((u * p + w * y : ℤ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hym)
  rw [huw, Int.cast_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Base change of a group object along equal morphisms. -/
theorem pullbackGrp_congr {X Y : Scheme} {f f' : X ⟶ Y} (h : f = f') (𝒜 : Grp (Over Y)) :
    Nonempty ((Over.pullback f).mapGrp.obj 𝒜 ≅ (Over.pullback f').mapGrp.obj 𝒜) := by
  subst h; exact ⟨Iso.refl _⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from `AbSchemeSpreadsOut` (proved).** Let `𝒜/ℤ[s]` spread out `A`, and
`y ≠ 0` an integer with `y·a` integral for every `a ∈ s` (`exists_integral_multiples`). For a prime
`p ∤ y` and `w ∣ p`, `y` is a unit and integral elements lie in the valuation ring `O_w`, so
`ℤ[s] ⊆ O_w`; the base change of `𝒜` to `O_w` is an abelian scheme (base-change stability) whose
generic fibre is that of `𝒜` (`Over.pullbackComp`, `Functor.mapGrpNatIso`). -/
theorem goodRedCofinite_of (h : AbSchemeSpreadsOut) : GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨s, 𝒜, h𝒜, ⟨e⟩⟩ := h L A
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpy : ¬ p ∣ y.natAbs := fun hd =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, hd, Int.natAbs_ne_zero.2 hy0⟩)
  obtain ⟨u, hu⟩ := isUnit_intCast_of_coprime (L := L) hp hv hpy
  have hinv : (y : L)⁻¹ ∈ Ow L v := by
    have h2 : ((u⁻¹ : (Ow L v)ˣ) : Ow L v) * (y : Ow L v) = 1 := by rw [← hu]; exact u.inv_mul
    have h3 : (((u⁻¹ : (Ow L v)ˣ) : Ow L v) : L) * (y : L) = 1 := by
      have := congrArg (fun z : Ow L v => (z : L)) h2
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left h3]
    exact ((u⁻¹ : (Ow L v)ˣ) : Ow L v).2
  have hmem : ∀ a ∈ s, a ∈ Ow L v := by
    intro a ha
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (show IsIntegral (Ow L v) (y • a) from (hyint a ha).tower_top)
    have hyL : (y : L) ≠ 0 := by exact_mod_cast hy0
    have ha' : a = (y : L)⁻¹ * (y • a) := by
      rw [zsmul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ hyL, _root_.one_mul]
    rw [ha', ← hb]
    exact mul_mem hinv b.2
  have hle : Subring.closure (s : Set L) ≤ (Ow L v).toSubring :=
    Subring.closure_le.2 (fun a ha => hmem a ha)
  let φ : Subring.closure (s : Set L) →+* Ow L v := Subring.inclusion hle
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap (Subring.closure (s : Set L)) L)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫ ?_⟩
    exact (pullbackGrp_congr hcomp 𝒜).some ≪≫ e

end FrobPiecesGood

end
