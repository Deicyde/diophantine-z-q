import ZInQKernel.Contrib.OneProof.RC.Stages.Kummer
import Mathlib.FieldTheory.Galois.Profinite
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.KatoHypV
import ZInQKernel.Contrib.OneProof.RC.Stages.Lattice
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.IndexAlgebra
import ZInQKernel.Contrib.OneProof.RC.Height.Torsion

/-! Tex 8312–8339: topology of the translation group, the central-scalar
obstruction, and the effect of adding a fixed auxiliary extension. -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Stages

variable {A : WeierstrassCurve ℚ} {Q : GeomPoint A}

/-- The cocycle is continuous in the inverse-limit topology: every component
depends on the action on two algebraic coordinates. -/
theorem DivisionTower.continuous_cocycle (d : DivisionTower A Q) (hQ) :
    Continuous (d.cocycle hQ) := by
  apply TateModule.continuous_iff.mpr
  intro n
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro σ
  have hx : ∀ x : Qbar, ∀ᶠ g in nhds σ, g x = σ x := fun x =>
    (IsLocallyConstant.iff_eventually_eq _).mp
      ((Algebra.IsIntegral.isIntegral (R := ℚ) x).isLocallyConstant_apply) σ
  cases hP : d.point n with
  | zero =>
    exact Filter.Eventually.of_forall (fun g => Subtype.ext (by simp [d.coe_proj_cocycle, hP, ← Affine.Point.zero_def]))
  | some x y hxy =>
    filter_upwards [hx x, hx y] with g hgx hgy
    apply Subtype.ext
    simp only [d.coe_proj_cocycle, hP, Affine.Point.map_some, AlgEquiv.coe_toAlgHom]
    congr 2

/-- The compact translation image over the kernel of the Tate action. -/
theorem DivisionTower.closed_image [A.IsElliptic] (d : DivisionTower A Q) (hQ) :
    IsClosed ((d.cocycle hQ) '' ((additiveRep A).ker : Set GalQ)) := by
  apply IsCompact.isClosed
  apply IsCompact.image _ (d.continuous_cocycle hQ)
  apply IsClosed.isCompact
  have hs : ((additiveRep A).ker : Set GalQ) =
      ⋂ x : TateMod A 2, {g | tateRep A 2 g x = x} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hg x
      exact DFunLike.congr_fun hg x
    · intro hg
      exact AddMonoidHom.ext hg
  rw [hs]
  exact isClosed_iInter fun x =>
    isClosed_singleton.preimage
      ((A.continuous_tateModuleGaloisRepresentation_apply 2).comp
        (continuous_id.prodMk continuous_const))

/-- The noncommuting lifts of a scalar and an arbitrary Galois element give the
central-scalar identity integrally when the translation image is zero. -/
theorem DivisionTower.scalar_identity_of_zero_translations (d : DivisionTower A Q) (hQ)
    (hzero : ∀ h : GalQ, additiveRep A h = 1 → d.cocycle hQ h = 0)
    {z : GalQ} {k : ℕ}
    (hz : ∀ x : TateMod A 2, tateRep A 2 z x = (1 + (2 : ℤ_[2]) ^ k) • x) (g : GalQ) :
    (2 ^ k : ℕ) • d.cocycle hQ g = tateRep A 2 g (d.cocycle hQ z) - d.cocycle hQ z := by
  let ρ := additiveRep A
  let c := d.cocycle hQ
  have hc := d.isCocycle hQ
  have hcomm : ρ (z * g) = ρ (g * z) := by
    rw [map_mul, map_mul]
    apply AddMonoidHom.ext
    intro x
    change tateRep A 2 z (tateRep A 2 g x) = tateRep A 2 g (tateRep A 2 z x)
    rw [hz, hz, map_smul]
  have hk : ρ ((g * z)⁻¹ * (z * g)) = 1 := by
    calc
      ρ ((g * z)⁻¹ * (z * g)) = ρ ((g * z)⁻¹) * ρ (z * g) := map_mul _ _ _
      _ = ρ ((g * z)⁻¹) * ρ (g * z) := congrArg (ρ ((g * z)⁻¹) * ·) hcomm
      _ = ρ ((g * z)⁻¹ * (g * z)) := (map_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, map_one]
  have heq : c (z * g) = c (g * z) := by
    have h := hc (g * z) ((g * z)⁻¹ * (z * g))
    rw [hzero _ hk, map_zero, add_zero, ← mul_assoc, mul_inv_cancel, one_mul] at h
    exact h
  change d.cocycle hQ (z * g) = d.cocycle hQ (g * z) at heq
  rw [hc z g, hc g z] at heq
  change c z + tateRep A 2 z (c g) = c g + tateRep A 2 g (c z) at heq
  have hcast : (2 : ℤ_[2]) ^ k = ((2 ^ k : ℕ) : ℤ_[2]) := by push_cast <;> rfl
  rw [hz, add_smul, one_smul, hcast, Nat.cast_smul_eq_nsmul] at heq
  apply eq_sub_iff_add_eq.mpr
  apply add_left_cancel (a := c g)
  rw [← heq]
  abel

/-- Finite-level form of the Kummer injection contradiction. If all translations
vanished, the fixed multiple of Q would have a rational division point at every level.
The fixed point produced here is Q_n corrected by the scalar lift's cocycle. -/
theorem DivisionTower.fixed_divisions_of_zero_translations (d : DivisionTower A Q) (hQ)
    (hzero : ∀ h : GalQ, additiveRep A h = 1 → d.cocycle hQ h = 0)
    {z : GalQ} {k : ℕ}
    (hz : ∀ x : TateMod A 2, tateRep A 2 z x = (1 + (2 : ℤ_[2]) ^ k) • x) (n : ℕ) :
    ∃ R : GeomPoint A, (2 ^ n : ℕ) • R = (2 ^ k : ℕ) • Q ∧
      ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom R = R := by
  let v := TateModule.proj n (d.cocycle hQ z)
  refine ⟨(2 ^ k : ℕ) • d.point n - v.val, ?_, ?_⟩
  · rw [nsmul_sub, smul_comm, d.divides, AddSubgroup.torsionBy.nsmul_iff.mp v.property, sub_zero]
  · intro g
    have hs := congrArg (fun t : TateMod A 2 => (TateModule.proj n t : GeomPoint A))
      (d.scalar_identity_of_zero_translations hQ hzero hz g)
    change ((TateModule.proj n ((2 ^ k : ℕ) • d.cocycle hQ g) : GeomPoint A)) =
      (TateModule.proj n (tateRep A 2 g (d.cocycle hQ z) - d.cocycle hQ z) : GeomPoint A) at hs
    rw [map_nsmul, map_sub, AddSubgroup.coe_nsmul, AddSubgroup.coe_sub,
      d.coe_proj_cocycle, coe_proj_tateRep] at hs
    change (2 ^ k : ℕ) • (Affine.Point.map g.toAlgHom (d.point n) - d.point n) =
      Affine.Point.map g.toAlgHom v.val - v.val at hs
    rw [nsmul_sub] at hs
    rw [map_sub, map_nsmul]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hs

/-- Fixed division points over the algebraic closure are rational. -/
theorem fixedPoint_descends (R : GeomPoint A)
    (hR : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom R = R) :
    ∃ R₀ : (A⁄ℚ).toAffine.Point, Affine.Point.baseChange (W' := A) ℚ Qbar R₀ = R := by
  cases R with
  | zero => exact ⟨0, map_zero _⟩
  | some x y hxy =>
    have hcoord (g : GalQ) : g x = x ∧ g y = y := by
      have h := hR g
      rw [Affine.Point.map_some] at h
      injection h with hx hy
      exact ⟨hx, hy⟩
    obtain ⟨x₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun g => (hcoord g).1
    obtain ⟨y₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr fun g => (hcoord g).2
    simp only [← Algebra.ofId_apply] at hxy ⊢
    exact ⟨.some x₀ y₀ ((Affine.baseChange_nonsingular A
      (f := Algebra.ofId ℚ Qbar) (FaithfulSMul.algebraMap_injective ℚ Qbar) x₀ y₀).mp hxy),
      Affine.Point.map_some _ _⟩

/-- Intersecting with an auxiliary finite normal kernel retains a multiple of every
translation. This is independent of intersections between the fields. -/
theorem DivisionTower.translation_in_auxiliary (d : DivisionTower A Q) (hQ)
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀]
    {h : GalQ} (hh : additiveRep A h = 1) :
    ∃ h₀ : GalQ, h₀ ∈ F₀.fixingSubgroup ∧ additiveRep A h₀ = 1 ∧
      d.cocycle hQ h₀ = F₀.fixingSubgroup.index • d.cocycle hQ h := by
  refine ⟨h ^ F₀.fixingSubgroup.index, F₀.fixingSubgroup.pow_index_mem h, ?_,
    (d.isCocycle hQ).pow_of_ker hh _⟩
  rw [map_pow, hh, one_pow]

/-- The Kummer injection argument using exact rational divisions and Northcott.
This gives the same contradiction as the rational cohomological injection in
tex 8325–8327; the finite-level proof avoids constructing rational cohomology (c). -/
theorem DivisionTower.nonzero_translations [A.IsElliptic] (d : DivisionTower A Q) (hQ)
    (P : (A⁄ℚ).toAffine.Point)
    (hP : Affine.Point.baseChange (W' := A) ℚ Qbar P = Q) (hnt : ¬ IsOfFinAddOrder P)
    (hS : SerreThm3) (hA : HasNoCM A) :
    ∃ h : GalQ, additiveRep A h = 1 ∧ d.cocycle hQ h ≠ 0 := by
  by_contra! hzero
  obtain ⟨k, hk, z, hz⟩ := serre_scalar hS A hA
  let P' := (2 ^ k : ℕ) • P
  have hpos : 0 < (P').canonicalHeight := by
    change 0 < ((2 ^ k : ℕ) • P).canonicalHeight
    rw [Affine.Point.canonicalHeight_nsmul]
    have := (Height.canonicalHeight_pos_iff (A⁄ℚ) P).mpr hnt
    positivity
  have hfin : twoDivIndex ⊤ P' ≠ ⊤ :=
    twoDivIndex_ne_top (fun n x => Affine.Point.canonicalHeight_nsmul n x)
      (fun B => Northcott.finite_le (h := Affine.Point.canonicalHeight) B) hpos
  apply hfin
  apply top_le_iff.mp
  apply ENat.forall_natCast_le_iff_le.mp
  intro n _
  obtain ⟨R, hR, hfix⟩ := d.fixed_divisions_of_zero_translations hQ hzero hz n
  obtain ⟨R₀, hR₀⟩ := fixedPoint_descends R hfix
  let f := Affine.Point.baseChange (W' := A) ℚ Qbar
  have he : (2 ^ n : ℕ) • R₀ = P' := by
    apply Affine.Point.map_injective (Algebra.ofId ℚ Qbar)
    change f ((2 ^ n : ℕ) • R₀) = f ((2 ^ k : ℕ) • P)
    rw [map_nsmul, map_nsmul, hR₀, hP, hR]
  exact (le_twoDivIndex_iff (AddSubgroup.mem_top P') n).mpr
    ⟨R₀, AddSubgroup.mem_top _, by rw [he, sub_self]; simp⟩

/-- Conjugation of a translation is the action of the corresponding Tate matrix. -/
theorem DivisionTower.conjugate_translation (d : DivisionTower A Q) (hQ)
    (g h : GalQ) (hh : additiveRep A h = 1) :
    d.cocycle hQ (g * h * g⁻¹) = additiveRep A g (d.cocycle hQ h) := by
  let c := d.cocycle hQ
  let ρ := additiveRep A
  have hc := d.isCocycle hQ
  have hinv := hc g g⁻¹
  rw [mul_inv_cancel, hc.map_one] at hinv
  rw [hc, hc, map_mul, hh, mul_one]
  change c g + ρ g (c h) + ρ g (c g⁻¹) = ρ g (c h)
  rw [add_comm (c g), add_assoc, ← hinv, add_zero]

/-- The closed subgroup of translations is a 2-adic submodule. -/
def DivisionTower.translationModule [A.IsElliptic] (d : DivisionTower A Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q) :
    Submodule ℤ_[2] (TateMod A 2) := by
  let H : AddSubgroup (TateMod A 2) :=
    (d.restriction hQ (additiveRep A).ker le_rfl).range.toAddSubgroup
  have he : (H : Set (TateMod A 2)) = (d.cocycle hQ) '' ((additiveRep A).ker : Set GalQ) := by
    ext x
    change (∃ h : (additiveRep A).ker, d.cocycle hQ h = x) ↔ _
    exact ⟨fun ⟨h, hx⟩ => ⟨h, h.property, hx⟩, fun ⟨h, hh, hx⟩ => ⟨⟨h, hh⟩, hx⟩⟩
  have hH : IsClosed (H : Set (TateMod A 2)) := by
    rw [he]
    exact d.closed_image hQ
  exact { H with smul_mem' := fun r _ hx => smul_mem_of_closed H hH hx r }

/-- Tex 8327–8328, with explicit unipotents (c). A nonzero translation generates
a full 2-power lattice under Serre's open congruence subgroup. -/
theorem DivisionTower.full_translations [A.IsElliptic] (d : DivisionTower A Q) (hQ)
    (hS : SerreThm3) (hA : HasNoCM A)
    {h : GalQ} (hh : additiveRep A h = 1) (hnz : d.cocycle hQ h ≠ 0) :
    ∃ a : ℕ, ∀ x : TateMod A 2, ∃ g : GalQ, additiveRep A g = 1 ∧
      d.cocycle hQ g = (2 ^ a : ℕ) • x := by
  obtain ⟨n, hn, ho⟩ := serre_two_adic hS A hA
  let B := tateBasis A
  let H := d.translationModule hQ
  have hstable : ∀ i j : Fin 2, i ≠ j → ∀ x ∈ H,
      x + (2 : ℤ_[2]) ^ n • (B.coord j x • B i) ∈ H := by
    intro i j hij x hx
    change ∃ t : (additiveRep A).ker, d.cocycle hQ t = _ at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨g, hg⟩ := ho (elementary B i j hij ((2 : ℤ_[2]) ^ n))
      (fun y => ⟨B.coord j y • B i, elementary_apply ..⟩)
    refine ⟨⟨g * t.val * g⁻¹, (inferInstance : (additiveRep A).ker.Normal).conj_mem _ t.property g⟩, ?_⟩
    rw [d.conjugate_translation hQ _ _ (MonoidHom.mem_ker.mp t.property)]
    change tateRep A 2 g _ = _
    rw [hg]
    exact elementary_apply ..
  obtain ⟨a, ha⟩ := full_lattice_of_unipotents B H hstable
    (v := d.cocycle hQ h) ⟨⟨h, MonoidHom.mem_ker.mpr hh⟩, rfl⟩ hnz
  refine ⟨a, fun x => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : (additiveRep A).ker, d.cocycle hQ g = (2 : ℤ_[2]) ^ a • x := ha x
  exact ⟨g, MonoidHom.mem_ker.mp g.property, by
    have hcast : (2 : ℤ_[2]) ^ a = ((2 ^ a : ℕ) : ℤ_[2]) := by push_cast <;> rfl
    rw [hg, hcast, Nat.cast_smul_eq_nsmul]⟩

/-- The full lattice still holds on the common kernel, with a possibly larger
exponent. A power of two lies in the ideal of the finite index. -/
theorem DivisionTower.full_translations_auxiliary [A.IsElliptic] (d : DivisionTower A Q) (hQ)
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀] [FiniteDimensional ℚ F₀]
    (a : ℕ) (ha : ∀ x : TateMod A 2, ∃ g : GalQ, additiveRep A g = 1 ∧
      d.cocycle hQ g = (2 ^ a : ℕ) • x) :
    ∃ e : ℕ, ∀ x : TateMod A 2, ∃ g : GalQ, g ∈ F₀.fixingSubgroup ∧
      additiveRep A g = 1 ∧ d.cocycle hQ g = (2 ^ e : ℕ) • x := by
  let m := F₀.fixingSubgroup.index
  have hm : m ≠ 0 := by
    change F₀.fixingSubgroup.index ≠ 0
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨n, u, hu⟩ := exists_two_pow_mul (c := (m : ℤ_[2])) (by exact_mod_cast hm)
  refine ⟨n + a, fun x => ?_⟩
  obtain ⟨g, hg, ht⟩ := ha (u • x)
  obtain ⟨g₀, hF₀, hg₀, hc⟩ := d.translation_in_auxiliary hQ F₀ hg
  refine ⟨g₀, hF₀, hg₀, ?_⟩
  rw [hc, ht]
  simp only [← Nat.cast_smul_eq_nsmul ℤ_[2], Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, smul_smul, pow_add]
  change ((m : ℤ_[2]) * ((2 : ℤ_[2]) ^ a * u)) • x = _
  rw [show (m : ℤ_[2]) * ((2 : ℤ_[2]) ^ a * u) = ((m : ℤ_[2]) * u) * (2 : ℤ_[2]) ^ a by ring,
    ← hu]

/-- Choose one stage detector and one exponent, after the auxiliary field is
fixed. The two explicit hypotheses on the Tate action of τ are its involution
property and the existence of a +1 eigenspace (in rank two, det = -1 suffices). -/
theorem DivisionTower.exists_fixed_detector [A.IsElliptic] (d : DivisionTower A Q) (hQ)
    (P : (A⁄ℚ).toAffine.Point) (hP : Affine.Point.baseChange (W' := A) ℚ Qbar P = Q)
    (hnt : ¬ IsOfFinAddOrder P) (hS : SerreThm3) (hA : HasNoCM A)
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀] [FiniteDimensional ℚ F₀]
    {τ : GalQ} (hτ : τ * τ = 1) (hneg : tateRep A 2 τ ≠ -1) :
    ∃ (a : ℕ) (h : GalQ) (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]),
      h ∈ F₀.fixingSubgroup ∧
      additiveRep A (h * τ) = additiveRep A τ ∧
      (∀ x, b (tateRep A 2 τ x) = b x) ∧
      Function.Surjective b ∧
      b (d.cocycle hQ ((h * τ) * (h * τ))) = 2 ^ (a + 1) := by
  have hC : ∀ x, tateRep A 2 τ (tateRep A 2 τ x) = x := by
    intro x
    change (tateRep A 2 τ * tateRep A 2 τ) x = x
    rw [← map_mul, hτ, map_one]; rfl
  obtain ⟨b, t, hb, ht⟩ := primitive_row_of_involution (tateBasis A) _ hC hneg
  obtain ⟨h, hh, hne⟩ := d.nonzero_translations hQ P hP hnt hS hA
  obtain ⟨a₀, ha₀⟩ := d.full_translations hQ hS hA hh hne
  obtain ⟨a, ha⟩ := d.full_translations_auxiliary hQ F₀ a₀ ha₀
  obtain ⟨g, hgF, hg, hv⟩ := ha t
  obtain ⟨hρ, hval⟩ := d.detectingElement hQ hg hτ b.toAddMonoidHom hb t ht a hv
  refine ⟨a, g, b, hgF, hρ, hb, ?_, hval⟩
  intro v
  exact ⟨v • t, by rw [map_smul, ht, smul_eq_mul, mul_one]⟩

#print axioms DivisionTower.exists_fixed_detector
#print axioms DivisionTower.nonzero_translations
#print axioms DivisionTower.conjugate_translation
#print axioms DivisionTower.translationModule
#print axioms DivisionTower.full_translations
#print axioms DivisionTower.full_translations_auxiliary
#print axioms DivisionTower.continuous_cocycle
#print axioms DivisionTower.closed_image
#print axioms DivisionTower.scalar_identity_of_zero_translations
#print axioms DivisionTower.fixed_divisions_of_zero_translations
#print axioms fixedPoint_descends
#print axioms DivisionTower.translation_in_auxiliary

end ZInQ.Manuscript.RC.Stages
