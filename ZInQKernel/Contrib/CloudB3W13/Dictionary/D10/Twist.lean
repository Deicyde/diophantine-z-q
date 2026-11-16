/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D10.Trace
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D9.Proof

/-!
# D10: the `twist` clause over the FLT fine moduli scheme (W13)

For `α ∈ Aut(𝒪)` the FLT objects are twisted by `act ↦ act ∘ α` (same scheme, group law, level
subscheme and level point); `trd_ringEquiv` supplies `act_trace`. `ptF ∘ twist` is a second
fine-moduli structure on the same `M`, so `IsFineModuli.exists_iso_of_isFineModuli` gives the
automorphism of `M`; the fibre comparison is as in D9.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

namespace D10

variable (α : LeafQM.O ≃+* LeafQM.O)

/-- `α` on the FLT lattice. -/
def aΛ (x : ↥Λ) : ↥Λ := toΛ (α (ofΛ x))

theorem coe_aΛ (x : ↥Λ) : ((aΛ α x : ↥Λ) : ℍ[ℚ, 2, -3]) = ((α (ofΛ x) : LeafQM.O) : ℍ[ℚ, 2, -3]) := rfl

theorem aΛ_symm (x : ↥Λ) : aΛ α (aΛ α.symm x) = x := by
  apply Subtype.ext; simp [coe_aΛ, aΛ, ofΛ, toΛ]

theorem aΛ_symm' (x : ↥Λ) : aΛ α.symm (aΛ α x) = x := by
  apply Subtype.ext; simp [coe_aΛ, aΛ, ofΛ, toΛ]

theorem aΛ_add (x y : ↥Λ) : aΛ α (x + y) = aΛ α x + aΛ α y := by
  apply Subtype.ext
  simp only [coe_aΛ, Submodule.coe_add]
  rw [show ofΛ (x + y) = ofΛ x + ofΛ y from Subtype.ext rfl, map_add, Subring.coe_add]

theorem mem_mul (x y : ↥Λ) : ((x : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3])) ∈ Λ := by
  have := (toΛ (ofΛ x * ofΛ y)).2
  rwa [coe_toΛ, Subring.coe_mul] at this

theorem aΛ_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3]) ∈ Λ) :
    aΛ α ⟨(x : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3]), h⟩ =
      ⟨(aΛ α x : ℍ[ℚ, 2, -3]) * (aΛ α y : ℍ[ℚ, 2, -3]), mem_mul _ _⟩ := by
  apply Subtype.ext
  simp only [coe_aΛ]
  rw [show ofΛ ⟨(x : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3]), h⟩ = ofΛ x * ofΛ y from Subtype.ext rfl,
    map_mul, Subring.coe_mul]

theorem trd_aΛ (m : ↥Λ) :
    (aΛ α m : ℍ[ℚ, 2, -3]) + star (aΛ α m : ℍ[ℚ, 2, -3]) = (m : ℍ[ℚ, 2, -3]) + star (m : ℍ[ℚ, 2, -3]) := by
  rw [QuaternionAlgebra.self_add_star', QuaternionAlgebra.self_add_star', coe_aΛ,
    trd_ringEquiv α (ofΛ m)]
  simp only [zero_mul, add_zero]
  rfl

theorem smul_three_iff (z : ↥Λ) :
    (∃ y : ↥Λ, (z : ℍ[ℚ, 2, -3]) = ((3 : ℕ) : ℚ) • (y : ℍ[ℚ, 2, -3])) ↔ ∃ w : LeafQM.O, ofΛ z = 3 * w := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨ofΛ y, Subtype.ext (by rw [Subring.coe_mul, coe_three]; rw [smul_three_eq] at hy; exact hy)⟩
  · rintro ⟨w, hw⟩
    refine ⟨toΛ w, ?_⟩
    rw [smul_three_eq, coe_toΛ, ← coe_three, ← Subring.coe_mul, ← hw]
    rfl

theorem three_dvd_aΛ_iff (z : ↥Λ) :
    (∃ y : ↥Λ, (aΛ α z : ℍ[ℚ, 2, -3]) = ((3 : ℕ) : ℚ) • (y : ℍ[ℚ, 2, -3])) ↔
      ∃ y : ↥Λ, (z : ℍ[ℚ, 2, -3]) = ((3 : ℕ) : ℚ) • (y : ℍ[ℚ, 2, -3]) := by
  rw [smul_three_iff, smul_three_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨α.symm w, ?_⟩
    have : α (ofΛ z) = 3 * w := hw
    have := congrArg α.symm this
    rw [map_mul, map_ofNat, RingEquiv.symm_apply_apply] at this
    exact this
  · rintro ⟨w, hw⟩
    refine ⟨α w, ?_⟩
    show α (ofΛ z) = _
    rw [hw, map_mul, map_ofNat]

variable {S : Type} [CommRing S]

/-- The twisted fake elliptic curve: `act ↦ act ∘ α`. -/
def twistE (E : FLT.CerednikDrinfeld.QM.FakeEllipticCurve Λ 1 S) :
    FLT.CerednikDrinfeld.QM.FakeEllipticCurve Λ 1 S where
  A := E.A
  f := E.f
  L := E.L
  comm := E.comm
  bundle := E.bundle
  dim_fibre := E.dim_fibre
  act x := E.act (aΛ α x)
  act_over x := E.act_over (aΛ α x)
  act_hom x := E.act_hom (aΛ α x)
  act_one h := by
    rw [show aΛ α ⟨1, h⟩ = ⟨1, h⟩ from Subtype.ext (by
      simp only [coe_aΛ]; rw [show ofΛ ⟨1, h⟩ = 1 from Subtype.ext rfl, map_one]; rfl)]
    exact E.act_one h
  act_mul x y h := by
    rw [aΛ_mul α x y h]
    exact E.act_mul (aΛ α x) (aΛ α y) _
  act_add x y T t P := by
    rw [aΛ_add α x y]
    exact E.act_add (aΛ α x) (aΛ α y) t P
  act_trace k _ _ sk V _ _ _ τ hinj hrange hmul hsmul m Φ hΦ n hn :=
    E.act_trace k sk V τ hinj hrange hmul hsmul (aΛ α m) Φ hΦ n (by rw [trd_aΛ]; exact hn)
  C := E.C
  lev := E.lev
  lev_closed := E.lev_closed
  lev_sub := E.lev_sub
  lev_one := E.lev_one
  lev_torsion := E.lev_torsion
  lev_stable x := E.lev_stable (aΛ α x)
  lev_finite := E.lev_finite
  lev_flat := E.lev_flat
  lev_finitePresentation := E.lev_finitePresentation
  lev_rank := E.lev_rank
  lev_fibre := E.lev_fibre

/-- The full level datum of the twisted curve (same point). -/
def twistFL (E : FLT.CerednikDrinfeld.QM.FakeEllipticCurve Λ 1 S) (P : E.FullLevel 3) :
    (twistE α E).FullLevel 3 where
  P := P.P
  torsion := P.torsion
  generates k _ _ sk Q hQ := by
    obtain ⟨x, hx⟩ := P.generates k sk Q hQ
    refine ⟨aΛ α.symm x, ?_⟩
    rw [← aΛ_symm α x] at hx
    exact hx
  annihilator k _ _ sk x := by
    exact (P.annihilator k sk (aΛ α x)).trans (three_dvd_aΛ_iff α x)

/-- The twist on objects with full level. -/
def twistW (u : FLT.CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ 1 3 S) :
    FLT.CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ 1 3 S :=
  ⟨twistE α u.1, twistFL α u.1 u.2⟩

open FLT.CerednikDrinfeld.QM in
theorem iso_twistW {u u' : FakeEllipticCurve.WithFullLevel Λ 1 3 S}
    (h : FakeEllipticCurve.WithFullLevel.Iso u u') :
    FakeEllipticCurve.WithFullLevel.Iso (twistW α u) (twistW α u') := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  exact ⟨e, he, hmul, fun x => hact (aΛ α x), hlev, hP⟩

open FLT.CerednikDrinfeld.QM in
theorem iso_of_twistW {u u' : FakeEllipticCurve.WithFullLevel Λ 1 3 S}
    (h : FakeEllipticCurve.WithFullLevel.Iso (twistW α u) (twistW α u')) :
    FakeEllipticCurve.WithFullLevel.Iso u u' := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  refine ⟨e, he, hmul, fun x => ?_, hlev, hP⟩
  have := hact (aΛ α.symm x)
  change u.1.act (aΛ α (aΛ α.symm x)) ≫ e.hom = e.hom ≫ u'.1.act (aΛ α (aΛ α.symm x)) at this
  rwa [aΛ_symm] at this

open FLT.CerednikDrinfeld.QM in
theorem isPullback_twistW {S' : Type} [CommRing S'] (φ : S →+* S')
    {u : FakeEllipticCurve.WithFullLevel Λ 1 3 S} {u' : FakeEllipticCurve.WithFullLevel Λ 1 3 S'}
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :
    FakeEllipticCurve.WithFullLevel.IsPullback φ (twistW α u) (twistW α u') := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := h
  exact ⟨g, hg, hmul, fun x => hact (aΛ α x), hlev, hP⟩

open FLT.CerednikDrinfeld.QM in
theorem iso_twistW_symm (u : FakeEllipticCurve.WithFullLevel Λ 1 3 S) :
    FakeEllipticCurve.WithFullLevel.Iso (twistW α (twistW α.symm u)) u := by
  refine ⟨Iso.refl _, Category.id_comp _, fun t P Q => ?_, fun x => ?_, fun t P => ?_, ?_⟩
  · apply Subtype.ext; simp [FLT.CerednikDrinfeld.QM.mapPt_coe]; rfl
  · change u.1.act (aΛ α.symm (aΛ α x)) ≫ 𝟙 _ = 𝟙 _ ≫ u.1.act x
    rw [aΛ_symm', Category.comp_id, Category.id_comp]
  · simp only [FLT.CerednikDrinfeld.QM.FactorsThrough, FLT.CerednikDrinfeld.QM.mapPt_coe, Iso.refl_hom,
      Category.comp_id]
    rfl
  · exact Subtype.ext (Category.comp_id _)

open FLT.CerednikDrinfeld.QM in
/-- `ptF ∘ twist α` is again a fine moduli structure on `M`. -/
theorem isFineModuli_twist {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : PtF 𝒪 πM} (hM : IsFineModuli Λ 1 3 M πM ptF) :
    IsFineModuli Λ 1 3 M πM (fun S _ s u => ptF S s (twistW α u)) where
  ptF_iso S _ s u u' h := hM.ptF_iso S s _ _ (iso_twistW α h)
  ptF_pullback S S' _ _ φ s s' hs u u' h := hM.ptF_pullback S S' φ s s' hs _ _ (isPullback_twistW α φ h)
  ptF_surjective S _ s x := by
    obtain ⟨u, hu⟩ := hM.ptF_surjective S s x
    exact ⟨twistW α.symm u, (hM.ptF_iso S s _ _ (iso_twistW_symm α u)).trans hu⟩
  ptF_injective S _ s u u' h := iso_of_twistW α (hM.ptF_injective S s _ _ h)

end D10

end ZInQ.Contrib.CloudB2Shimura.Dictionary
