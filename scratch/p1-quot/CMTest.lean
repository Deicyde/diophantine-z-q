import ZInQKernel.Contrib.OneProof.QuotientP1.FixedDisjoint

namespace HDec

set_option maxHeartbeats 1000000
set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open MonoidalCategory CartesianMonoidalCategory MonObj

/-- The level structure `φ ∘ η` for an invertible `φ` in the commutant. -/
def levelComp (P : QML3 Qbar) (φ ψ : AbVar.End P.A) (hφ : φ ∈ com P.q) (h2 : ψ * φ = 1) :
    Level3 P.q where
  eta := (endPt P.A Qbar φ).comp P.e.eta
  linear a b := by
    have hc : φ * P.q.iota a = P.q.iota a * φ := by
      rw [com, Subring.mem_centralizer_iff] at hφ
      exact (hφ _ ⟨a, rfl⟩).symm
    change endPt P.A Qbar φ (P.e.eta (a * b)) = qmAct P.q Qbar a (endPt P.A Qbar φ (P.e.eta b))
    rw [P.e.linear]
    simp only [qmAct, RingHom.comp_apply]
    have := congrArg (fun F : AddMonoid.End (Additive (AbVar.Pt Qbar P.A)) => F (P.e.eta b))
      (congrArg (endPt P.A Qbar) hc)
    simp only [map_mul] at this
    exact this
  ker a := by
    change endPt P.A Qbar φ (P.e.eta a) = 0 ↔ _
    rw [← P.e.ker]
    constructor
    · intro h
      have h3 := congrArg (endPt P.A Qbar ψ) h
      have h4 := congrArg (fun F : AddMonoid.End (Additive (AbVar.Pt Qbar P.A)) => F (P.e.eta a))
        (congrArg (endPt P.A Qbar) h2)
      simp only [map_mul, map_one] at h4
      rw [map_zero] at h3
      exact h4.symm.trans h3
    · intro h; rw [h, map_zero]

/-- **An invertible element of the commutant fixes a class under some `rightMul`.** If `φ ∈ com P.q` is
invertible, then `φ(η(a)) = η(a u₀)` for some `u₀` invertible mod 3 (T5, `Level3.torsor`), and for a unit `u` with
`u u₀ ≡ 1` (`exists_unit_congr`) `φ` is an isomorphism `rightMul u P ≅ P`. -/
theorem rightMul_fix_of_unit (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) (φ ψ : AbVar.End P.A)
    (hφ : φ ∈ com P.q) (h1 : φ * ψ = 1) (h2 : ψ * φ = 1) :
    ∃ (u : Oˣ) (u₀ : O), (∀ a, endPt P.A Qbar φ (P.e.eta a) = P.e.eta (a * u₀)) ∧
      (∃ c : O, (u : O) * u₀ - 1 = 3 * c) ∧ M3.rightMul u (M3.mk P) = M3.mk P := by
  obtain ⟨u₀, v₀, hvu, hlin⟩ := Level3.torsor hT P (levelComp P φ ψ hφ h2)
  obtain ⟨u', d, hd⟩ := TSHeckeUnits.exists_unit_congr u₀ v₀ hvu
  refine ⟨u'⁻¹, u₀, hlin, ⟨(↑u'⁻¹ : O) * d, ?_⟩, ?_⟩
  · have : (↑u'⁻¹ : O) * u₀ - 1 = (↑u'⁻¹ : O) * (u₀ - u') := by
      rw [mul_sub, Units.inv_mul]
    rw [this, hd]; noncomm_ring
  · have hcom : ∀ a, φ * P.q.iota a = P.q.iota a * φ := by
      intro a
      rw [com, Subring.mem_centralizer_iff] at hφ
      exact (hφ _ ⟨a, rfl⟩).symm
    obtain ⟨c, hc⟩ : ∃ c : O, (↑u'⁻¹ : O) * u₀ - 1 = 3 * c := ⟨(↑u'⁻¹ : O) * d, by
      have : (↑u'⁻¹ : O) * u₀ - 1 = (↑u'⁻¹ : O) * (u₀ - u') := by
        rw [mul_sub, Units.inv_mul]
      rw [this, hd]; noncomm_ring⟩
    apply Quotient.sound
    exact ⟨{
      φ := φ
      ψ := ψ
      left := congrArg AbVar.Hom.hom h2
      right := congrArg AbVar.Hom.hom h1
      equivariant := fun a => (congrArg AbVar.Hom.hom (hcom a))
      level := fun a => by
        change endPt P.A Qbar φ (P.e.eta (a * ↑u'⁻¹)) = P.e.eta a
        rw [show endPt P.A Qbar φ (P.e.eta (a * ↑u'⁻¹)) = (levelComp P φ ψ hφ h2).eta (a * ↑u'⁻¹)
          from rfl, hlin, P.e.eq_iff]
        exact ⟨a * c, calc a * ↑u'⁻¹ * u₀ - a = a * (↑u'⁻¹ * u₀ - 1) := by noncomm_ring
          _ = a * (3 * c) := by rw [hc]
          _ = 3 * (a * c) := by noncomm_ring⟩ }⟩

/-- An integer not divisible by 3 is not in `3𝒪`. -/
theorem intCast_not_mem_three (k : ℤ) (hk : ¬ (3 : ℤ) ∣ k) : ¬ ∃ c : O, (k : O) = 3 * c := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := c.2
  have h := congrArg Subtype.val hc
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [Subring.coe_mul, h33] at h
  rw [show ((c : O) : B) = ofInt m from hm, _root_.LeafQM.AV.three_mul_ofInt] at h
  have hk' : ((k : O) : B) = (k : B) := map_intCast O.subtype k
  rw [hk'] at h
  have hJ := congrArg QuaternionAlgebra.imJ h
  have hR := congrArg QuaternionAlgebra.re h
  simp [ofInt] at hJ hR
  apply hk
  refine ⟨m 0, ?_⟩
  have hm2 : (m 2 : ℚ) = 0 := by linarith
  have : (k : ℚ) = 3 * m 0 := by rw [hR, hm2]; ring
  exact_mod_cast this

/-- **Glue (AutCM24): the automorphisms of a QM pair with CM by `ℤ[√−6]` are `±1`** (the units of an order in
`ℚ(√−6)`; a consequence of the chain's `QMCentralizerCM`). -/
def AutCM24 : Prop :=
  ∀ (P : QML3 Qbar), HasCM24 P.q → ∀ c d : AbVar.End P.A, c ∈ com P.q → c * d = 1 → d * c = 1 →
    c = 1 ∨ c = -1

/-- **`rightMul u` moves the class of a `ℤ[√−6]` object unless `u ≡ ±1 mod 3𝒪`** (given `AutCM24`). -/
theorem rightMul_moves_cm24 (hA : AutCM24) (P : QML3 Qbar) (hP : HasCM24 P.q) (u : Oˣ)
    (h1 : ¬ ∃ c : O, (u : O) - 1 = 3 * c) (h2 : ¬ ∃ c : O, (u : O) + 1 = 3 * c) :
    M3.rightMul u (M3.mk P) ≠ M3.mk P := by
  intro h
  obtain ⟨f⟩ : Nonempty ((P.rightMul u).Iso P) := Quotient.exact h
  let c : AbVar.End P.A := f.φ
  let d : AbVar.End P.A := f.ψ
  have hc : c ∈ com P.q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact AbVar.Hom.ext' (f.equivariant a).symm
  have hlev : ∀ a, endPt P.A Qbar c (P.e.eta (a * u)) = P.e.eta a := f.level
  rcases hA P hP c d hc (AbVar.Hom.ext' f.right) (AbVar.Hom.ext' f.left) with he | he
  · have := hlev 1
    rw [he, map_one, _root_.one_mul] at this
    exact h1 ((P.e.eq_iff _ _).1 this)
  · have := hlev 1
    rw [he, map_neg, map_one, _root_.one_mul] at this
    change -P.e.eta (u : O) = P.e.eta 1 at this
    rw [← map_neg] at this
    obtain ⟨c, hc'⟩ := (P.e.eq_iff _ _).1 this
    exact h2 ⟨-c, by rw [mul_neg, ← hc']; noncomm_ring⟩

end MCRQuot

end
