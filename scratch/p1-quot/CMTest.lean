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

theorem M3.twist_refl' (m : M3 Qbar) : M3.twist (RingEquiv.refl LeafQM.O) m = m :=
  Quotient.inductionOn m (fun _ => rfl)

/-- From `u u₀ ≡ 1` and `u ≡ ε` (`ε² = 1`): `u₀ ≡ ε`. -/
theorem congr_inv_of_congr {u u₀ ε c c' : O} (hε : ε * ε = 1) (hc : u * u₀ - 1 = 3 * c)
    (hc' : u - ε = 3 * c') : u₀ - ε = 3 * (ε * c - ε * c' * u₀) := by
  have : u₀ - ε = ε * (u * u₀ - 1) - ε * (u - ε) * u₀ := by
    have h1 : ε * (u * u₀ - 1) - ε * (u - ε) * u₀ = ε * ε * u₀ - ε := by noncomm_ring
    rw [h1, hε, _root_.one_mul]
  rw [this, hc, hc']; noncomm_ring

/-- **The `ℤ[i]` case of `CMStabObjWeak`**, from T5, `AutCM24` and a `ℤ[√−6]` object. -/
theorem cmStab4_of (hT : ObjBridge.TorsionStructure) (hA : AutCM24) (P₂₄ : QML3 Qbar)
    (h24 : HasCM24 P₂₄.q) (P : QML3 Qbar) (hP : HasCM4 P.q) :
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m := by
  obtain ⟨φ, hφc, hφ2⟩ := hP
  have h1 : φ * -φ = 1 := by rw [mul_neg, hφ2, neg_neg]
  have h2 : -φ * φ = 1 := by rw [neg_mul, hφ2, neg_neg]
  obtain ⟨u, u₀, hlin, ⟨c, hc⟩, hfix⟩ := rightMul_fix_of_unit hT P φ (-φ) hφc h1 h2
  -- `φ` cannot act on `A[3]` by `±1`
  have hsq : ∀ ε : O, ε * ε = 1 → (∃ c' : O, u₀ - ε = 3 * c') → False := by
    intro ε hε ⟨c', hc'⟩
    have hact : ∀ a, endPt P.A Qbar φ (P.e.eta a) = P.e.eta (a * ε) := by
      intro a
      rw [hlin, P.e.eq_iff]
      exact ⟨a * c', by
        calc a * u₀ - a * ε = a * (u₀ - ε) := by noncomm_ring
          _ = a * (3 * c') := by rw [hc']
          _ = 3 * (a * c') := by noncomm_ring⟩
    have e1 : endPt P.A Qbar (φ * φ) (P.e.eta 1) = P.e.eta 1 := by
      rw [map_mul]
      change endPt P.A Qbar φ (endPt P.A Qbar φ (P.e.eta 1)) = _
      rw [hact, hact, _root_.one_mul, hε]
    rw [hφ2, map_neg, map_one] at e1
    change -P.e.eta 1 = P.e.eta 1 at e1
    have e2 : P.e.eta ((2 : ℤ) : O) = 0 := by
      have : ((2 : ℤ) : O) = 1 + 1 := by norm_num
      rw [this, map_add]
      conv_lhs => arg 1; rw [← e1]
      exact neg_add_cancel _
    obtain ⟨c'', hc''⟩ := (P.e.ker _).1 e2
    exact intCast_not_mem_three 2 (by decide) ⟨c'', hc''⟩
  refine ⟨RingEquiv.refl _, u, by rw [M3.twist_refl']; exact hfix, ⟨M3.mk P₂₄, ?_⟩⟩
  rw [M3.twist_refl']
  apply rightMul_moves_cm24 hA P₂₄ h24 u
  · rintro ⟨c', hc'⟩
    exact hsq 1 (_root_.one_mul 1) ⟨_, congr_inv_of_congr (_root_.one_mul 1) hc hc'⟩
  · rintro ⟨c', hc'⟩
    refine hsq (-1) (by noncomm_ring) ⟨_, congr_inv_of_congr (by noncomm_ring) hc (c' := c') ?_⟩
    rw [sub_neg_eq_add, hc']

/-- Endomorphisms commute with base change of points. -/
theorem endPt_bcPt (P : QML3 Qbar) (f : AbVar.End P.A) (y : P.A.Pt Qbar) :
    endPt P.A (AlgebraicClosure Qbar) f
        (Additive.ofMul (bcPt P.A y : P.A.Pt (AlgebraicClosure Qbar))) =
      Additive.ofMul (bcPt P.A (Additive.toMul (endPt P.A Qbar f (Additive.ofMul y))) :
        P.A.Pt (AlgebraicClosure Qbar)) := by
  change Additive.ofMul ((toKbar Qbar ≫ y) ≫ f.hom) = Additive.ofMul (toKbar Qbar ≫ y ≫ f.hom)
  rw [Category.assoc]

/-- **A primitive sixth root of unity in the commutant does not act by `−1` on `A[3]`** (T5: with
`χ = φ + 1`, `χ² = 3χ − 3`; `χ` kills `A[3]`; on a point `x` of order 9, `χ(x) ∈ A[3]` so `0 = χ²(x) = −3x`). -/
theorem not_act_neg_one (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) (φ : AbVar.End P.A)
    (hφ : φ * φ - φ + 1 = 0) (u₀ : O)
    (hlin : ∀ a, endPt P.A Qbar φ (P.e.eta a) = P.e.eta (a * u₀))
    (hu : ∃ c : O, u₀ + 1 = 3 * c) : False := by
  obtain ⟨c, hc⟩ := hu
  set χ : AbVar.End P.A := φ + 1 with hχ
  have hφ' : φ * φ = φ - 1 := by
    rw [← sub_eq_zero, ← hφ]; abel
  have h3 : (3 : AbVar.End P.A) = 1 + 1 + 1 := by norm_num
  have hχ2 : χ * χ = 3 * χ - 3 := by
    rw [hχ, add_mul, mul_add, mul_add, hφ', _root_.mul_one, _root_.one_mul, _root_.mul_one, h3,
      add_mul, add_mul, _root_.one_mul]
    abel
  -- `χ` kills the image of `η`
  have hkill : ∀ a, endPt P.A Qbar χ (P.e.eta a) = 0 := by
    intro a
    rw [hχ, map_add, map_one]
    change endPt P.A Qbar φ (P.e.eta a) + P.e.eta a = 0
    rw [hlin, ← map_add, P.e.ker]
    exact ⟨a * c, by
      calc a * u₀ + a = a * (u₀ + 1) := by noncomm_ring
        _ = a * (3 * c) := by rw [hc]
        _ = 3 * (a * c) := by noncomm_ring⟩
  -- `χ` kills `A(L)[3]`
  have hkill3 : ∀ z : Additive (P.A.Pt (AlgebraicClosure Qbar)), (3 : ℕ) • z = 0 → endPt P.A (AlgebraicClosure Qbar) χ z = 0 := by
    intro z hz
    have hz1 : (Additive.toMul z) ^ 3 = (1 : P.A.Pt (AlgebraicClosure Qbar)) := by
      rw [← toMul_nsmul, hz]; rfl
    obtain ⟨a, ha⟩ := Level3.onto hT P (Additive.toMul z) hz1
    have hz2 : z = Additive.ofMul (bcPt P.A (Additive.toMul (P.e.eta a)) :
        P.A.Pt (AlgebraicClosure Qbar)) := by
      apply Additive.toMul.injective; exact ha.symm
    rw [hz2]
    refine (endPt_bcPt P χ (Additive.toMul (P.e.eta a))).trans ?_
    rw [ofMul_toMul, hkill]
    change Additive.ofMul (toKbar Qbar ≫ (1 : P.A.Pt Qbar)) = 0
    rw [MonObj.comp_one]; rfl
  -- a point of order 9
  have hdim : ObjBridge.dim (_root_.ObjBridge.toGrp P.A) = ((2 : ℕ) : WithBot ℕ∞) := by
    change P.A.dim = _
    rw [P.surface]; rfl
  obtain ⟨e, he⟩ := hT Qbar (_root_.ObjBridge.toGrp P.A) 2 9 hdim (by norm_num) (Nat.cast_ne_zero.mpr (by norm_num))
  set x := (e.symm (fun _ => 1)).1 with hxdef
  have hx9 : x ^ 9 = 1 := (e.symm (fun _ => 1)).2
  have he1 : e ⟨1, by simp [PkgI2.torsion]⟩ = 0 := by
    have := he ⟨1, by simp [PkgI2.torsion]⟩ ⟨1, by simp [PkgI2.torsion]⟩
      (by simp [PkgI2.torsion])
    simp only [_root_.mul_one] at this
    calc e ⟨1, _⟩ = (e ⟨1, _⟩ + e ⟨1, _⟩) - e ⟨1, _⟩ := by abel
      _ = e ⟨1, _⟩ - e ⟨1, _⟩ := by rw [← this]
      _ = 0 := sub_self _
  have hx3 : x ^ 3 ≠ 1 := by
    intro h3
    have m1 : x * x ∈ PkgI2.torsion (_root_.ObjBridge.toGrp P.A) (AlgebraicClosure Qbar) 9 := by
      simp only [PkgI2.torsion, Set.mem_ofPred_eq]; rw [mul_pow, hx9, _root_.one_mul]
    have m2 : x * x * x ∈ PkgI2.torsion (_root_.ObjBridge.toGrp P.A) (AlgebraicClosure Qbar) 9 := by
      simp only [PkgI2.torsion, Set.mem_ofPred_eq]; rw [mul_pow, mul_pow, hx9, _root_.one_mul,
        _root_.one_mul]
    have hxx := he (e.symm (fun _ => 1)) (e.symm (fun _ => 1)) m1
    have hxxx := he ⟨x * x, m1⟩ (e.symm (fun _ => 1)) m2
    rw [Equiv.apply_symm_apply] at hxx hxxx
    rw [hxx] at hxxx
    have h1 : (⟨x * x * x, m2⟩ : PkgI2.torsion (_root_.ObjBridge.toGrp P.A) (AlgebraicClosure Qbar) 9) = ⟨1, by simp [PkgI2.torsion]⟩ := by
      apply Subtype.ext
      show x * x * x = 1
      rw [← h3, pow_succ, pow_two]
    rw [h1, he1] at hxxx
    have := congrFun hxxx 0
    simp at this
    exact absurd this (by decide)
  -- the contradiction
  set x' : P.A.Pt (AlgebraicClosure Qbar) := x with hx'
  have hx9' : x' ^ 9 = 1 := hx9
  have hx3' : x' ^ 3 ≠ 1 := hx3
  set X : Additive (P.A.Pt (AlgebraicClosure Qbar)) := Additive.ofMul x' with hX
  have hX9 : (9 : ℕ) • X = 0 := by rw [hX, ← ofMul_pow, hx9']; rfl
  have hX3 : (3 : ℕ) • X ≠ 0 := by
    rw [hX, ← ofMul_pow]; intro h; exact hx3' (Additive.ofMul.injective h)
  have k1 : endPt P.A (AlgebraicClosure Qbar) χ ((3 : ℕ) • X) = 0 :=
    hkill3 _ (by rw [← mul_nsmul']; exact hX9)
  have k2 : endPt P.A (AlgebraicClosure Qbar) χ (endPt P.A (AlgebraicClosure Qbar) χ X) = 0 := by
    apply hkill3
    rw [← map_nsmul, k1]
  have h3n : ∀ y : Additive (P.A.Pt (AlgebraicClosure Qbar)), (3 : ℕ) • y = y + y + y := by
    intro y; rw [succ_nsmul, two_nsmul]
  have hχ2' : χ * χ = χ + χ + χ - 1 - 1 - 1 := by
    rw [hχ, add_mul, mul_add, mul_add, hφ', _root_.mul_one, _root_.one_mul, _root_.mul_one]
    abel
  clear_value χ
  have k3 : endPt P.A (AlgebraicClosure Qbar) (χ * χ) X =
      endPt P.A (AlgebraicClosure Qbar) χ X + endPt P.A (AlgebraicClosure Qbar) χ X +
        endPt P.A (AlgebraicClosure Qbar) χ X - (X + X + X) := by
    rw [hχ2', map_sub, map_sub, map_sub, map_add, map_add, map_one]
    have e : ∀ (f : AddMonoid.End (Additive (P.A.Pt (AlgebraicClosure Qbar)))),
        (f + f + f - 1 - 1 - 1) X = f X + f X + f X - (X + X + X) := by
      intro f
      show f X + f X + f X - X - X - X = _
      abel
    exact e _
  rw [map_mul] at k3
  change endPt P.A (AlgebraicClosure Qbar) χ (endPt P.A (AlgebraicClosure Qbar) χ X) = _ at k3
  rw [k2, ← h3n, ← map_nsmul, k1, zero_sub, ← h3n] at k3
  exact hX3 (neg_eq_zero.mp k3.symm)

end MCRQuot

end
