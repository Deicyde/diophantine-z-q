import RayProof4

/-! # rayclass-cft, Part P5: the CM data at a representative, the three fields, `RayClassCM` -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT ShimuraGlue.Ray
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## P5a. The object at a representative `(τ, u)` of `ιC^* y` -/

/-- At a representative `(τ, u)`, `u ∈ 𝒪̂^×`, of `ιC^* y`, the object is uniformized by `Λ_τ` and
inherits the CM of the object `P` of `y` (`R1fpProps` naturality, `ModuliAtUnits`, `CMBaseChange`). -/
theorem obj_at {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (hR1 : R1fpProps Y Φ) (hU : ModuliAtUnits Y Φ Ψ)
    (hB : CMBaseChange) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P)
    (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU) (hτu : Ψ τ u = fieldMap ιC ≫ y) :
    ∃ (P' : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts P'.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      HDec.HSyn.G0Split.FibreQM.IotaCompatible P' Φu ∧
      (HasCM4 P.q → HasCM4 P'.q) ∧ (HasCM3 P.q → HasCM3 P'.q) ∧ (HasCM24 P.q → HasCM24 P'.q) := by
  obtain ⟨-, -, -, hnat, -, -⟩ := hR1
  obtain ⟨Q, hQ, hbc⟩ := hnat Qbar ℂ ιC y P hP
  obtain ⟨P', hP', Φu, hun, hio⟩ := hU u hu τ
  rw [hτu, hQ] at hP'
  obtain ⟨f⟩ := Quotient.exact hP'
  let g : QMIso Q.q P'.q := ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩
  obtain ⟨b4, b3, b24⟩ := hB (ιC : Qbar →+* ℂ) P Q hbc
  exact ⟨P', Φu, hun, hio, fun h => HasCM4.of_iso g (b4 h), fun h => HasCM3.of_iso g (b3 h),
    fun h => HasCM24.of_iso g (b24 h)⟩

/-! ## P5b. From an eigen-element `β ∈ 𝒪` to the CM data `(q, κ₀)` -/

/-- **`𝒪_k = ℤ[y]`** (glue; for `k = ℚ(i), ℚ(ζ₃)` Mathlib's cyclotomic rings of integers, for
`ℚ(√−6)` the elementary computation `−6 ≡ 2 mod 4`). -/
def RingOfIntegersGen (k : Type) [Field k] [NumberField k] (y : k) : Prop :=
  ∀ x : 𝓞 k, ∃ a b : ℤ, (x : k) = a + b * y

theorem inO_int_comb {β : LeafQM.B} (hβ : InO β) (a b : ℤ) : InO ((a : LeafQM.B) + (b : LeafQM.B) * β) :=
  (LeafQM.O.add_mem (intCast_mem LeafQM.O a) (LeafQM.O.mul_mem (intCast_mem LeafQM.O b) hβ) :
    ((a : LeafQM.B) + (b : LeafQM.B) * β) ∈ LeafQM.O)

/-- The CM data from an eigen-element. -/
theorem cm_data (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {yk : k}
    (hy : ∀ r : ℚ, yk ≠ r) {P Q : ℚ} (hyq : yk * yk + P * yk + Q = 0) (hO : RingOfIntegersGen k yk)
    (τ : UpperHalfPlane) (β : LeafQM.B) (hβO : InO β)
    (hβ : β * β + P • β + algebraMap ℚ LeafQM.B Q = 0) (lam : ℂ)
    (heig : Matrix.mulVec ((BPAnalytic.QM.iota β).map (algebraMap ℝ ℂ)) ![(τ : ℂ), 1] =
      lam • ![(τ : ℂ), 1]) :
    ∃ (q : k →ₐ[ℚ] LeafQM.B) (κ₀ : k →+* ℂ), (∀ x : 𝓞 k, InO (q x)) ∧ IsCMPoint q κ₀ τ := by
  have heig' : Matrix.mulVec (iotaC β) ![(τ : ℂ), 1] = lam • ![(τ : ℂ), 1] := heig
  have hl := eig_rel (v := ![(τ : ℂ), 1]) (by simp) heig' hβ
  refine ⟨liftQuad hk hy hyq β hβ, (liftQuad hk hy hyq lam hl).toRingHom, fun x => ?_, fun a => ?_⟩
  · obtain ⟨a, b, hab⟩ := hO x
    have e : (x : k) = ((a : ℚ) : k) + ((b : ℚ) : k) * yk := by rw [hab]; push_cast; ring
    rw [e, liftQuad_apply]
    have e2 : algebraMap ℚ LeafQM.B (a : ℚ) + (b : ℚ) • β = (a : LeafQM.B) + (b : LeafQM.B) * β := by
      rw [Algebra.smul_def]; simp
    rw [e2]
    exact inO_int_comb hβO a b
  · obtain ⟨r, s, rfl⟩ := exists_rat_repr hk hy a
    show Matrix.mulVec (iotaC _) _ = _
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftQuad_apply, liftQuad_apply, map_add,
      AlgHom.commutes, map_smul, Matrix.add_mulVec, Matrix.smul_mulVec, heig']
    ext i
    fin_cases i <;>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal, Algebra.smul_def] <;> ring

/-! ## P5c. The three fields -/

theorem not_rat_of_disc {k : Type} [Field k] [CharZero k] {y : k} {P Q : ℚ}
    (hyq : y * y + P * y + Q = 0) (hd : P * P < 4 * Q) : ∀ r : ℚ, y ≠ r := by
  intro r hr
  rw [hr] at hyq
  have : r * r + P * r + Q = 0 := by exact_mod_cast hyq
  nlinarith [sq_nonneg (2 * r + P)]

theorem isTotallyComplex_of_root {k : Type} [Field k] [NumberField k] {y : k} {P Q : ℚ}
    (hyq : y * y + P * y + Q = 0) (hd : P * P < 4 * Q) : IsTotallyComplex k := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
  intro hr
  set z := w.embedding y
  have hz : z * z + P * z + Q = 0 := by
    have := congrArg w.embedding hyq
    simpa [z] using this
  have hconj : (starRingEnd ℂ) z = z :=
    congrArg (fun f => f y) (NumberField.ComplexEmbedding.isReal_iff.1 hr)
  have him : z.im = 0 := Complex.conj_eq_iff_im.1 hconj
  have hre := congrArg Complex.re hz
  simp [Complex.mul_re, him] at hre
  have hd' : (P : ℝ) * P < 4 * Q := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * z.re + P)]

/-- `i = ζ₄`. -/
def y4 : K4 := IsCyclotomicExtension.zeta 4 ℚ K4
/-- `−ζ₃` (a root of `X² − X + 1`). -/
def y3 : K3 := -IsCyclotomicExtension.zeta 3 ℚ K3
/-- `√−6` in `K24 = ℚ(s6)`. -/
def y24 : K24 := ⟨s6, IntermediateField.mem_adjoin_simple_self ℚ s6⟩

theorem y4_rel : y4 * y4 + ((0 : ℚ) : K4) * y4 + ((1 : ℚ) : K4) = 0 := by
  have hz := IsCyclotomicExtension.zeta_spec 4 ℚ K4
  have h2 : (y4 ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hz.pow_eq_one
  have hne : y4 ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  rcases sq_eq_one_iff.1 h2 with h | h
  · exact absurd h hne
  · push_cast; linear_combination h

theorem y3_rel : y3 * y3 + ((-1 : ℚ) : K3) * y3 + ((1 : ℚ) : K3) = 0 := by
  have hz := IsCyclotomicExtension.zeta_spec 3 ℚ K3
  have e3 : (IsCyclotomicExtension.zeta 3 ℚ K3) ^ 2 + IsCyclotomicExtension.zeta 3 ℚ K3 + 1 = 0 := by
    have := hz.isRoot_cyclotomic (by norm_num)
    simpa [Polynomial.cyclotomic_three, Polynomial.eval_add, Polynomial.eval_pow] using this
  simp only [y3]; push_cast; linear_combination e3

theorem y24_rel : y24 * y24 + ((0 : ℚ) : K24) * y24 + ((6 : ℚ) : K24) = 0 := by
  apply Subtype.ext
  have h6 : (((6 : ℚ) : K24) : CyclotomicField 24 ℚ) = 6 := by
    show ((6 : ℚ) : CyclotomicField 24 ℚ) = 6
    norm_num
  have h0 : (((0 : ℚ) : K24) : CyclotomicField 24 ℚ) = 0 := by
    show ((0 : ℚ) : CyclotomicField 24 ℚ) = 0
    norm_num
  simp only [y24, IntermediateField.coe_add, IntermediateField.coe_mul, h6, h0,
    IntermediateField.coe_zero]
  linear_combination s6_sq

theorem finrank_K4 : Module.finrank ℚ K4 = 2 := by
  rw [IsCyclotomicExtension.finrank K4 (n := 4) (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

theorem finrank_K3 : Module.finrank ℚ K3 = 2 := by
  rw [IsCyclotomicExtension.finrank K3 (n := 3) (Polynomial.cyclotomic.irreducible_rat (n := 3) (by norm_num))]
  decide

theorem finrank_K24 : Module.finrank ℚ K24 = 2 := by
  have hint : IsIntegral ℚ s6 := (Algebra.IsIntegral.isIntegral (R := ℚ) s6)
  rw [IntermediateField.adjoin.finrank hint]
  have hmin : (Polynomial.X ^ 2 + Polynomial.C (6 : ℚ)) = minpoly ℚ s6 := by
    refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
    · refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
      · rw [Polynomial.natDegree_X_pow_add_C]; norm_num
      · intro x hx
        simp [Polynomial.IsRoot] at hx
        nlinarith [sq_nonneg x]
    · simp [s6_sq]
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  rw [← hmin, Polynomial.natDegree_X_pow_add_C]

instance : IsTotallyComplex K4 := isTotallyComplex_of_root y4_rel (by norm_num)
instance : IsTotallyComplex K3 := isTotallyComplex_of_root y3_rel (by norm_num)
instance : IsTotallyComplex K24 := isTotallyComplex_of_root y24_rel (by norm_num)

/-! ## P5d. `RayClassCM` -/

theorem com_rel {Q : QML3 ℂ} (ρ : com Q.q →+* LeafQM.B) {φ : PkgI3.AbVar.End Q.A} (hφ : φ ∈ com Q.q)
    {P0 Q0 : ℤ} (h : φ * φ + P0 * φ + Q0 = 0) :
    ρ ⟨φ, hφ⟩ * ρ ⟨φ, hφ⟩ + ((P0 : ℚ)) • ρ ⟨φ, hφ⟩ + algebraMap ℚ LeafQM.B (Q0 : ℚ) = 0 := by
  have e : (⟨φ, hφ⟩ : com Q.q) * ⟨φ, hφ⟩ + (P0 : com Q.q) * ⟨φ, hφ⟩ + (Q0 : com Q.q) = 0 :=
    Subtype.ext (by simpa using h)
  have := congrArg ρ e
  simp only [map_add, map_mul, map_intCast, map_zero] at this
  rw [Algebra.smul_def, map_intCast, map_intCast]
  exact this

/-- **`RayClassCM` from the leaves `ShimuraMainThmIDeligneY3AbU`, `MumfordRigidityCore`,
`ClassNumberOneB` and the glue `QHatIntegral` (three fields), `CMBaseChange`, `CMAnalytic`,
`RingOfIntegersGen` (three fields).** -/
theorem rayClassCM_of (hL : ShimuraMainThmIDeligneY3AbU)
    (hMR : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) (hCN : ClassNumberOneB)
    (hI4 : QHatIntegral K4) (hI3 : QHatIntegral K3) (hI24 : QHatIntegral K24)
    (hB : CMBaseChange) (hA : CMAnalytic)
    (hO4 : RingOfIntegersGen K4 y4) (hO3 : RingOfIntegersGen K3 y3)
    (hO24 : RingOfIntegersGen K24 y24) : RayClassCM := by
  obtain ⟨Y, Φ, hAb, Ψ, hb, hU⟩ := hL
  have hR1 : R1fpProps Y Φ := (LeafQM.AV.R1UnivRigid.r1fpProps_iff_ab_core hMR Y Φ).2 hAb
  refine ⟨Y, Φ, hR1, fun y P hP => ⟨fun h4 => ?_, fun h3 => ?_, fun h24 => ?_⟩⟩
  · refine embed_core hb hCN K4 finrank_K4 hI4 y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, c4, -, -⟩ := obj_at hR1 hU hB y P hP τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c4 h4
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K4 finrank_K4 (not_rat_of_disc y4_rel (by norm_num)) y4_rel hO4 τ _ hβO ?_ lam heig
    have := com_rel ρ hφ (P0 := 0) (Q0 := 1) (by rw [hφ2]; simp)
    simpa using this
  · refine embed_core hb hCN K3 finrank_K3 hI3 y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, -, c3, -⟩ := obj_at hR1 hU hB y P hP τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c3 h3
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K3 finrank_K3 (not_rat_of_disc y3_rel (by norm_num)) y3_rel hO3 τ _ hβO ?_ lam heig
    have := com_rel ρ hφ (P0 := -1) (Q0 := 1) (by rw [← hφ2]; simp; abel)
    simpa using this
  · refine embed_core hb hCN K24 finrank_K24 hI24 y (fun τ u hu hτu => ?_)
    obtain ⟨P', Φu, hun, hio, -, -, c24⟩ := obj_at hR1 hU hB y P hP τ u hu hτu
    obtain ⟨ρ, hρ⟩ := hA τ P' Φu hun hio
    obtain ⟨φ, hφ, hφ2⟩ := c24 h24
    obtain ⟨hβO, lam, heig⟩ := hρ ⟨φ, hφ⟩
    refine cm_data K24 finrank_K24 (not_rat_of_disc y24_rel (by norm_num)) y24_rel hO24 τ _ hβO ?_
      lam heig
    have := com_rel ρ hφ (P0 := 0) (Q0 := 6) (by rw [hφ2]; simp)
    simpa using this

end RayClassCFT

#print axioms RayClassCFT.embed_core
#print axioms RayClassCFT.rayClassCM_of
