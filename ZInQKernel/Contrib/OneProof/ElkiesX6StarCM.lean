import ZInQKernel.Contrib.OneProof.X6AtkinLehnerIdeal
import ZInQKernel.Contrib.OneProof.R5fpCountLe
import ZInQKernel.Contrib.OneProof.ElkiesC.ClassNumber24

/-!
# elkies-c: Elkies' CM values at **every** CM point, from the CM point of each discriminant

Task elkies-c (docs/research/elkies-c.md). The leaf `X6ALIdeal.ElkiesX6StarEveryIdeal` (x6-coarse; it discharges the
bundle field `elkiesX6StarEvery`) states Elkies' CM values `t = 0, 1, ∞` at **every** `ℚ̄`-point whose QM pair
satisfies `HasCM24`, `HasCM4`, `HasCM3` (some `φ ∈ End_𝒪(A)` with `φ² = −6`, `φ² = −1`, `φ² − φ + 1 = 0`). Elkies
(1998, §3, p. 17 and Table 1) prints the value at *the* CM point of each discriminant of `X*(6) = X₀(6,1)/W`. Two
steps separate the two readings (x6-coarse §4.1 step (c), and the reviewer's deciding step for this row):

1. **exactness** ("the `HasCM` set is Elkies' CM points"): `HasCM_D P.q → End_𝒪(A) ≅ R_D`, `R_D` the order of
   discriminant `D` (`com_equiv_of_hasCM24` etc.; the lattice model of gr56-prove, `GR56.com_equiv_of_eig`), and the
   converse; with gr-dict's dictionary this is `IsGRCMPoint` (`hasCM24_iff_isGRCMPoint` etc.);
2. **"every" from "one"** (step (c)): the `ℚ̄`-points with `HasCM_D` are exactly two, conjugate under
   `Aut(ℚ̄/ℚ)`, so a `ℚ`-rational coordinate takes one value on them. The count `≤ 2` is
   `EichlerBound.r5fpCountLe_proof` (`#CM(R) ≤ 2^{b(k)} h(R)`) with `h = 1, 1` for `ℤ[i]`, `ℤ[ζ₃]` (Pi0X6) and
   `h(ℤ[√−6]) ≤ 2`, `b(ℚ(√−6)) = 0` (proved in `ElkiesC.ClassNumber24`); the Galois stability is the Galois clause of
   `X6Props`; the conjugate point differs from the first because Elkies' charts give it a coordinate `√−3` or
   `√−1` (`s² = −t`, `r² = 3(t − 1)`).

The new leaf `ElkiesX6StarOneIdeal` is `ElkiesX6StarEveryIdeal` with the CM clause replaced by its printed form
"the CM point of discriminant `−24` (resp. `−4`, `−3`) is at `t = 0` (resp. `1`, `∞`)", in the weakest reading:
**some** point with `HasCM_D` has that value. `elkiesX6StarEveryIdeal_of_one` proves the old leaf from it and the
three textbook fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`;
`elkiesX6StarEvery_of_one` discharges the bundle field `elkiesX6StarEvery`.

No `sorry`; standard axioms only.
-/

set_option linter.all false

noncomputable section

namespace ElkiesC

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open HDec.QMSplit.CNO (act act_add act_mul act_one act_smul act_zero)
open ShimuraGlue.Ray RayClassCFT

/-! ## 1. Elements of `𝒪` are integral over `ℤ` -/

theorem isIntegral_of_mem_O {b : B} (hb : b ∈ LeafQM.O) : IsIntegral ℤ b := by
  obtain ⟨n, rfl⟩ := (hb : InO b)
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 * n 0 + n 2) * Polynomial.X +
      Polynomial.C (n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2), ?_, ?_⟩
  · have hd : (Polynomial.X ^ 2 - Polynomial.C (2 * n 0 + n 2) * Polynomial.X +
        Polynomial.C (n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2) :
          Polynomial ℤ).natDegree = 2 := by compute_degree!
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one 2 hd.le ?_
    simp [Polynomial.coeff_X, Polynomial.coeff_C]
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    ext <;> simp [LeafQM.ofInt, sq] <;> ring

/-! ## 2. Exactness: a relation in `End_𝒪(A)` determines `End_𝒪(A)` -/

section Exact

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

/-- `P` has an element `φ ∈ End_𝒪(A)` with `φ² + pφ + q = 0`. -/
def HasRel {K : Type} [Field K] {A : PkgI3.AbVar K} (p q : ℤ) (qs : QMStr A) : Prop :=
  ∃ φ ∈ com qs, φ * φ + (p : PkgI3.AbVar.End A) * φ + (q : PkgI3.AbVar.End A) = 0

theorem hasRel_24 {K : Type} [Field K] {A : PkgI3.AbVar K} (qs : QMStr A) : HasCM24 qs ↔ HasRel 0 6 qs := by
  constructor
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, by rw [h]; push_cast; ring⟩
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, by push_cast at h; linear_combination h⟩

theorem hasRel_4 {K : Type} [Field K] {A : PkgI3.AbVar K} (qs : QMStr A) : HasCM4 qs ↔ HasRel 0 1 qs := by
  constructor
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, by rw [h]; push_cast; ring⟩
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, by push_cast at h; linear_combination h⟩

theorem hasRel_3 {K : Type} [Field K] {A : PkgI3.AbVar K} (qs : QMStr A) : HasCM3 qs ↔ HasRel (-1) 1 qs := by
  constructor
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, by push_cast; linear_combination h⟩
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, by push_cast at h; linear_combination h⟩

theorem hasRel_of_ringEquiv {K K' : Type} [Field K] [Field K'] {A : PkgI3.AbVar K} {A' : PkgI3.AbVar K'}
    {qs : QMStr A} {qs' : QMStr A'} (e : com qs ≃+* com qs') {p q : ℤ} (h : HasRel p q qs) : HasRel p q qs' := by
  obtain ⟨φ, hφ, hr⟩ := h
  refine ⟨(e ⟨φ, hφ⟩ : PkgI3.AbVar.End A'), (e ⟨φ, hφ⟩).2, ?_⟩
  have h1 : (⟨φ, hφ⟩ : com qs) * ⟨φ, hφ⟩ + (p : com qs) * ⟨φ, hφ⟩ + (q : com qs) = 0 :=
    Subtype.ext (by simpa using hr)
  have h2 := congrArg e h1
  simp only [map_add, map_mul, map_intCast, map_zero] at h2
  have h3 := congrArg Subtype.val h2
  simpa using h3

/-- The conductor of the maximal order is `1`. -/
theorem conductor_max (k : Type) [Field k] : conductor (integralClosure ℤ k).toSubring = 1 :=
  AddSubgroup.relIndex_self _

include hU hG hM in
/-- **Exactness.** If `End_𝒪(A)` (over `ℚ̄`) contains a root of `X² + pX + q`, the polynomial of a generator `y` of
`𝓞_k = ℤ[y]` (`k` imaginary quadratic), then `End_𝒪(A) ≅ 𝓞_k`. Lattice model: the scalar `c` of the root is an
eigenvalue `ι(x)v = cv` of some `x ∈ 𝒪` (`exists_O`), so `y ↦ x` is an optimal embedding `k → B` (its preimage of
`𝒪` consists of integral elements, and contains `ℤ[y] = 𝓞_k`), and `GR56.com_equiv_of_eig` reads `End_𝒪` off it. -/
theorem com_equiv_of_rel {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {yk : k}
    (hy : ∀ r : ℚ, yk ≠ r) {P Q : ℚ} (hyq : yk * yk + P * yk + Q = 0) (hO : RingOfIntegersGen k yk)
    {p q : ℤ} (hp : (p : ℚ) = P) (hq : (q : ℚ) = Q) (Pr : QMPair Qbar) (h : HasRel p q Pr.q) :
    Nonempty (com Pr.q ≃+* (integralClosure ℤ k).toSubring) := by
  obtain ⟨e0⟩ := GR56.com_bcQ Pr
  have h' : HasRel p q (GR56.bcQ Pr).q := hasRel_of_ringEquiv e0 h
  obtain ⟨φ, hφ, hr⟩ := h'
  set D := GR56.datQ hU hG hM Pr with hD
  have hC := AvSplit.Final.h69 hU hG
  have hA := (GR56.bcQ Pr).surface
  set φ' : com (GR56.bcQ Pr).q := ⟨φ, hφ⟩ with hφ'
  have hr' : φ' * φ' + (p : com _) * φ' + (q : com _) = 0 := Subtype.ext (by simpa using hr)
  set c := D.scal φ' with hcdef
  have hc : c * c + (p : ℂ) * c + (q : ℂ) = 0 := by
    have := congrArg D.scalHom hr'
    simp only [map_add, map_mul, map_intCast, map_zero, GR56.LatData.scalHom_apply] at this
    exact this
  obtain ⟨x, hxO, hx⟩ := D.exists_O hC hA φ'
  have hxrel : x * x + P • x + algebraMap ℚ B Q = 0 := by
    apply HDec.QMLattice.act_inj D.v_ne
    rw [act_add, act_add, act_mul, hx, HDec.QMLattice.act_smul_vec, hx, act_smul, hx,
      HDec.QMLattice.act_algebraMap, act_zero, smul_smul, smul_smul, ← add_smul, ← add_smul, ← hp, ← hq]
    push_cast
    rw [hc, zero_smul]
  have hcrel : c * c + P • c + algebraMap ℚ ℂ Q = 0 := by
    rw [← hp, ← hq, Rat.smul_def]; push_cast; exact hc
  set Φ := liftQuad hk hy hyq x hxrel with hΦ
  set ψ := (liftQuad hk hy hyq c hcrel).toRingHom with hψ
  have hint : ∀ a : k, IsIntegral ℤ a → Φ a ∈ LeafQM.O := by
    intro a ha
    obtain ⟨m, n, hmn⟩ := hO ⟨a, ha⟩
    have e : a = ((m : ℚ) : k) + ((n : ℚ) : k) * yk := by
      have : a = (m : k) + n * yk := hmn
      rw [this]; push_cast; ring
    rw [e, hΦ, liftQuad_apply]
    have e2 : algebraMap ℚ B (m : ℚ) + (n : ℚ) • x = (m : B) + (n : B) * x := by
      rw [Algebra.smul_def]; simp
    rw [e2]
    exact LeafQM.O.add_mem (intCast_mem LeafQM.O m) (LeafQM.O.mul_mem (intCast_mem LeafQM.O n) hxO)
  have hopt : LeafQM.O.comap Φ.toRingHom = (integralClosure ℤ k).toSubring := by
    ext a
    rw [Subring.mem_comap]
    constructor
    · intro ha
      have hi : IsIntegral ℤ (Φ a) := isIntegral_of_mem_O ha
      exact (isIntegral_algHom_iff (Φ.restrictScalars ℤ) Φ.toRingHom.injective).mp hi
    · intro ha
      exact hint a ha
  have heig : ∀ a, act ((⟨Φ, hopt⟩ : GRCountX6.OptEmb k _).1 a) D.v = ψ a • D.v := by
    intro a
    obtain ⟨r, s, rfl⟩ := exists_rat_repr hk hy a
    show act (Φ ((r : k) + s * yk)) D.v = ψ ((r : k) + s * yk) • D.v
    rw [hψ, hΦ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftQuad_apply, liftQuad_apply, act_add,
      HDec.QMLattice.act_algebraMap, act_smul, hx, Rat.smul_def, add_smul, smul_smul]
    simp
  obtain ⟨⟨e⟩, -⟩ := GR56.com_equiv_of_eig hC hA D hk (by rw [conductor_max]; norm_num) ⟨Φ, hopt⟩ ψ heig
  exact ⟨e0.trans e⟩

include hU hG hM in
theorem com_equiv_of_hasCM24 (Pr : QMPair Qbar) (h : HasCM24 Pr.q) : Nonempty (com Pr.q ≃+* R24) :=
  com_equiv_of_rel hU hG hM finrank_K24 y24_ne y24_rel ringOfIntegersGen_K24 (p := 0) (q := 6)
    (by norm_num) (by norm_num) Pr ((hasRel_24 _).1 h)

include hU hG hM in
theorem com_equiv_of_hasCM4 (Pr : QMPair Qbar) (h : HasCM4 Pr.q) : Nonempty (com Pr.q ≃+* Pi0X6.R4) :=
  com_equiv_of_rel hU hG hM finrank_K4 (not_rat_of_disc y4_rel (by norm_num)) y4_rel ringOfIntegersGen_K4
    (p := 0) (q := 1) (by norm_num) (by norm_num) Pr ((hasRel_4 _).1 h)

include hU hG hM in
theorem com_equiv_of_hasCM3 (Pr : QMPair Qbar) (h : HasCM3 Pr.q) : Nonempty (com Pr.q ≃+* Pi0X6.R3) :=
  com_equiv_of_rel hU hG hM finrank_K3 (not_rat_of_disc y3_rel (by norm_num)) y3_rel ringOfIntegersGen_K3
    (p := -1) (q := 1) (by norm_num) (by norm_num) Pr ((hasRel_3 _).1 h)

/-- Conversely `End_𝒪(A) ≅ 𝓞_k` gives the relation (pull back the generator). -/
theorem hasRel_of_com_equiv {k : Type} [Field k] [NumberField k] {yk : k} (hyi : IsIntegral ℤ yk) {p q : ℤ}
    (hyq : yk * yk + (p : k) * yk + (q : k) = 0) {Pr : QMPair Qbar}
    (e : com Pr.q ≃+* (integralClosure ℤ k).toSubring) : HasRel p q Pr.q := by
  set y : (integralClosure ℤ k).toSubring := ⟨yk, hyi⟩
  refine ⟨(e.symm y : PkgI3.AbVar.End Pr.A), (e.symm y).2, ?_⟩
  have h1 : y * y + (p : (integralClosure ℤ k).toSubring) * y + (q : (integralClosure ℤ k).toSubring) = 0 :=
    Subtype.ext (by simpa using hyq)
  have h2 := congrArg e.symm h1
  simp only [map_add, map_mul, map_intCast, map_zero] at h2
  have h3 := congrArg Subtype.val h2
  simpa using h3

end Exact

/-! ## 3. Galois stability of the `HasRel` points -/

section Galois

open HDec.G0ModField.KernelField (endBC)

theorem hasRel_bcAut (σ : Qbar →+* Qbar) (Pr : QMPair Qbar) {p q : ℤ} (h : HasRel p q Pr.q) :
    HasRel p q (X6ALIdeal.bcAut σ Pr).q := by
  letI : Algebra Qbar Qbar := σ.toAlgebra
  obtain ⟨φ, hφ, hr⟩ := h
  refine ⟨endBC Pr.A Qbar φ, ?_, ?_⟩
  · show endBC Pr.A Qbar φ ∈ Subring.centralizer (Set.range ((endBC Pr.A Qbar).comp Pr.q.iota))
    rw [Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have hc : Pr.q.iota a * φ = φ * Pr.q.iota a :=
      (Subring.mem_centralizer_iff.mp hφ) _ ⟨a, rfl⟩
    simp only [RingHom.comp_apply, ← map_mul, hc]
  · have := congrArg (endBC Pr.A Qbar) hr
    simpa using this

theorem hasRel_of_iso {K : Type} [Field K] {Pr Qr : QMPair K} (f : QMIso Pr.q Qr.q) {p q : ℤ}
    (h : HasRel p q Pr.q) : HasRel p q Qr.q :=
  hasRel_of_ringEquiv (comEquiv f) h

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {X : Over (Spec (CommRingCat.of ℚ))}
  {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}

/-- **The `HasRel` points are `Aut(ℚ̄/ℚ)`-stable** (Galois clause of `X6Props`, uniqueness of base change
`ShimuraSplit.bc_uniquePair`, and `End_𝒪` of the base change `bcAut σ`). -/
theorem hasRel_galPt (h6 : X6Props Y Φ X Ψ fY) (σ : Qbar ≃ₐ[ℚ] Qbar) {x : fieldPt Qbar ⟶ X} {Pr : QMPair Qbar}
    (hx : Ψ x = Quotient.mk _ Pr) {p q : ℤ} (h : HasRel p q Pr.q) :
    ∃ Qr : QMPair Qbar, Ψ (Pi0X6.galPt σ x) = Quotient.mk _ Qr ∧ HasRel p q Qr.q := by
  obtain ⟨Qr, hQ, hbc⟩ := h6.2.2.2.1 σ x Pr hx
  obtain ⟨f⟩ := ShimuraSplit.bc_uniquePair (X6ALIdeal.isBaseChange_bcAut (σ : Qbar →+* Qbar) Pr) hbc
  exact ⟨Qr, hQ, hasRel_of_iso f (hasRel_bcAut _ Pr h)⟩

end Galois

/-! ## 4. Counting: at most two classes -/

section Count

/-- Three points whose classes lie in a set of at most two elements: two of them coincide. -/
theorem two_of_three {α β : Type*} (Ψ : α ≃ β) (T : Set β) [Finite T] (hT : Nat.card T ≤ 2) (x y z : α)
    (hx : Ψ x ∈ T) (hy : Ψ y ∈ T) (hz : Ψ z ∈ T) : x = y ∨ x = z ∨ y = z := by
  let e := Finite.equivFin T
  have hcard : Nat.card T = Fintype.card (Fin (Nat.card T)) := by simp
  have ha := (e ⟨_, hx⟩).isLt
  have hb := (e ⟨_, hy⟩).isLt
  have hc := (e ⟨_, hz⟩).isLt
  have key : (e ⟨_, hx⟩).val = (e ⟨_, hy⟩).val ∨ (e ⟨_, hx⟩).val = (e ⟨_, hz⟩).val ∨
      (e ⟨_, hy⟩).val = (e ⟨_, hz⟩).val := by omega
  rcases key with k1 | k1 | k1
  · exact Or.inl (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1))))
  · exact Or.inr (Or.inl (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1)))))
  · exact Or.inr (Or.inr (Ψ.injective (congrArg Subtype.val (e.injective (Fin.ext k1)))))

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

include hU hG hM in
/-- **At most two classes with `End_𝒪 ≅ R`** for `R` with `2^{b(k)} h(R) ≤ 2` (`EichlerBound.r5fpCountLe_proof`). -/
theorem cm_le_two {k : Type} [Field k] [NumberField k] [NumberField.IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (hh0 : Nat.card (CommRing.Pic (integralClosure ℤ k).toSubring) ≠ 0)
    (hh : 2 ^ inertCount6 k * Nat.card (CommRing.Pic (integralClosure ℤ k).toSubring) ≤ 2) :
    Finite {c : Quotient (pairSetoid Qbar) //
        ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* (integralClosure ℤ k).toSubring)} ∧
      Nat.card {c : Quotient (pairSetoid Qbar) //
        ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* (integralClosure ℤ k).toSubring)} ≤ 2 := by
  obtain ⟨hf, hle⟩ := EichlerBound.r5fpCountLe_proof hU hG hM k hk (integralClosure ℤ k).toSubring le_rfl
    (by rw [conductor_max]; norm_num) hh0
  exact ⟨hf, hle.trans hh⟩

include hU hG hM in
theorem cm_le_two_24 :
    Finite {c : Quotient (pairSetoid Qbar) // ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R24)} ∧
      Nat.card {c : Quotient (pairSetoid Qbar) //
        ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R24)} ≤ 2 :=
  cm_le_two hU hG hM finrank_K24 pic_R24_ne_zero (by rw [inertCount6_K24]; simpa using pic_R24_le_two)

include hU hG hM in
theorem cm_le_two_4 :
    Finite {c : Quotient (pairSetoid Qbar) // ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* Pi0X6.R4)} ∧
      Nat.card {c : Quotient (pairSetoid Qbar) //
        ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* Pi0X6.R4)} ≤ 2 :=
  cm_le_two hU hG hM finrank_K4 (by rw [Pi0X6.pic_R4]; norm_num) (by rw [Pi0X6.inertCount6_K4, Pi0X6.pic_R4])

include hU hG hM in
theorem cm_le_two_3 :
    Finite {c : Quotient (pairSetoid Qbar) // ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* Pi0X6.R3)} ∧
      Nat.card {c : Quotient (pairSetoid Qbar) //
        ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* Pi0X6.R3)} ≤ 2 :=
  cm_le_two hU hG hM finrank_K3 (by rw [Pi0X6.pic_R3]; norm_num) (by rw [Pi0X6.inertCount6_K3, Pi0X6.pic_R3])

end Count

/-! ## 5. Elkies' charts: a point over `0`, `1` or `∞` is not `ℚ`-rational -/

section Charts

open X6Glue

/-- An element of `ℚ̄` fixed by every automorphism is rational. -/
theorem exists_moves {z : Qbar} (hz : ∀ r : ℚ, z ≠ algebraMap ℚ Qbar r) : ∃ σ : Qbar ≃ₐ[ℚ] Qbar, σ z ≠ z := by
  by_contra h
  push_neg at h
  have hmem : z ∈ IntermediateField.fixedField
      (IntermediateField.fixingSubgroup (⊥ : IntermediateField ℚ Qbar)) := fun σ => h σ.1
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.1 hmem
  exact hz r hr.symm

theorem not_rat_of_sq {z : Qbar} {d : ℚ} (hd : d < 0) (hz : z ^ 2 = (d : Qbar)) :
    ∀ r : ℚ, z ≠ algebraMap ℚ Qbar r := by
  intro r hr
  rw [hr, eq_ratCast, ← Rat.cast_pow] at hz
  have : r ^ 2 = d := Rat.cast_injective hz
  nlinarith [sq_nonneg r]

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}

/-- A point with a non-rational coordinate in its residue field is moved by some `σ`. -/
theorem galPt_ne_of_mem {x : fieldPt Qbar ⟶ X} {z : Qbar} (hzx : z ∈ residueImage (X := X.left) x.left)
    {d : ℚ} (hd : d < 0) (hz : z ^ 2 = (d : Qbar)) : ∃ σ : Qbar ≃ₐ[ℚ] Qbar, Pi0X6.galPt σ x ≠ x := by
  obtain ⟨σ, hσ⟩ := exists_moves (not_rat_of_sq hd hz)
  exact ⟨σ, fun h => hσ ((Pi0X6.galPt_eq_self_iff σ x).1 h z hzx)⟩

/-- Values of sections of `t.U` at a point of `t.U` lie in its residue field. -/
theorem eval_mem (x : fieldPt Qbar ⟶ X) (U : X.left.Opens)
    (h : (Scheme.SpecToEquivOfField Qbar X.left x.left).1 ∈ U) (f : Γ(X.left, U)) :
    (Scheme.SpecToEquivOfField Qbar X.left x.left).2
        (X.left.evaluation U _ h f) ∈ residueImage (X := X.left) x.left :=
  IntermediateField.subset_adjoin ℚ _ ⟨_, rfl⟩

/-- **At a point over a finite value `c`, Elkies' charts give `s(x)² = −c` and `r(x)² = 3(c − 1)` in the residue
field.** -/
theorem charts_at_some (hc : ElkiesCharts X t) (x : fieldPt Qbar ⟶ X) {c : Qbar}
    (hx : t.val (K := Qbar) x.left = OnePoint.some c) :
    (∃ s ∈ residueImage (X := X.left) x.left, s ^ 2 = -c) ∧
      ∃ r ∈ residueImage (X := X.left) x.left, r ^ 2 = 3 * (c - 1) := by
  obtain ⟨-, -, φU, φV, hT, -, -, -⟩ := hc
  set pt := Scheme.SpecToEquivOfField Qbar X.left x.left with hpt
  unfold ToP1.val at hx
  rw [← hpt] at hx
  by_cases h : pt.1 ∈ t.U
  swap
  · rw [dif_neg h] at hx; exact absurd hx.symm (OnePoint.coe_ne_infty _)
  rw [dif_pos h] at hx
  set ev : Γ(X.left, t.U) →+* Qbar := (X.left.evaluation t.U pt.1 h ≫ pt.2).hom with hev
  have hev_apply : ∀ f, ev f = pt.2 (X.left.evaluation t.U pt.1 h f) := fun f => rfl
  have hcT : ev (φU eT) = c := by
    rw [hT, hev_apply]; exact OnePoint.coe_injective hx
  refine ⟨⟨ev (φU eS), by rw [hev_apply]; exact eval_mem x t.U h _, ?_⟩,
    ⟨ev (φU eR), by rw [hev_apply]; exact eval_mem x t.U h _, ?_⟩⟩
  · have := congrArg (fun z => ev (φU z)) X6Glue.rel1
    simp only [map_add, map_pow, map_zero, hcT] at this
    linear_combination this
  · have := congrArg (fun z => ev (φU z)) X6Glue.rel2
    simp only [map_sub, map_pow, map_mul, map_one, map_ofNat, map_zero, hcT] at this
    linear_combination this

/-- **At a point over `∞`, Elkies' second chart gives `b(x)² = −3`** (`b = r/s`, `b² = 3(1/t − 1)`). -/
theorem charts_at_infty (hc : ElkiesCharts X t) (x : fieldPt Qbar ⟶ X)
    (hx : t.val (K := Qbar) x.left = OnePoint.infty) :
    ∃ b ∈ residueImage (X := X.left) x.left, b ^ 2 = -3 := by
  obtain ⟨-, -, φU, φV, -, hTg, -, -⟩ := hc
  set pt := Scheme.SpecToEquivOfField Qbar X.left x.left with hpt
  unfold ToP1.val at hx
  rw [← hpt] at hx
  by_cases h : pt.1 ∈ t.U
  · rw [dif_pos h] at hx; exact absurd hx (OnePoint.coe_ne_infty _)
  have hV : pt.1 ∈ t.V := by
    have := t.cover
    have hmem : pt.1 ∈ (t.U ⊔ t.V : X.left.Opens) := by rw [this]; trivial
    rcases (TopologicalSpace.Opens.mem_sup).1 hmem with h' | h'
    · exact absurd h' h
    · exact h'
  set ev : Γ(X.left, t.V) →+* Qbar := (X.left.evaluation t.V pt.1 hV ≫ pt.2).hom with hev
  have hev_apply : ∀ f, ev f = pt.2 (X.left.evaluation t.V pt.1 hV f) := fun f => rfl
  have hg0 : ev (φV eT) = 0 := by
    rw [hTg, hev_apply]
    have : X.left.evaluation t.V pt.1 hV t.g = 0 := by
      rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, t.basicOpen_g]
      exact fun h' => h h'.1
    rw [this, map_zero]
  refine ⟨ev (φV eR), by rw [hev_apply]; exact eval_mem x t.V hV _, ?_⟩
  have := congrArg (fun z => ev (φV z)) X6Glue.rel2
  simp only [map_sub, map_pow, map_mul, map_one, map_ofNat, map_zero, hg0] at this
  linear_combination this

theorem moved_of_val (hc : ElkiesCharts X t) (x : fieldPt Qbar ⟶ X)
    (hx : t.val (K := Qbar) x.left = OnePoint.some 0 ∨ t.val (K := Qbar) x.left = OnePoint.some 1 ∨
      t.val (K := Qbar) x.left = OnePoint.infty) :
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, Pi0X6.galPt σ x ≠ x := by
  rcases hx with h | h | h
  · obtain ⟨-, r, hr, hr2⟩ := charts_at_some hc x h
    exact galPt_ne_of_mem hr (d := -3) (by norm_num) (by rw [hr2]; push_cast; ring)
  · obtain ⟨⟨s, hs, hs2⟩, -⟩ := charts_at_some hc x h
    exact galPt_ne_of_mem hs (d := -1) (by norm_num) (by rw [hs2]; push_cast; ring)
  · obtain ⟨b, hb, hb2⟩ := charts_at_infty hc x h
    exact galPt_ne_of_mem hb (d := -3) (by norm_num) (by rw [hb2]; push_cast; ring)

end Charts

/-! ## 6. "Every" from "one" -/

section Every

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {X : Over (Spec (CommRingCat.of ℚ))}
  {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}

/-- **The core.** Let `S` be a set of `ℚ̄`-points of `X` stable under `Aut(ℚ̄/ℚ)`, whose classes lie in a set of at
most two classes, and `x₀ ∈ S` a point moved by some `σ` at which `t` takes a value `v` fixed by every `σ`. Then
`t = v` on all of `S`. -/
theorem every_of_one_core (t : ToP1 X.left) (S : (fieldPt Qbar ⟶ X) → Prop)
    (hS : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) x, S x → S (Pi0X6.galPt σ x))
    (T : Set (Quotient (pairSetoid Qbar))) [Finite T] (hT : Nat.card T ≤ 2) (hST : ∀ x, S x → Ψ x ∈ T)
    {x₀ : fieldPt Qbar ⟶ X} (h₀ : S x₀) {v : OnePoint Qbar} (hv : t.val (K := Qbar) x₀.left = v)
    (hfix : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, v.map (σ : Qbar →+* Qbar) = v)
    {σ : Qbar ≃ₐ[ℚ] Qbar} (hσ : Pi0X6.galPt σ x₀ ≠ x₀) :
    ∀ x, S x → t.val (K := Qbar) x.left = v := by
  intro x hx
  have hv' : t.val (K := Qbar) (Pi0X6.galPt σ x₀).left = v := by rw [Pi0X6.val_galPt, hv, hfix]
  rcases two_of_three Ψ T hT x x₀ (Pi0X6.galPt σ x₀) (hST x hx) (hST x₀ h₀) (hST _ (hS σ x₀ h₀))
    with h | h | h
  · rw [h, hv]
  · rw [h, hv']
  · exact absurd h.symm hσ

theorem map_zero_fix (σ : Qbar ≃ₐ[ℚ] Qbar) : (OnePoint.some (0 : Qbar)).map (σ : Qbar →+* Qbar) = OnePoint.some 0 := by
  simp [OnePoint.map_some]
theorem map_one_fix (σ : Qbar ≃ₐ[ℚ] Qbar) : (OnePoint.some (1 : Qbar)).map (σ : Qbar →+* Qbar) = OnePoint.some 1 := by
  simp [OnePoint.map_some]
theorem map_infty_fix (σ : Qbar ≃ₐ[ℚ] Qbar) : (OnePoint.infty : OnePoint Qbar).map (σ : Qbar →+* Qbar) = OnePoint.infty := by
  simp [OnePoint.map_infty]

include hU hG hM in
/-- **Step (c) for one discriminant**, in terms of a relation `(p, q)`, its field `k` and a count `≤ 2`. -/
theorem every_of_one_rel (h6 : X6Props Y Φ X Ψ fY) (t : ToP1 X.left) (hc : X6Glue.ElkiesCharts X t)
    {p q : ℤ} {R : Type} [CommRing R]
    (hexact : ∀ Pr : QMPair Qbar, HasRel p q Pr.q → Nonempty (com Pr.q ≃+* R))
    (hcount : Finite {c : Quotient (pairSetoid Qbar) // ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ∧
      Nat.card {c : Quotient (pairSetoid Qbar) // ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ≤ 2)
    {v : OnePoint Qbar} (hv3 : v = OnePoint.some 0 ∨ v = OnePoint.some 1 ∨ v = OnePoint.infty)
    (hone : ∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasRel p q P.q ∧
      t.val (K := Qbar) x.left = v) :
    ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P → HasRel p q P.q →
      t.val (K := Qbar) x.left = v := by
  obtain ⟨hfin, hle⟩ := hcount
  set T : Set (Quotient (pairSetoid Qbar)) :=
    {c | ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} with hTdef
  haveI : Finite T := hfin
  let S : (fieldPt Qbar ⟶ X) → Prop := fun x => ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ HasRel p q P.q
  have hS : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) x, S x → S (Pi0X6.galPt σ x) := by
    rintro σ x ⟨P, hP, hr⟩
    exact hasRel_galPt h6 σ hP hr
  have hST : ∀ x, S x → Ψ x ∈ T := by
    rintro x ⟨P, hP, hr⟩
    exact ⟨P, hP.symm, hexact P hr⟩
  obtain ⟨x₀, P₀, hP₀, hr₀, hv⟩ := hone
  have hfix : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, v.map (σ : Qbar →+* Qbar) = v := by
    intro σ
    rcases hv3 with rfl | rfl | rfl
    · exact map_zero_fix σ
    · exact map_one_fix σ
    · exact map_infty_fix σ
  obtain ⟨σ, hσ⟩ := moved_of_val hc x₀ (by rw [hv]; exact hv3)
  intro x P hP hr
  exact every_of_one_core t S hS T hle hST ⟨P₀, hP₀, hr₀⟩ hv hfix hσ x ⟨P, hP, hr⟩

end Every

/-! ## 7. The new leaf and the discharge -/

section Leaf

open HDec.QMSplit.Moduli X6ALIdeal

/-- **LEAF `ElkiesX6StarOneIdeal`** (Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), arXiv
math/0005160, §3 with `Σ = {2, 3}`: `X*(1) = X(1)/W`, p. 10, `w_p : A ↦ A/ker I_p`; `X*(1) ≅ P¹_t` with the
elliptic points of orders 2, 4, 6 at `t = 0, 1, ∞`, p. 17; the CM points of discriminants `−24, −4, −3` at
`t = 0, 1, ∞`, Table 1 p. 26 and pp. 22–23; function field `ℚ(t)(√(−t), √(3(t − 1)))`, p. 17; locators as read by
the lead from arXiv math/0005160, recorded in x6-coarse §7).

The clauses of `X6ALIdeal.ElkiesX6StarEveryIdeal` (function field `ℚ(X)^W = ℚ(t)` with Elkies' isogeny-form `W`,
the charts `s² = −t`, `r² = 3(t − 1)`, on every witness of the moduli description carrying the printed
Atkin–Lehner automorphisms), with the CM clause in its printed form: **the** CM point of discriminant `−24`
(resp. `−4`, `−3`) of `X*(6)` is at `t = 0` (resp. `1`, `∞`), read in the weakest way: **some** `ℚ̄`-point whose
QM pair has an `𝒪`-endomorphism `φ` with `φ² = −6` (resp. `φ² = −1`, `φ² − φ + 1 = 0`) has that `t`-value.

*Why a consequence of the print, not stronger*: Elkies' CM point of discriminant `D` on `X*(6)` is the image of the
QM surfaces with `End_𝒪(A) ≅ R_D`; any such surface has an endomorphism with the stated relation (the generator of
`R_D`), so the existential follows from the printed value at that point. Unlike `ElkiesX6StarEveryIdeal`, the leaf
does not assert anything at points with `HasCM_D` other than one: the passage to every such point (exactness of
`HasCM_D`, `#CM(R_D) ≤ 2`, Galois conjugacy) is proved glue (`elkiesX6StarEveryIdeal_of_one`). -/
def ElkiesX6StarOneIdeal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY → ALIdealClause X Ψ →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        fixedByWIdeal Ψ =
          (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      ((∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM24 P.q ∧
          t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM4 P.q ∧
          t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM3 P.q ∧
          t.val (K := Qbar) x.left = OnePoint.infty)) ∧
      X6Glue.ElkiesCharts X t

/-- **Step (c) and the `HasCM` step, proved**: the CM clause at every point from the CM clause at one point, on any
witness, from the textbook fields. -/
theorem every_cm_of_one (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}
    (h6 : X6Props Y Φ X Ψ fY) (t : ToP1 X.left) (hc : X6Glue.ElkiesCharts X t)
    (hone : (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM24 P.q ∧
          t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM4 P.q ∧
          t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM3 P.q ∧
          t.val (K := Qbar) x.left = OnePoint.infty)) :
    ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
      (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty) := by
  obtain ⟨⟨x24, P24, h24, c24, v24⟩, ⟨x4, P4, h4, c4, v4⟩, ⟨x3, P3, h3, c3, v3⟩⟩ := hone
  intro x P hP
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact every_of_one_rel hU hG hM h6 t hc (p := 0) (q := 6)
      (fun Pr hr => com_equiv_of_hasCM24 hU hG hM Pr ((hasRel_24 _).2 hr)) (cm_le_two_24 hU hG hM)
      (Or.inl rfl) ⟨x24, P24, h24, (hasRel_24 _).1 c24, v24⟩ x P hP ((hasRel_24 _).1 h)
  · exact every_of_one_rel hU hG hM h6 t hc (p := 0) (q := 1)
      (fun Pr hr => com_equiv_of_hasCM4 hU hG hM Pr ((hasRel_4 _).2 hr)) (cm_le_two_4 hU hG hM)
      (Or.inr (Or.inl rfl)) ⟨x4, P4, h4, (hasRel_4 _).1 c4, v4⟩ x P hP ((hasRel_4 _).1 h)
  · exact every_of_one_rel hU hG hM h6 t hc (p := -1) (q := 1)
      (fun Pr hr => com_equiv_of_hasCM3 hU hG hM Pr ((hasRel_3 _).2 hr)) (cm_le_two_3 hU hG hM)
      (Or.inr (Or.inr rfl)) ⟨x3, P3, h3, (hasRel_3 _).1 c3, v3⟩ x P hP ((hasRel_3 _).1 h)

/-- **x6-coarse's leaf from the new leaf and the three textbook fields.** -/
theorem elkiesX6StarEveryIdeal_of_one (h : ElkiesX6StarOneIdeal)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : ElkiesX6StarEveryIdeal := by
  intro Y Φ X Ψ fY h1 h6 hal
  obtain ⟨t, hff, hone, hc⟩ := h Y Φ X Ψ fY h1 h6 hal
  exact ⟨t, hff, every_cm_of_one hU hG hM h6 t hc hone, hc⟩

/-- **The bundle field `elkiesX6StarEvery` from the new leaf** (with x6-coarse's `elkiesX6StarEvery_of_ideal'`). -/
theorem elkiesX6StarEvery_of_one (h : ElkiesX6StarOneIdeal) (hX : X6CoarseModuliIdeal)
    (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU) (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    ElkiesPrint.ElkiesX6StarEvery :=
  elkiesX6StarEvery_of_ideal' (elkiesX6StarEveryIdeal_of_one h hU hG hM) hX hY hM

/-- **The new leaf is no stronger than the old one, given CM points exist** (`CMExists`, e.g. from González–Rotger's
count): the existential CM clause follows from the universal one. -/
theorem one_of_everyIdeal (h : ElkiesX6StarEveryIdeal)
    (hE : ∀ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)),
      CMExists X Ψ) : ElkiesX6StarOneIdeal := by
  intro Y Φ X Ψ fY h1 h6 hal
  obtain ⟨t, hff, hcm, hc⟩ := h Y Φ X Ψ fY h1 h6 hal
  obtain ⟨⟨x4, P4, h4, c4⟩, ⟨x3, P3, h3, c3⟩, ⟨x24, P24, h24, c24⟩⟩ := hE X Ψ
  exact ⟨t, hff, ⟨⟨x24, P24, h24, c24, (hcm x24 P24 h24).1 c24⟩, ⟨x4, P4, h4, c4, (hcm x4 P4 h4).2.1 c4⟩,
    ⟨x3, P3, h3, c3, (hcm x3 P3 h3).2.2 c3⟩⟩, hc⟩

end Leaf

/-! ## 8. The reviewer's deciding step: `HasCM_D` points are González–Rotger's (Elkies') CM points -/

section Dict

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

include hU hG hM in
/-- **`HasCM24` ⇔ CM by `ℤ[√−6]` exactly** (`End_𝒪(A) ≅ ℤ[√−6]`). -/
theorem hasCM24_iff_com (Pr : QMPair Qbar) : HasCM24 Pr.q ↔ Nonempty (com Pr.q ≃+* R24) :=
  ⟨com_equiv_of_hasCM24 hU hG hM Pr, fun ⟨e⟩ => (hasRel_24 _).2
    (hasRel_of_com_equiv (k := K24) y24_integral (p := 0) (q := 6) (by push_cast; linear_combination y24_mul) e)⟩

include hU hG hM in
/-- **`HasCM4` ⇔ CM by `ℤ[i]` exactly.** -/
theorem hasCM4_iff_com (Pr : QMPair Qbar) : HasCM4 Pr.q ↔ Nonempty (com Pr.q ≃+* Pi0X6.R4) :=
  ⟨com_equiv_of_hasCM4 hU hG hM Pr, fun ⟨e⟩ => (hasRel_4 _).2
    (hasRel_of_com_equiv (k := K4) (IsCyclotomicExtension.zeta_spec 4 ℚ K4).isIntegral (by norm_num)
      (p := 0) (q := 1) (by have := y4_rel; push_cast at this ⊢; linear_combination this) e)⟩

include hU hG hM in
/-- **`HasCM3` ⇔ CM by `ℤ[ζ₃]` exactly.** -/
theorem hasCM3_iff_com (Pr : QMPair Qbar) : HasCM3 Pr.q ↔ Nonempty (com Pr.q ≃+* Pi0X6.R3) :=
  ⟨com_equiv_of_hasCM3 hU hG hM Pr, fun ⟨e⟩ => (hasRel_3 _).2
    (hasRel_of_com_equiv (k := K3) ((IsCyclotomicExtension.zeta_spec 3 ℚ K3).isIntegral (by norm_num)).neg
      (p := -1) (q := 1) (by have := y3_rel; push_cast at this ⊢; linear_combination this) e)⟩

include hU hG hM in
/-- **The `HasCM24` points of a witness are González–Rotger's CM points by `ℤ[√−6]`** (`GRDict.IsGRCMPoint`, the
points `[z] ∈ Γ∖ℍ` fixed by an optimal embedding, through the moduli interpretation). -/
theorem hasCM24_iff_isGRCMPoint {X : Over (Spec (CommRingCat.of ℚ))}
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (x : fieldPt Qbar ⟶ X) :
    (∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ HasCM24 P.q) ↔ GRDict.IsGRCMPoint Ψ R24 x := by
  rw [GRDict.isGRCMPoint_iff hU hG hM finrank_K24 le_rfl (by rw [conductor_max]; norm_num) Ψ x]
  exact exists_congr fun P => and_congr_right fun _ => hasCM24_iff_com hU hG hM P

include hU hG hM in
theorem hasCM4_iff_isGRCMPoint {X : Over (Spec (CommRingCat.of ℚ))}
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (x : fieldPt Qbar ⟶ X) :
    (∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ HasCM4 P.q) ↔ GRDict.IsGRCMPoint Ψ Pi0X6.R4 x := by
  rw [GRDict.isGRCMPoint_iff hU hG hM finrank_K4 le_rfl (by rw [conductor_max]; norm_num) Ψ x]
  exact exists_congr fun P => and_congr_right fun _ => hasCM4_iff_com hU hG hM P

include hU hG hM in
theorem hasCM3_iff_isGRCMPoint {X : Over (Spec (CommRingCat.of ℚ))}
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (x : fieldPt Qbar ⟶ X) :
    (∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ HasCM3 P.q) ↔ GRDict.IsGRCMPoint Ψ Pi0X6.R3 x := by
  rw [GRDict.isGRCMPoint_iff hU hG hM finrank_K3 le_rfl (by rw [conductor_max]; norm_num) Ψ x]
  exact exists_congr fun P => and_congr_right fun _ => hasCM3_iff_com hU hG hM P

end Dict

end ElkiesC
