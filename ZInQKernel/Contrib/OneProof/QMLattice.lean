import ZInQKernel.Contrib.OneProof.H.TailZ26

/-! # gt-qm: `QMCentralizerCMC` and Yu's dichotomy at `(2, −3)` by the complex lattice

Task gt-qm (docs/research/gt-qm.md; gap-triage A5 and A9).

**A5.** The added-bundle field `HDec.QMSplit.Aut.QMCentralizerCMC` (TailU: the centralizer `End_𝒪(A)` of the
QM of an abelian surface over `ℂ` is `ℤ` or `Φ⁻¹(𝒪)` for an imaginary quadratic `k` and `Φ : k → B`) is
proved (`qmCentralizerCMC_of`) from three textbook fields of the bundle (`uniformizationLeafAll`,
`gagaMorphism`, `mumfordTorsionAlgClosed`) and the chain's proved glue (`qmLatticeFree_of`,
`qmSkolemNoetherC_proof`, `qmClassNumberOne_proof`, `unif_ring_hom`, `lift_unique`, `AvSplit.Final.h38/h69`).

**A9.** `YuThm11` (textbook field `yuThm11`) is used by the chain only at `(a, b) = (2, −3)`, for the embedding
of a QM structure by `𝒪`, over `AlgebraicClosure ℚ` or `AlgebraicClosure L'` (`L'` finite over `ℚ`). That
form, `YuB6Alg`, is proved (`yuB6Alg_of'`, from the same three fields; T11(b) is proved in the chain) and is
implied by `YuThm11` (`yuB6Alg_of_yuThm11`). `YuThm11` itself (every algebraically closed `k` of
characteristic `0`, every indefinite division `(a, b)`) is not proved here.

* §1 pure algebra in `B = (2, −3)`: the commutant of `ι(𝒪)` in `End_ℂ(ℂ²)` is `ℂ`; the eigen-subring
  `S_v = {x ∈ B : ι(x)v ∈ ℂv}`; for `v = (τ, 1)ᵀ`, `Im τ ≠ 0`, a nonzero pure quaternion of `S_v` squares to a
  negative rational, and the centralizer of such an element is `ℚ + ℚy₀`.
* §2 `alg_core`: a ring embedded in `B` with image `𝒪 ∩ S_{(τ,1)}` is `ℤ` or `Φ⁻¹(𝒪)` with `k = S_{(τ,1)}`.
* §3 `unif_conj`: `End(A)` is the ring of `ℂ`-linear maps preserving `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, `ι`-compatibly
  (T35 + T11a + `QMLatticeAlgebra`); `com_embed`: `End_𝒪(A) ≅ 𝒪 ∩ S_{(τ,1)}`.
* §4 `qmCentralizerCMC_of`.
* §5 `exists_lift`, `end0_equiv` (`ℚ ⊗_ℤ M ≅ C` for a lattice `M` in a `ℚ`-algebra `C`).
* §6 the `ℂ`-basis `(v, w)`, clearing denominators, and the two cases: `S_{(τ,1)} = ℚ` gives
  `End⁰(A) ≅ B` (`case_triv`), otherwise `End⁰(A) ≅ M₂(ℚ(√d))`, `d = y₀² < 0` (`case_quad`).
* §7 `yu_core` (over `ℂ`), `YuB6Alg`, `YuB6Emb` (fields embeddable in `ℂ`), `yuB6Emb_of`, `yuB6Alg_of`,
  `yuB6Alg_of'`, `yuB6Alg_of_yuThm11`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMLattice

open scoped Quaternion

open HDec.QMSplit.CNO (act act_add act_mul act_one act_smul act_eq_zero act_sub act_zero act_neg
  mem_qmOrbit_iff oBasis_mem)

abbrev B := LeafQM.B

/-! ## §1 Algebra in `B` -/

theorem act_smul_vec (x : B) (c : ℂ) (w : Fin 2 → ℂ) : act x (c • w) = c • act x w := by
  simp [act, Matrix.mulVec_smul]

theorem act_add_vec (x : B) (u u' : Fin 2 → ℂ) : act x (u + u') = act x u + act x u' := by
  simp [act, Matrix.mulVec_add]

theorem act_algebraMap (r : ℚ) (w : Fin 2 → ℂ) : act (algebraMap ℚ B r) w = (r : ℂ) • w := by
  rw [Algebra.algebraMap_eq_smul_one, act_smul, act_one]

theorem act_inj {v : Fin 2 → ℂ} (hv : v ≠ 0) {x y : B} (h : act x v = act y v) : x = y :=
  sub_eq_zero.mp (act_eq_zero hv (by rw [act_sub, h, sub_self]))

/-- The explicit action of a quaternion on `ℂ²`. -/
theorem act_apply0 (x : B) (w : Fin 2 → ℂ) : act x w 0 =
    ((x.re : ℂ) + (x.imI : ℂ) * √2) * w 0 + (-3 * (x.imJ : ℂ) - 3 * √2 * (x.imK : ℂ)) * w 1 := by
  simp [act, FibreQMNorm.qmMatB, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.mul_apply, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
  ring

theorem act_apply1 (x : B) (w : Fin 2 → ℂ) : act x w 1 =
    ((x.imJ : ℂ) - √2 * (x.imK : ℂ)) * w 0 + ((x.re : ℂ) - (x.imI : ℂ) * √2) * w 1 := by
  simp [act, FibreQMNorm.qmMatB, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.mul_apply, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
  ring

/-- **The commutant of `ι(𝒪)` in `End_ℂ(ℂ²)` is `ℂ`** (explicit: commuting with `ι(i) = diag(√2, −√2)`
makes `T` diagonal, commuting with `ι((1+j)/2)` makes the two entries equal). -/
theorem commutant (T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (h : ∀ x ∈ LeafQM.O, ∀ z, T (act x z) = act x (T z)) : ∃ c : ℂ, ∀ z, T z = c • z := by
  have s2 : (√2 : ℂ) ≠ 0 := BPAnalytic.QM.sqrt2_ne_zero
  let e0 : Fin 2 → ℂ := ![1, 0]
  let e1 : Fin 2 → ℂ := ![0, 1]
  have hz : ∀ z : Fin 2 → ℂ, z = z 0 • e0 + z 1 • e1 := by
    intro z; funext i; fin_cases i <;> simp [e0, e1]
  have hi0 : act (BPAnalytic.QM.oBasis 1) e0 = (√2 : ℂ) • e0 := by
    funext i; fin_cases i <;> simp [act_apply0, act_apply1, e0, BPAnalytic.QM.oBasis]
  have hi1 : act (BPAnalytic.QM.oBasis 1) e1 = (-√2 : ℂ) • e1 := by
    funext i; fin_cases i <;> simp [act_apply0, act_apply1, e1, BPAnalytic.QM.oBasis]
  have hj0 : act (BPAnalytic.QM.oBasis 2) e0 = (1 / 2 : ℂ) • (e0 + e1) := by
    funext i; fin_cases i <;> simp [act_apply0, act_apply1, e0, e1, BPAnalytic.QM.oBasis]
  have E1 := congrFun (h _ (oBasis_mem 1) e0) 1
  rw [hi0, map_smul, act_apply1] at E1
  have E2 := congrFun (h _ (oBasis_mem 1) e1) 0
  rw [hi1, map_smul, act_apply0] at E2
  have E3 := congrFun (h _ (oBasis_mem 2) e0) 1
  rw [hj0, map_smul, map_add, act_apply1] at E3
  simp [BPAnalytic.QM.oBasis] at E1 E2 E3
  have r0 : T e0 1 = 0 := by
    have : (2 * √2 : ℂ) * T e0 1 = 0 := by linear_combination E1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero s2)
  have r1 : T e1 0 = 0 := by
    have : (2 * √2 : ℂ) * T e1 0 = 0 := by linear_combination -E2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero s2)
  have r2 : T e1 1 = T e0 0 := by linear_combination 2 * E3
  refine ⟨T e0 0, fun z => ?_⟩
  rw [hz z, map_add, map_smul, map_smul]
  funext i; fin_cases i <;> simp [r0, r1, r2, e0, e1] <;> ring

/-- The eigen-subring `S_v = {x ∈ B : ι(x)v ∈ ℂv}`. -/
def S (v : Fin 2 → ℂ) : Subring B where
  carrier := {x | ∃ c : ℂ, act x v = c • v}
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [act_mul, hd, act_smul_vec, hc, smul_smul]⟩
  one_mem' := ⟨1, by rw [act_one, one_smul]⟩
  add_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [act_add, hc, hd, add_smul]⟩
  zero_mem' := ⟨0, by rw [act_zero, zero_smul]⟩
  neg_mem' := by
    rintro x ⟨c, hc⟩
    exact ⟨-c, by rw [act_neg, hc, neg_smul]⟩

theorem mem_S {v : Fin 2 → ℂ} {x : B} : x ∈ S v ↔ ∃ c : ℂ, act x v = c • v := Iff.rfl

theorem algebraMap_mem_S (v : Fin 2 → ℂ) (r : ℚ) : algebraMap ℚ B r ∈ S v :=
  ⟨r, act_algebraMap r v⟩

theorem S_comm {v : Fin 2 → ℂ} (hv : v ≠ 0) {x y : B} (hx : x ∈ S v) (hy : y ∈ S v) : x * y = y * x := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨d, hd⟩ := hy
  apply act_inj hv
  rw [act_mul, act_mul, hd, hc, act_smul_vec, act_smul_vec, hc, hd, smul_smul, smul_smul, mul_comm]

theorem star_eq (x : B) : star x = algebraMap ℚ B (2 * x.re) - x := by
  ext <;> simp [Algebra.algebraMap_eq_smul_one] <;> ring

theorem star_mem_S {v : Fin 2 → ℂ} {x : B} (hx : x ∈ S v) : star x ∈ S v := by
  rw [star_eq]; exact (S v).sub_mem (algebraMap_mem_S v _) hx

/-- The inverse `x⁻¹ = nrd(x)⁻¹ x̄` stays in `S_v`. -/
theorem inv_mem_S {v : Fin 2 → ℂ} (hv : v ≠ 0) {x : B} (hx : x ∈ S v) (hx0 : x ≠ 0) :
    ∃ y ∈ S v, x * y = 1 := by
  refine ⟨(QMSplit.CNO.nrd x)⁻¹ • star x, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (S v).mul_mem (algebraMap_mem_S v _) (star_mem_S hx)
  · have e := QMSplit.CNO.div_mul_cancel' 1 x hx0
    rw [one_mul] at e
    rw [S_comm hv hx (by rw [Algebra.smul_def]; exact (S v).mul_mem (algebraMap_mem_S v _) (star_mem_S hx))]
    exact e

/-- **A pure quaternion with a real eigenvalue on `(τ, 1)ᵀ`, `Im τ ≠ 0`, is zero** (`ι(y)` is a real
matrix; taking real and imaginary parts of the two rows). -/
theorem pure_zero_of_real {τ : ℂ} (hτ : τ.im ≠ 0) {y : B} (hy : y.re = 0) {c : ℂ} (hc : c.im = 0)
    (h : act y ![τ, 1] = c • ![τ, 1]) : y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [act_apply0] at h0
  rw [act_apply1] at h1
  simp [hy] at h0 h1
  have r0 := congrArg Complex.re h0
  have i0 := congrArg Complex.im h0
  have r1 := congrArg Complex.re h1
  have i1 := congrArg Complex.im h1
  simp [hc] at r0 i0 r1 i1
  have s2 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have e1' : (y.imJ : ℝ) - √2 * y.imK = 0 := i1.resolve_right hτ
  have e0' : (y.imI : ℝ) * √2 = c.re := i0.resolve_right hτ
  have ha : (y.imI : ℝ) * √2 = 0 := by linear_combination (e0' - r1 + e1' * τ.re) / 2
  have hb : (y.imJ : ℝ) + √2 * y.imK = 0 := by linear_combination (r0 - e0' * τ.re) / (-3)
  have hc' : (y.imK : ℝ) * √2 = 0 := by linear_combination (hb - e1') / 2
  have a0 : (y.imI : ℝ) = 0 := (mul_eq_zero.mp ha).resolve_right s2
  have c0 : (y.imK : ℝ) = 0 := (mul_eq_zero.mp hc').resolve_right s2
  have b0 : (y.imJ : ℝ) = 0 := by rw [c0] at e1'; simpa using e1'
  exact ⟨by exact_mod_cast a0, by exact_mod_cast b0, by exact_mod_cast c0⟩

/-- The square of a pure quaternion of `(2, −3)`. -/
def sqForm (y : B) : ℚ := 2 * y.imI ^ 2 - 3 * y.imJ ^ 2 + 6 * y.imK ^ 2

theorem pure_sq {y : B} (hy : y.re = 0) : y * y = algebraMap ℚ B (sqForm y) := by
  ext <;> simp [sqForm, hy, Algebra.algebraMap_eq_smul_one] <;> ring

/-- **A nonzero pure quaternion in `S_{(τ,1)}` squares to a negative rational**: its eigenvalue `c`
satisfies `c² = y²`, and `c` is not real (`pure_zero_of_real`). -/
theorem sqForm_neg {τ : ℂ} (hτ : τ.im ≠ 0) {y : B} (hy : y.re = 0) (hyS : y ∈ S ![τ, 1])
    (hy0 : ¬ (y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0)) : sqForm y < 0 := by
  obtain ⟨c, hc⟩ := hyS
  have hsq : act (y * y) ![τ, 1] = (c * c) • ![τ, 1] := by
    rw [act_mul, hc, act_smul_vec, hc, smul_smul]
  rw [pure_sq hy, act_algebraMap] at hsq
  have h1 := congrFun hsq 1
  simp at h1
  -- h1 : (sqForm y : ℂ) = c * c
  by_contra hn
  push Not at hn
  apply hy0
  refine pure_zero_of_real hτ hy ?_ hc
  have hr := congrArg Complex.re h1
  have hi := congrArg Complex.im h1
  simp at hr hi
  have hn' : (0 : ℝ) ≤ (sqForm y : ℝ) := by exact_mod_cast hn
  by_contra hci
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp (show c.re * c.im = 0 by linarith) with h | h
    · exact h
    · exact absurd h hci
  have : c.im * c.im ≤ 0 := by nlinarith
  exact hci (by nlinarith [mul_self_nonneg c.im])

/-- **The centralizer of a nonzero pure quaternion `y₀` is `ℚ + ℚy₀`** (in `(2, −3)`; the commutator
of pure parts is a twisted cross product). -/
theorem comm_span {y0 y : B} (h0 : y0.re = 0) (hy0 : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0))
    (h : y * y0 = y0 * y) : ∃ α β : ℚ, y = algebraMap ℚ B α + β • y0 := by
  have e1 := congrArg QuaternionAlgebra.imI h
  have e2 := congrArg QuaternionAlgebra.imJ h
  have e3 := congrArg QuaternionAlgebra.imK h
  simp [h0] at e1 e2 e3
  have E1 : y.imJ * y0.imK = y.imK * y0.imJ := by linarith
  have E2 : y.imI * y0.imK = y.imK * y0.imI := by linarith
  have E3 : y.imI * y0.imJ = y.imJ * y0.imI := by linarith
  have key : ∃ β : ℚ, y.imI = β * y0.imI ∧ y.imJ = β * y0.imJ ∧ y.imK = β * y0.imK := by
    by_cases a1 : y0.imI = 0
    · by_cases a2 : y0.imJ = 0
      · have a3 : y0.imK ≠ 0 := fun a3 => hy0 ⟨a1, a2, a3⟩
        rw [a1] at E2; rw [a2] at E1
        refine ⟨y.imK / y0.imK, ?_, ?_, ?_⟩
        · rw [a1, mul_zero]; simpa [a3] using E2
        · rw [a2, mul_zero]; simpa [a3] using E1
        · field_simp
      · rw [a1] at E3
        refine ⟨y.imJ / y0.imJ, ?_, ?_, ?_⟩
        · rw [a1, mul_zero]; simpa [a2] using E3
        · field_simp
        · rw [div_mul_eq_mul_div, eq_div_iff a2]; linarith
    · refine ⟨y.imI / y0.imI, ?_, ?_, ?_⟩
      · field_simp
      · rw [div_mul_eq_mul_div, eq_div_iff a1]; linarith
      · rw [div_mul_eq_mul_div, eq_div_iff a1]; linarith
  obtain ⟨β, b1, b2, b3⟩ := key
  refine ⟨y.re, β, ?_⟩
  ext <;> simp [h0, Algebra.algebraMap_eq_smul_one, b1, b2, b3]

/-! ## §2 The algebraic core: a subring of `B` cut out by `𝒪 ∩ S_{(τ,1)}` -/

theorem int_of_O {x : B} (hx : x ∈ LeafQM.O) (h1 : x.imI = 0) (h2 : x.imJ = 0) (h3 : x.imK = 0) :
    ∃ n : ℤ, x = (n : B) := by
  obtain ⟨n, rfl⟩ := hx
  simp [LeafQM.ofInt] at h1 h2 h3
  simp [h3] at h1
  refine ⟨n 0, ?_⟩
  ext <;> simp [LeafQM.ofInt, h1, h2, h3]

/-- **The algebraic core.** A ring `R` embedded in `B` with image exactly `𝒪 ∩ S_{(τ,1)}` (`Im τ > 0`) is
`ℤ`, or `Φ⁻¹(𝒪)` for the imaginary quadratic field `k = S_{(τ,1)}` and its inclusion `Φ : k → B`. -/
theorem alg_core {R : Type} [Ring R] {τ : ℂ} (hτ : 0 < τ.im) (F : R →+* B) (hF : Function.Injective F)
    (hR : ∀ x, x ∈ Set.range F ↔ (x ∈ LeafQM.O ∧ x ∈ S ![τ, 1])) :
    Nonempty (R ≃+* ℤ) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k), NumberField.IsTotallyComplex k ∧
      Module.finrank ℚ k = 2 ∧
      ∃ Φ : k →ₐ[ℚ] QMSplit.Aut.B, Nonempty (R ≃+* LeafQM.O.comap Φ.toRingHom) := by
  set v : Fin 2 → ℂ := ![τ, 1] with hvdef
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 1
  have hτ' : τ.im ≠ 0 := hτ.ne'
  have hFO : ∀ r, F r ∈ LeafQM.O := fun r => ((hR (F r)).1 ⟨r, rfl⟩).1
  have hFS : ∀ r, F r ∈ S v := fun r => ((hR (F r)).1 ⟨r, rfl⟩).2
  by_cases hall : ∀ x ∈ S v, x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · left
    have hsurj : Function.Surjective (Int.castRingHom R) := by
      intro r
      obtain ⟨h1, h2, h3⟩ := hall _ (hFS r)
      obtain ⟨n, hn⟩ := int_of_O (hFO r) h1 h2 h3
      exact ⟨n, hF (by simp [hn])⟩
    have hinj : Function.Injective (Int.castRingHom R) := by
      rw [injective_iff_map_eq_zero]
      intro n hn
      have h1 := congrArg F hn
      simp at h1
      have h2 := congrArg QuaternionAlgebra.re h1
      simpa using h2
    exact ⟨(RingEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm⟩
  · right
    obtain ⟨x0, hx0S, hx0⟩ : ∃ x ∈ S v, ¬ (x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0) := by
      by_contra hc
      exact hall (fun x hx => by
        by_contra h
        exact hc ⟨x, hx, h⟩)
    set y0 := x0 - algebraMap ℚ B x0.re with hy0def
    have hy0re : y0.re = 0 := by simp [y0, Algebra.algebraMap_eq_smul_one]
    have hy0S : y0 ∈ S v := (S v).sub_mem hx0S (algebraMap_mem_S v _)
    have hy0nz : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0) := by
      simpa [y0, Algebra.algebraMap_eq_smul_one] using hx0
    have hneg := sqForm_neg hτ' hy0re hy0S hy0nz
    have hfield : IsField (S v) :=
      { exists_pair_ne := ⟨0, 1, fun h => by
          have := congrArg (fun z : S v => (z : B).re) h
          simp at this⟩
        mul_comm := fun a b => Subtype.ext (S_comm hv a.2 b.2)
        mul_inv_cancel := fun {a} ha => by
          obtain ⟨y, hy, hxy⟩ := inv_mem_S hv a.2 (fun h => ha (Subtype.ext h))
          exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩ }
    letI : Field (S v) := hfield.toField
    haveI hcz : CharZero (S v) := ⟨fun m n h => by
      have := congrArg (fun z : S v => (z : B).re) h
      simpa using this⟩
    let Φ : S v →ₐ[ℚ] QMSplit.Aut.B := RingHom.toRatAlgHom (S v).subtype
    have hΦ : ∀ x : S v, Φ x = (x : B) := fun x => rfl
    have hΦinj : Function.Injective Φ := fun a b h => Subtype.ext (by rwa [hΦ, hΦ] at h)
    haveI hfd : FiniteDimensional ℚ (S v) := Module.Finite.of_injective Φ.toLinearMap hΦinj
    haveI : NumberField (S v) := ⟨⟩
    have htc : NumberField.IsTotallyComplex (S v) := by
      refine NumberField.isTotallyComplex_of_sq_ratCast_of_neg (x := ⟨y0, hy0S⟩) (r := sqForm y0) ?_ hneg
      apply hΦinj
      rw [map_pow, AlgHom.commutes, hΦ]
      show y0 ^ 2 = _
      rw [pow_two, pure_sq hy0re]
    have hrange : LinearMap.range Φ.toLinearMap = Submodule.span ℚ (Set.range ![(1 : B), y0]) := by
      apply le_antisymm
      · rintro _ ⟨s, rfl⟩
        obtain ⟨α, β, hαβ⟩ := comm_span hy0re hy0nz (S_comm hv s.2 hy0S)
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨![α, β], ?_⟩
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [AlgHom.toLinearMap_apply, hΦ, hαβ, Algebra.algebraMap_eq_smul_one]
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨1, by simp⟩
        · exact ⟨⟨y0, hy0S⟩, rfl⟩
    have hli : LinearIndependent ℚ ![(1 : B), y0] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e0 := congrArg QuaternionAlgebra.re hst
      have e1 := congrArg QuaternionAlgebra.imI hst
      have e2 := congrArg QuaternionAlgebra.imJ hst
      have e3 := congrArg QuaternionAlgebra.imK hst
      simp [hy0re] at e0 e1 e2 e3
      refine ⟨e0, ?_⟩
      by_contra ht
      exact hy0nz ⟨e1.resolve_left ht, e2.resolve_left ht, e3.resolve_left ht⟩
    have hfr : Module.finrank ℚ (S v) = 2 := by
      rw [← LinearMap.finrank_range_of_inj (f := Φ.toLinearMap) hΦinj, hrange, finrank_span_eq_card hli]
      simp
    refine ⟨S v, inferInstance, inferInstance, htc, hfr, Φ, ⟨?_⟩⟩
    let G : R →+* LeafQM.O.comap Φ.toRingHom :=
      (F.codRestrict (S v) hFS).codRestrict _ (fun r => hFO r)
    refine RingEquiv.ofBijective G ⟨fun a b h => hF ?_, fun s => ?_⟩
    · have := congrArg (fun z : LeafQM.O.comap Φ.toRingHom => ((z : S v) : B)) h
      exact this
    · obtain ⟨r, hr⟩ := (hR ((s : S v) : B)).2 ⟨s.2, (s : S v).2⟩
      exact ⟨r, Subtype.ext (Subtype.ext hr)⟩

/-! ## §3 The centralizer through the uniformization `A(ℂ) = ℂ²/ι(𝒪)(τ, 1)ᵀ` -/

open HSyn.G0Split.FibreQM in
/-- **The analytic representation, normalized** (from the same inputs as `com_embed`): a ring embedding
`ρ : End(A) → End_ℂ(ℂ²)` with `ρ(ι(a)) = ι(a)` and image exactly the maps preserving
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`. -/
theorem unif_conj (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : LeafQM.AV.QMStr A) :
    ∃ (τ : ℂ) (_ : 0 < τ.im) (ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ)),
      Function.Injective ρ ∧ (∀ a z, ρ (q.iota a) z = act (a : B) z) ∧
      ∀ N : Module.End ℂ (Fin 2 → ℂ),
        (∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1]) ↔ ∃ e, ρ e = N := by
  have hE : UniformizationExistsT35 := AvSplit.Final.h38 hU hM
  have hR : T11aRiemannEnd := ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hU hG)
  have hL : QMLatticeAlgebra :=
    qmLatticeAlgebra_of_free (qmLatticeFree_of qmSkolemNoetherC_proof QMSplit.CNO.qmClassNumberOne_proof)
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ A (RingHom.id ℂ) 2 hA
  haveI := hd
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR A hA Λ Φu hΦ
  obtain ⟨τ, hτ, Fl, hF, hFρ⟩ := hL Λ hlat (ρ.comp q.iota) (fun a z hz => hpres (q.iota a) z hz)
  have hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ FibreQMNorm.qmOrbit ![τ, 1] := by
    intro z
    rw [← FibreQMNorm.qmLattice_eq_orbit hτ.ne', ← hF]
    constructor
    · intro h; exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      have : w = z := Fl.injective he
      rw [← this]; exact hw
  have hT11 := hR A 2 Λ Φu hA hΦ
  have hρinj : Function.Injective ρ := fun e e' h =>
    (hT11.1 (ρ e) (hpres e)).unique (hρ e) (fun z => by rw [h]; exact hρ e' z)
  have hρsurj : ∀ N : Module.End ℂ (Fin 2 → ℂ), (∀ z ∈ Λ, N z ∈ Λ) → ∃ e, ρ e = N := by
    intro N hN
    obtain ⟨f, hf, -⟩ := hT11.1 N hN
    exact ⟨f, lift_unique hΦ (fun z => by rw [hρ, hf])⟩
  let ρ' : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ) :=
    { toFun := fun e => Fl.toLinearMap ∘ₗ ρ e ∘ₗ Fl.symm.toLinearMap
      map_one' := LinearMap.ext fun z => by simp
      map_mul' := fun e e' => LinearMap.ext fun z => by simp [map_mul]
      map_zero' := LinearMap.ext fun z => by simp
      map_add' := fun e e' => LinearMap.ext fun z => by simp [map_add] }
  have hρ' : ∀ e z, ρ' e z = Fl (ρ e (Fl.symm z)) := fun e z => rfl
  refine ⟨τ, hτ, ρ', fun e e' h => hρinj ?_, fun a z => ?_, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · refine LinearMap.ext fun w => ?_
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => Fl.symm (T (Fl w))) h
    simpa [hρ'] using this
  · rw [hρ']
    have := hFρ a (Fl.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  · obtain ⟨e, he⟩ := hρsurj (Fl.symm.toLinearMap ∘ₗ N ∘ₗ Fl.toLinearMap) (fun z hz => by
      rw [hΛ]
      simpa using hN _ ((hΛ z).1 hz))
    refine ⟨e, LinearMap.ext fun z => ?_⟩
    rw [hρ', he]
    simp
  · rintro ⟨e, rfl⟩ z hz
    rw [hρ']
    rw [← hΛ]
    apply hpres
    rw [hΛ]
    simpa using hz

/-- **`End_𝒪(A)` embeds in `B` with image `𝒪 ∩ S_{(τ,1)}`.** By `unif_conj`, `End(A)` is the ring of
`ℂ`-linear maps preserving `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, `ι`-compatibly. An element `e` of the centralizer acts by a
map commuting with `ι(𝒪)`, hence by a scalar `c(e)` (`commutant`); since `c(e)(τ, 1)ᵀ ∈ Λ_τ`,
`c(e)(τ, 1)ᵀ = ι(x)(τ, 1)ᵀ` for a unique `x ∈ 𝒪`; `e ↦ x` is the embedding. Conversely each such `x` gives
the scalar `c`, which preserves `Λ_τ` and so comes from an endomorphism, central because `ρ` is
injective. -/
theorem com_embed (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : LeafQM.AV.QMStr A) :
    ∃ (τ : ℂ) (_ : 0 < τ.im) (F : LeafQM.AV.com q →+* B), Function.Injective F ∧
      ∀ x : B, x ∈ Set.range F ↔ (x ∈ LeafQM.O ∧ x ∈ S ![τ, 1]) := by
  obtain ⟨τ, hτ, ρ, hρinj, hρι, hρrange⟩ := unif_conj hU hG hM A hA q
  have hv : (![τ, 1] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 1
  -- elements of the centralizer act by scalars
  have hcomm : ∀ e ∈ LeafQM.AV.com q, ∃ c : ℂ, ∀ w, ρ e w = c • w := by
    intro e he
    apply commutant (ρ e)
    intro x hx z
    have hcm : q.iota ⟨x, hx⟩ * e = e * q.iota ⟨x, hx⟩ := by
      rw [LeafQM.AV.com, Subring.mem_centralizer_iff] at he
      exact he _ ⟨⟨x, hx⟩, rfl⟩
    have h1 : act x z = ρ (q.iota ⟨x, hx⟩) z := (hρι ⟨x, hx⟩ z).symm
    have h2 : act x (ρ e z) = ρ (q.iota ⟨x, hx⟩) (ρ e z) := (hρι ⟨x, hx⟩ (ρ e z)).symm
    rw [h1, h2, ← Module.End.mul_apply, ← map_mul, ← hcm, map_mul, Module.End.mul_apply]
  have hcinj : ∀ a b : ℂ, a • (![τ, 1] : Fin 2 → ℂ) = b • ![τ, 1] → a = b :=
    fun a b h => smul_left_injective ℂ hv h
  let c : LeafQM.AV.com q → ℂ := fun e => ρ e ![τ, 1] 1
  have hscal : ∀ e : LeafQM.AV.com q, ∀ w, ρ e w = c e • w := by
    intro e w
    obtain ⟨c0, h0⟩ := hcomm e e.2
    have : c e = c0 := by
      show ρ e ![τ, 1] 1 = c0
      rw [h0]
      simp
    rw [this, h0]
  have c_one : c 1 = 1 := hcinj _ _ (by rw [← hscal, OneMemClass.coe_one, map_one, one_smul]; rfl)
  have c_zero : c 0 = 0 := hcinj _ _ (by rw [← hscal, ZeroMemClass.coe_zero, map_zero, zero_smul]; rfl)
  have c_mul : ∀ e e', c (e * e') = c e * c e' := fun e e' => hcinj _ _ (by
    rw [← hscal, MulMemClass.coe_mul, map_mul, Module.End.mul_apply, hscal e', map_smul, hscal e,
      smul_smul, mul_comm])
  have c_add : ∀ e e', c (e + e') = c e + c e' := fun e e' => hcinj _ _ (by
    rw [← hscal, AddMemClass.coe_add, map_add, LinearMap.add_apply, hscal e, hscal e', add_smul])
  have hvO : ∀ e : LeafQM.AV.com q, ∃ x ∈ LeafQM.O, act x ![τ, 1] = c e • ![τ, 1] := by
    intro e
    have h1 : (![τ, 1] : Fin 2 → ℂ) ∈ FibreQMNorm.qmOrbit ![τ, 1] := by
      rw [mem_qmOrbit_iff]
      exact ⟨1, LeafQM.O.one_mem, (act_one _).symm⟩
    have h2 := (hρrange (ρ e)).2 ⟨e, rfl⟩ _ h1
    rw [hscal, mem_qmOrbit_iff] at h2
    obtain ⟨x, hx, hxe⟩ := h2
    exact ⟨x, hx, hxe.symm⟩
  choose X hXO hX using hvO
  let F : LeafQM.AV.com q →+* B :=
    { toFun := X
      map_one' := act_inj hv (by rw [hX, act_one, c_one, one_smul])
      map_mul' := fun e e' => act_inj hv (by
        rw [hX, act_mul, hX, act_smul_vec, hX, smul_smul, c_mul, mul_comm])
      map_zero' := act_inj hv (by rw [hX, act_zero, c_zero, zero_smul])
      map_add' := fun e e' => act_inj hv (by rw [hX, act_add, hX, hX, c_add, add_smul]) }
  have hFX : ∀ e, F e = X e := fun e => rfl
  refine ⟨τ, hτ, F, fun e e' h => ?_, fun x => ⟨?_, ?_⟩⟩
  · have h1 : c e • (![τ, 1] : Fin 2 → ℂ) = c e' • ![τ, 1] := by
      rw [← hX, ← hX]; exact congrArg (fun y => act y ![τ, 1]) h
    apply Subtype.ext
    apply hρinj
    refine LinearMap.ext fun w => ?_
    rw [hscal e, hscal e', hcinj _ _ h1]
  · rintro ⟨e, rfl⟩
    exact ⟨hXO e, c e, hX e⟩
  · rintro ⟨hxO, c0, hc0⟩
    let N : Module.End ℂ (Fin 2 → ℂ) := c0 • LinearMap.id
    have hN : ∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1] := by
      intro z hz
      rw [mem_qmOrbit_iff] at hz ⊢
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨y * x, LeafQM.O.mul_mem hy hxO, ?_⟩
      show c0 • act y ![τ, 1] = _
      rw [act_mul, hc0, act_smul_vec]
    obtain ⟨e0, he0⟩ := (hρrange N).1 hN
    have he0com : e0 ∈ LeafQM.AV.com q := by
      rw [LeafQM.AV.com, Subring.mem_centralizer_iff]
      rintro _ ⟨a, rfl⟩
      apply hρinj
      rw [map_mul, map_mul, he0]
      refine LinearMap.ext fun w => ?_
      simp [N]
    have hce : c ⟨e0, he0com⟩ = c0 := hcinj _ _ (by rw [← hscal]; show ρ e0 _ = _; rw [he0]; rfl)
    refine ⟨⟨e0, he0com⟩, act_inj hv ?_⟩
    rw [hFX, hX, hce, hc0]

/-! ## §4 `QMCentralizerCMC` -/

/-- **`QMCentralizerCMC` (added-bundle field `qmCentralizerCMC`) from the textbook fields
`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`.** -/
theorem qmCentralizerCMC_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    HDec.QMSplit.Aut.QMCentralizerCMC := by
  intro A hA q
  obtain ⟨τ, hτ, F, hF, hR⟩ := com_embed hU hG hM A hA q
  exact alg_core hτ F hF hR

/-! ## §5 Toward `YuThm11` (gap-triage A9): generic lemmas -/

/-- Lifting a ring hom through an injective ring hom containing its range. -/
theorem exists_lift {X Y Z : Type} [Ring X] [Ring Y] [Ring Z] (g : X →+* Z) (θ : Y →+* Z)
    (hθ : Function.Injective θ) (h : ∀ x, g x ∈ Set.range θ) : ∃ Ψ : X →+* Y, ∀ x, θ (Ψ x) = g x := by
  let e : Y ≃+* θ.range := RingEquiv.ofBijective θ.rangeRestrict
    ⟨fun a b hab => hθ (congrArg Subtype.val hab), θ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (g.codRestrict θ.range (fun x => h x)), fun x => ?_⟩
  have : θ.rangeRestrict (e.symm (g.codRestrict θ.range (fun x => h x) x)) =
      g.codRestrict θ.range (fun x => h x) x := e.apply_symm_apply _
  exact congrArg Subtype.val this

/-- **`ℚ ⊗_ℤ M ≅ C`** for a ring embedding `Ψ : M → C` into a `ℚ`-algebra whose image spans `C` up to
denominators. -/
theorem end0_equiv {M C : Type} [Ring M] [Ring C] [Algebra ℚ C] (Ψ : M →+* C)
    (hinj : Function.Injective Ψ)
    (hspan : ∀ c : C, ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • c ∈ Set.range Ψ) :
    Nonempty (TensorProduct ℤ ℚ M ≃ₐ[ℚ] C) := by
  let f : M →ₗ[ℤ] C := Ψ.toAddMonoidHom.toIntLinearMap
  have hf : ∀ m, f m = Ψ m := fun m => rfl
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f := by
    refine ⟨fun x => ?_, fun c => ?_, fun {x₁ x₂} h => ⟨1, by simpa using hinj h⟩⟩
    · have hx : (x : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero x
      have hxq : ((x : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hx
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ] at hab
        exact smul_right_injective C hxq hab
      · intro c
        refine ⟨(((x : ℤ) : ℚ)⁻¹) • c, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_inv_cancel₀ hxq, one_smul]
    · obtain ⟨n, hn, m, hm⟩ := hspan c
      refine ⟨(m, ⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩), ?_⟩
      show ((n : ℤ)) • c = f m
      rw [hf, hm, ← Int.cast_smul_eq_zsmul ℚ]
      simp
  have hbc : IsBaseChange ℚ f := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mp hloc
  let e := hbc.equiv
  have he : ∀ (s : ℚ) (m : M), e (s ⊗ₜ m) = s • Ψ m := fun s m => hbc.equiv_tmul s m
  refine ⟨AlgEquiv.ofLinearEquiv e ?_ ?_⟩
  · show e (1 ⊗ₜ 1) = 1
    rw [he, map_one, one_smul]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
    | tmul s m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, mul_add]
      | tmul t n =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, he, he, he, map_mul, smul_mul_smul_comm]

/-! ## §6 The lattice algebra of `ℂ²/Λ_τ` -/

/-- `w = ι(i)(τ, 1)ᵀ`. -/
def wvec (τ : ℂ) : Fin 2 → ℂ := act (BPAnalytic.QM.oBasis 1) ![τ, 1]

theorem wvec_eq (τ : ℂ) : wvec τ = ![√2 * τ, -√2] := by
  funext i; fin_cases i <;> simp [wvec, act_apply0, act_apply1, BPAnalytic.QM.oBasis]

theorem vw_li {τ : ℂ} (hτ : τ.im ≠ 0) : LinearIndependent ℂ ![![τ, 1], wvec τ] := by
  have hτ0 : τ ≠ 0 := fun h => hτ (by rw [h, Complex.zero_im])
  have s2 : (√2 : ℂ) ≠ 0 := BPAnalytic.QM.sqrt2_ne_zero
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [wvec_eq] at h0 h1
  have ht : (2 * √2 * τ : ℂ) * t = 0 := by linear_combination h0 - τ * h1
  have ht' : t = 0 := (mul_eq_zero.mp ht).resolve_left (by simp [hτ0, s2])
  refine ⟨?_, ht'⟩
  rw [ht'] at h1; simpa using h1

/-- The `ℂ`-basis `(v, w)` of `ℂ²`. -/
def bvw {τ : ℂ} (hτ : τ.im ≠ 0) : Module.Basis (Fin 2) ℂ (Fin 2 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (vw_li hτ) (by simp)

theorem bvw_zero {τ : ℂ} (hτ : τ.im ≠ 0) : bvw hτ 0 = ![τ, 1] := by
  simp [bvw, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem bvw_one {τ : ℂ} (hτ : τ.im ≠ 0) : bvw hτ 1 = wvec τ := by
  simp [bvw, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem decomp {τ : ℂ} (hτ : τ.im ≠ 0) (u : Fin 2 → ℂ) :
    u = (bvw hτ).repr u 0 • ![τ, 1] + (bvw hτ).repr u 1 • wvec τ := by
  conv_lhs => rw [← (bvw hτ).sum_repr u]
  rw [Fin.sum_univ_two, bvw_zero, bvw_one]

theorem repr_comb {τ : ℂ} (hτ : τ.im ≠ 0) (α β : ℂ) :
    (bvw hτ).repr (α • ![τ, 1] + β • wvec τ) 0 = α ∧ (bvw hτ).repr (α • ![τ, 1] + β • wvec τ) 1 = β := by
  rw [← bvw_zero hτ, ← bvw_one hτ]
  simp [Finsupp.single_apply]

/-- `x ↦ ι(x)v`, `ℚ`-linearly. -/
def actV (v : Fin 2 → ℂ) : B →ₗ[ℚ] (Fin 2 → ℂ) where
  toFun b := act b v
  map_add' a b := act_add a b v
  map_smul' r b := by
    rw [act_smul, RingHom.id_apply, Rat.cast_smul_eq_qsmul]

/-- **If `S_{(τ,1)} = ℚ`, every `ℂ`-linear map preserving `ι(B)(τ, 1)ᵀ` is some `ι(x)`.** With
`N' = N − ι(x)` killing `v` and `N'w = ι(y)v`, `y ≠ 0` would force the `w`-coordinate of `ι(b)v` to be
rational for all `b ∈ B`; that `ℚ`-linear functional has kernel `S_v = ℚ`, so `4 ≤ 1 + 1`. -/
theorem eq_act_of_trivial {τ : ℂ} (hτ : τ.im ≠ 0)
    (hall : ∀ x ∈ S ![τ, 1], x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0)
    (N : Module.End ℂ (Fin 2 → ℂ)) (hN : ∀ x : B, ∃ y : B, N (act x ![τ, 1]) = act y ![τ, 1]) :
    ∃ x : B, ∀ z, N z = act x z := by
  obtain ⟨x, hx⟩ := hN 1
  rw [act_one] at hx
  obtain ⟨y1, hy1⟩ := hN (BPAnalytic.QM.oBasis 1)
  set y := y1 - x * BPAnalytic.QM.oBasis 1 with hydef
  have hNw : N (wvec τ) - act x (wvec τ) = act y ![τ, 1] := by
    rw [hydef, act_sub, act_mul, ← hy1]; rfl
  refine ⟨x, ?_⟩
  by_cases hy : y = 0
  · intro z
    have hw : N (wvec τ) = act x (wvec τ) := by
      rw [hy, act_zero] at hNw; exact sub_eq_zero.mp hNw
    rw [decomp hτ z, map_add, map_smul, map_smul, act_add_vec, act_smul_vec, act_smul_vec, hx, hw]
  · exfalso
    obtain ⟨yi, hyi⟩ : ∃ yi : B, yi * y = 1 :=
      ⟨(QMSplit.CNO.nrd y)⁻¹ • star y, by simpa using QMSplit.CNO.div_mul_cancel' 1 y hy⟩
    let β : B →ₗ[ℚ] ℂ := ((bvw hτ).coord 1).restrictScalars ℚ ∘ₗ actV ![τ, 1]
    have hβ : ∀ b, β b = (bvw hτ).repr (act b ![τ, 1]) 1 := fun b => rfl
    have hβrat : ∀ b, ∃ r : ℚ, β b = r := by
      intro b
      obtain ⟨z, hz⟩ := hN b
      have e1 : N (act b ![τ, 1]) - act x (act b ![τ, 1]) = β b • act y ![τ, 1] := by
        conv_lhs => rw [decomp hτ (act b ![τ, 1])]
        rw [map_add, map_smul, map_smul, act_add_vec, act_smul_vec, act_smul_vec, hx, hβ, ← hNw]
        module
      have e2 : act (yi * (z - x * b)) ![τ, 1] = β b • ![τ, 1] := by
        rw [act_mul, act_sub, act_mul, ← hz, e1, act_smul_vec, ← act_mul, hyi, act_one]
      obtain ⟨h1, h2, h3⟩ := hall _ ⟨β b, e2⟩
      set u := yi * (z - x * b)
      have hu : u = algebraMap ℚ B u.re := by
        ext <;> simp [h1, h2, h3, Algebra.algebraMap_eq_smul_one]
      refine ⟨u.re, ?_⟩
      rw [hu, act_algebraMap] at e2
      have := congrFun e2 1
      simpa using this.symm
    have hker : ∀ b, β b = 0 → b ∈ Submodule.span ℚ {(1 : B)} := by
      intro b hb
      have : act b ![τ, 1] = (bvw hτ).repr (act b ![τ, 1]) 0 • ![τ, 1] := by
        conv_lhs => rw [decomp hτ (act b ![τ, 1])]
        rw [← hβ, hb, zero_smul, add_zero]
      obtain ⟨h1, h2, h3⟩ := hall b ⟨_, this⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨b.re, by ext <;> simp [h1, h2, h3]⟩
    have hr : Module.finrank ℚ (LinearMap.range β) ≤ 1 := by
      have hle : LinearMap.range β ≤ Submodule.span ℚ {(1 : ℂ)} := by
        rintro _ ⟨b, rfl⟩
        obtain ⟨r, hr⟩ := hβrat b
        rw [hr, Submodule.mem_span_singleton]
        exact ⟨r, by simp [Rat.cast_smul_eq_qsmul]⟩
      exact (Submodule.finrank_mono hle).trans ((finrank_span_le_card ({(1 : ℂ)} : Set ℂ)).trans (by simp))
    have hk : Module.finrank ℚ (LinearMap.ker β) ≤ 1 :=
      (Submodule.finrank_mono (fun b hb => hker b hb)).trans ((finrank_span_le_card ({(1 : B)} : Set B)).trans (by simp))
    have := LinearMap.finrank_range_add_finrank_ker β
    rw [QuaternionAlgebra.finrank_eq_four] at this
    omega

/-- `ι` as a ring hom `B → End_ℂ(ℂ²)`. -/
def actHom : B →+* Module.End ℂ (Fin 2 → ℂ) where
  toFun x := Matrix.toLin' (FibreQMNorm.qmMatB x)
  map_one' := by rw [QMSplit.CNO.qmMatB_one, Matrix.toLin'_one]; rfl
  map_mul' x y := by rw [QMSplit.CNO.qmMatB_mul, Matrix.toLin'_mul]; rfl
  map_zero' := by rw [QMSplit.CNO.qmMatB_zero, map_zero]
  map_add' x y := by rw [QMSplit.CNO.qmMatB_add, map_add]

theorem actHom_apply (x : B) (z : Fin 2 → ℂ) : actHom x z = act x z := by
  simp [actHom, act, Matrix.toLin'_apply]

theorem actHom_inj : Function.Injective actHom := fun x y h =>
  act_inj (v := ![1, 0]) (fun h0 => by simpa using congrFun h0 0)
    (by rw [← actHom_apply, ← actHom_apply, h])

theorem actHom_smul (r : ℚ) (x : B) : actHom (r • x) = ((r : ℂ)) • actHom x :=
  LinearMap.ext fun z => by rw [actHom_apply, act_smul, LinearMap.smul_apply, actHom_apply]

/-- A map preserving `Λ_τ` preserves `ι(B)(τ, 1)ᵀ`. -/
theorem presB_of_lattice {τ : ℂ} {N : Module.End ℂ (Fin 2 → ℂ)}
    (hN : ∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1]) :
    ∀ x : B, ∃ y : B, N (act x ![τ, 1]) = act y ![τ, 1] := by
  intro x
  obtain ⟨d, hd, hdx⟩ := QMSplit.Aut.O_spans (x := x)
  have h1 : act ((d : ℚ) • x) ![τ, 1] ∈ FibreQMNorm.qmOrbit ![τ, 1] :=
    (mem_qmOrbit_iff _ _).2 ⟨_, hdx, rfl⟩
  obtain ⟨o, ho, hoe⟩ := (mem_qmOrbit_iff _ _).1 (hN _ h1)
  refine ⟨((d : ℚ)⁻¹) • o, ?_⟩
  rw [act_smul, map_smul] at hoe
  have hdC : (((d : ℚ)) : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [act_smul, ← hoe, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by exact_mod_cast hd), one_smul]

/-- **Clearing denominators**: a map preserving `ι(B)(τ, 1)ᵀ` has a positive multiple preserving
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`. -/
theorem denom {τ : ℂ} {N : Module.End ℂ (Fin 2 → ℂ)}
    (hN : ∀ x : B, ∃ y : B, N (act x ![τ, 1]) = act y ![τ, 1]) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1],
      ((n : ℂ) • N) z ∈ FibreQMNorm.qmOrbit ![τ, 1] := by
  choose y hy using fun k : Fin 4 => hN (BPAnalytic.QM.oBasis k)
  choose d hd hdy using fun k : Fin 4 => QMSplit.Aut.O_spans (x := y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr (fun k _ => hd k), ?_⟩
  have hgen : ∀ k, ((∏ k, d k : ℕ) : ℂ) • N (act (BPAnalytic.QM.oBasis k) ![τ, 1]) ∈
      FibreQMNorm.qmOrbit ![τ, 1] := by
    intro k
    obtain ⟨m, hm⟩ : d k ∣ ∏ j, d j := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    rw [hy k, hm]
    apply (mem_qmOrbit_iff _ _).2
    refine ⟨((m : ℤ) : B) * ((d k : ℚ) • y k), LeafQM.O.mul_mem (intCast_mem LeafQM.O m) (hdy k), ?_⟩
    rw [act_mul, act_smul]
    have : act ((m : ℤ) : B) (((d k : ℚ) : ℂ) • act (y k) ![τ, 1]) =
        ((m : ℂ)) • (((d k : ℚ) : ℂ) • act (y k) ![τ, 1]) := by
      rw [show ((m : ℤ) : B) = algebraMap ℚ B (m : ℚ) by simp, act_algebraMap]
      push_cast; rfl
    rw [this, smul_smul]
    push_cast
    ring_nf
  intro z hz
  unfold FibreQMNorm.qmOrbit at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hgen k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx

/-- **Case `S_{(τ,1)} = ℚ`: `ℚ ⊗ End ≅ B`.** -/
theorem case_triv {τ : ℂ} (hτ : 0 < τ.im) {M : Type} [Ring M] (g0 : M →+* Module.End ℂ (Fin 2 → ℂ))
    (hg0 : Function.Injective g0)
    (hrange : ∀ N : Module.End ℂ (Fin 2 → ℂ),
      (∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1]) ↔ ∃ m, g0 m = N)
    (hall : ∀ x ∈ S ![τ, 1], x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0) :
    Nonempty (TensorProduct ℤ ℚ M ≃ₐ[ℚ] B) := by
  have hτ' : τ.im ≠ 0 := hτ.ne'
  obtain ⟨Ψ, hΨ⟩ := exists_lift g0 actHom actHom_inj (fun m => by
    obtain ⟨x, hx⟩ := eq_act_of_trivial hτ' hall (g0 m)
      (presB_of_lattice ((hrange (g0 m)).2 ⟨m, rfl⟩))
    exact ⟨x, LinearMap.ext fun z => by rw [actHom_apply, hx]⟩)
  refine end0_equiv Ψ (fun a b h => hg0 (by rw [← hΨ, ← hΨ, h])) (fun b => ?_)
  obtain ⟨n, hn, hnb⟩ := denom (N := actHom b) (fun x => ⟨b * x, by rw [actHom_apply, act_mul]⟩)
  obtain ⟨m, hm⟩ := (hrange _).1 hnb
  refine ⟨n, hn, m, actHom_inj ?_⟩
  rw [hΨ, hm, actHom_smul]
  push_cast; rfl

/-- **Case `S_{(τ,1)} ≠ ℚ`: `ℚ ⊗ End ≅ M₂(ℚ(√d))`, `d = y₀² < 0`.** `θ : ℚ(√d) → ℂ` sends `√d` to the
eigenvalue `c₀` of `y₀`; `ι(B)(τ, 1)ᵀ = θ(k)v ⊕ θ(k)w` (dimension count), so in the basis `(v, w)` the maps
preserving `ι(B)(τ, 1)ᵀ` are exactly the matrices over `θ(k)`. -/
theorem case_quad {τ : ℂ} (hτ : 0 < τ.im) {M : Type} [Ring M] (g0 : M →+* Module.End ℂ (Fin 2 → ℂ))
    (hg0 : Function.Injective g0)
    (hrange : ∀ N : Module.End ℂ (Fin 2 → ℂ),
      (∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1]) ↔ ∃ m, g0 m = N)
    {y0 : B} (hy0re : y0.re = 0) (hy0S : y0 ∈ S ![τ, 1])
    (hy0nz : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0)) :
    Nonempty (TensorProduct ℤ ℚ M ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (sqForm y0)))) := by
  have hτ' : τ.im ≠ 0 := hτ.ne'
  have hv : (![τ, 1] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 1
  have hdneg : sqForm y0 < 0 := sqForm_neg hτ' hy0re hy0S hy0nz
  obtain ⟨c0, hc0⟩ := hy0S
  have hc0sq : c0 ^ 2 = ((sqForm y0 : ℚ) : ℂ) := by
    have hsq : act (y0 * y0) ![τ, 1] = (c0 * c0) • ![τ, 1] := by
      rw [act_mul, hc0, act_smul_vec, hc0, smul_smul]
    rw [pure_sq hy0re, act_algebraMap] at hsq
    have h1 := congrFun hsq 1
    simp at h1
    rw [pow_two, ← h1]
  set f : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (sqForm y0) with hf
  have hf0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) _
  have hfdeg : f.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  let θ : AdjoinRoot f →ₐ[ℚ] ℂ :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId ℚ ℂ) c0 (by simp [f, hc0sq])
  have hθmk : ∀ p, θ (AdjoinRoot.mk f p) = Polynomial.aeval c0 p := fun p => by
    simp [θ, Polynomial.aeval_def]
  have hθinj : Function.Injective θ := by
    haveI : Fact (Irreducible f) := ⟨Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hfdeg]; decide) (fun x hx => by
        simp [f] at hx
        nlinarith [sq_nonneg x])⟩
    exact θ.toRingHom.injective
  have act_pow : ∀ i : ℕ, act (y0 ^ i) ![τ, 1] = c0 ^ i • ![τ, 1] := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, one_smul, act_one]
    | succ i ih => rw [pow_succ, act_mul, hc0, act_smul_vec, ih, smul_smul, pow_succ, mul_comm]
  have act_aeval : ∀ p : Polynomial ℚ,
      act (Polynomial.aeval y0 p) ![τ, 1] = Polynomial.aeval c0 p • ![τ, 1] := by
    intro p
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
    change actV ![τ, 1] _ = _
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change p.coeff i • act (y0 ^ i) ![τ, 1] = _
    rw [act_pow, smul_assoc]
  have hP3a : ∀ a : AdjoinRoot f, ∃ x : B, act x ![τ, 1] = θ a • ![τ, 1] := by
    intro a
    induction a using AdjoinRoot.induction_on with
    | ih p => exact ⟨Polynomial.aeval y0 p, by rw [act_aeval, hθmk]⟩
  have hP3 : ∀ a a' : AdjoinRoot f, ∃ x : B, θ a • ![τ, 1] + θ a' • wvec τ = act x ![τ, 1] := by
    intro a a'
    obtain ⟨x1, h1⟩ := hP3a a
    obtain ⟨x2, h2⟩ := hP3a a'
    refine ⟨x1 + BPAnalytic.QM.oBasis 1 * x2, ?_⟩
    rw [act_add, act_mul, h2, act_smul_vec, h1]
    rfl
  haveI : Module.Finite ℚ (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hfrAR : Module.finrank ℚ (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
  let L : (AdjoinRoot f × AdjoinRoot f) →ₗ[ℚ] (Fin 2 → ℂ) :=
    (θ.toLinearMap.smulRight ![τ, 1]).coprod (θ.toLinearMap.smulRight (wvec τ))
  have hL : ∀ a a', L (a, a') = θ a • ![τ, 1] + θ a' • wvec τ := fun a a' => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, a'⟩ hab
    rw [hL] at hab
    have := LinearIndependent.pair_iff.mp (vw_li hτ') (θ a) (θ a') hab
    simp only [Prod.mk_eq_zero]
    exact ⟨hθinj (by rw [this.1, map_zero]), hθinj (by rw [this.2, map_zero])⟩
  have hactinj : Function.Injective (actV ![τ, 1]) := fun x y h => act_inj hv h
  have hrangeEq : LinearMap.range L = LinearMap.range (actV ![τ, 1]) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨⟨a, a'⟩, rfl⟩
      obtain ⟨x, hx⟩ := hP3 a a'
      exact ⟨x, by rw [hL, hx]; rfl⟩
    · rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hactinj,
        Module.finrank_prod, hfrAR, QuaternionAlgebra.finrank_eq_four]
  have hVB : ∀ x : B, ∃ a a' : AdjoinRoot f, act x ![τ, 1] = θ a • ![τ, 1] + θ a' • wvec τ := by
    intro x
    have : act x ![τ, 1] ∈ LinearMap.range L := by rw [hrangeEq]; exact ⟨x, rfl⟩
    obtain ⟨⟨a, a'⟩, hab⟩ := this
    exact ⟨a, a', by rw [← hL, hab]⟩
  let TM := LinearMap.toMatrixAlgEquiv (bvw hτ')
  let θM : Matrix (Fin 2) (Fin 2) (AdjoinRoot f) →+* Matrix (Fin 2) (Fin 2) ℂ :=
    θ.toRingHom.mapMatrix
  have hθM : ∀ (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot f)) i j, θM X i j = θ (X i j) := fun X i j => rfl
  have hθMinj : Function.Injective θM := fun X Y h => Matrix.ext fun i j => hθinj (by
    rw [← hθM, ← hθM, h])
  have hcoord : ∀ x : B, ∀ i, ∃ r : AdjoinRoot f, θ r = (bvw hτ').repr (act x ![τ, 1]) i := by
    intro x i
    obtain ⟨a, a', h⟩ := hVB x
    have := repr_comb hτ' (θ a) (θ a')
    fin_cases i
    · exact ⟨a, by rw [h]; exact this.1.symm⟩
    · exact ⟨a', by rw [h]; exact this.2.symm⟩
  have hbj : ∀ j : Fin 2, ∃ x : B, bvw hτ' j = act x ![τ, 1] := by
    intro j
    fin_cases j
    · exact ⟨1, by rw [act_one]; exact bvw_zero hτ'⟩
    · exact ⟨BPAnalytic.QM.oBasis 1, bvw_one hτ'⟩
  obtain ⟨Ψ, hΨ⟩ := exists_lift (TM.toRingEquiv.toRingHom.comp g0) θM hθMinj (fun m => by
    have hpres := presB_of_lattice ((hrange (g0 m)).2 ⟨m, rfl⟩)
    have : ∀ i j, ∃ r, θ r = TM (g0 m) i j := by
      intro i j
      obtain ⟨x, hx⟩ := hbj j
      obtain ⟨y, hy⟩ := hpres x
      obtain ⟨r, hr⟩ := hcoord y i
      refine ⟨r, ?_⟩
      rw [hr]
      show _ = (LinearMap.toMatrixAlgEquiv (bvw hτ')) (g0 m) i j
      rw [LinearMap.toMatrixAlgEquiv_apply, hx, hy]
    choose R hR using this
    exact ⟨Matrix.of R, Matrix.ext fun i j => by rw [hθM]; exact hR i j⟩)
  refine end0_equiv Ψ (fun a a' h => hg0 (TM.injective ?_)) (fun Nm => ?_)
  · have h1 := hΨ a
    have h2 := hΨ a'
    rw [h] at h1
    exact h1.symm.trans h2
  · let Ml := TM.symm (θM Nm)
    have hMl : ∀ i j, (bvw hτ').repr (Ml (bvw hτ' j)) i = θ (Nm i j) := by
      intro i j
      rw [← LinearMap.toMatrixAlgEquiv_apply]
      show TM Ml i j = _
      rw [TM.apply_symm_apply, hθM]
    have hMlb : ∀ j, Ml (bvw hτ' j) = θ (Nm 0 j) • ![τ, 1] + θ (Nm 1 j) • wvec τ := by
      intro j
      rw [decomp hτ' (Ml (bvw hτ' j)), hMl, hMl]
    have e0 : Ml ![τ, 1] = θ (Nm 0 0) • ![τ, 1] + θ (Nm 1 0) • wvec τ := by
      rw [← hMlb 0, bvw_zero hτ']
    have e1 : Ml (wvec τ) = θ (Nm 0 1) • ![τ, 1] + θ (Nm 1 1) • wvec τ := by
      rw [← hMlb 1, bvw_one hτ']
    have hpres : ∀ x : B, ∃ y : B, Ml (act x ![τ, 1]) = act y ![τ, 1] := by
      intro x
      obtain ⟨a, a', h⟩ := hVB x
      obtain ⟨y, hy⟩ := hP3 (a * Nm 0 0 + a' * Nm 0 1) (a * Nm 1 0 + a' * Nm 1 1)
      refine ⟨y, ?_⟩
      rw [h, ← hy, map_add, map_smul, map_smul, e0, e1]
      simp only [map_add, map_mul]
      module
    obtain ⟨n, hn, hnM⟩ := denom hpres
    obtain ⟨m, hm⟩ := (hrange _).1 hnM
    refine ⟨n, hn, m, hθMinj ?_⟩
    rw [hΨ]
    show TM (g0 m) = θM ((n : ℚ) • Nm)
    rw [hm, map_smul, TM.apply_symm_apply]
    ext i j
    rw [hθM, Matrix.smul_apply, Matrix.smul_apply, hθM, map_smul]
    simp [Rat.smul_def]

/-! ## §7 Yu's dichotomy at `B = (2, −3)` for QM by `𝒪` -/

/-- **The dichotomy over `ℂ`** (for any ring `M` with a bijection onto `End(A)`). -/
theorem yu_core (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : LeafQM.AV.QMStr A)
    {M : Type} [Ring M] (j : M →+* PkgI3.AbVar.End A) (hj : Function.Bijective j) :
    Nonempty (TensorProduct ℤ ℚ M ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) ∨
      ∃ d : ℚ, d < 0 ∧ Nonempty (TensorProduct ℤ ℚ M ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) := by
  obtain ⟨τ, hτ, ρ, hρinj, -, hρrange⟩ := unif_conj hU hG hM A hA q
  have hg0 : Function.Injective (ρ.comp j) := hρinj.comp hj.1
  have hrange : ∀ N : Module.End ℂ (Fin 2 → ℂ),
      (∀ z ∈ FibreQMNorm.qmOrbit ![τ, 1], N z ∈ FibreQMNorm.qmOrbit ![τ, 1]) ↔
        ∃ m, (ρ.comp j) m = N := by
    intro N
    rw [hρrange N]
    constructor
    · rintro ⟨e, he⟩
      obtain ⟨m, hm⟩ := hj.2 e
      exact ⟨m, by rw [RingHom.comp_apply, hm, he]⟩
    · rintro ⟨m, hm⟩
      exact ⟨j m, hm⟩
  by_cases hall : ∀ x ∈ S ![τ, 1], x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · exact Or.inl (case_triv hτ (ρ.comp j) hg0 hrange hall)
  · right
    obtain ⟨x0, hx0S, hx0⟩ : ∃ x ∈ S ![τ, 1], ¬ (x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0) := by
      by_contra hc
      exact hall (fun x hx => by
        by_contra h
        exact hc ⟨x, hx, h⟩)
    set y0 := x0 - algebraMap ℚ B x0.re with hy0def
    have hy0re : y0.re = 0 := by simp [y0, Algebra.algebraMap_eq_smul_one]
    have hy0S : y0 ∈ S ![τ, 1] := (S _).sub_mem hx0S (algebraMap_mem_S _ _)
    have hy0nz : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0) := by
      simpa [y0, Algebra.algebraMap_eq_smul_one] using hx0
    exact ⟨sqForm y0, sqForm_neg hτ.ne' hy0re hy0S hy0nz,
      case_quad hτ (ρ.comp j) hg0 hrange hy0re hy0S hy0nz⟩

-- `YuB6Alg` is declared in `ZInQKernel/Contrib/OneProof/H/TailA.lean` (moved there by yu-prune, unchanged, so that
-- the chain's four consumers of Yu's theorem can take it as their hypothesis).

/-- **Yu's dichotomy at `B = (2, −3)` for QM by `𝒪`, over every algebraically closed field of characteristic
`0` that embeds in `ℂ`** (e.g. `ℂ`, `ℚ̄`, any such field of cardinality at most the continuum). -/
def YuB6Emb : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k], Nonempty (k →+* ℂ) → ∀ (A : PkgI3.AbVar k),
    A.dim = 2 → ∀ q : LeafQM.AV.QMStr A,
      Nonempty (PkgI3.AbVar.End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) ∨
        ∃ d : ℚ, d < 0 ∧ Nonempty (PkgI3.AbVar.End0 A ≃ₐ[ℚ]
          Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- **`YuB6Emb` proved** from the textbook fields `uniformizationLeafAll`, `gagaMorphism`,
`mumfordTorsionAlgClosed` and T11(b) (`T11b_Rigidity`): transport to `ℂ` along the embedding and T11(b)
(`End(A) = End(A_ℂ)`), then `yu_core`. -/
theorem yuB6Emb_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hR : ZInQ.LeafPush2.T11b_Rigidity) : YuB6Emb := by
  intro k _ _ _ hσ A hA q
  obtain ⟨σ⟩ := hσ
  letI : Algebra k ℂ := σ.toAlgebra
  let e := HDec.G0ModField.KernelField.endBC A ℂ
  have he : Function.Bijective e := by
    refine ⟨HDec.G0ModField.KernelField.endBC_injective A ℂ, fun g => ?_⟩
    obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := hR k ℂ A A g.hom inferInstance
    exact ⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.ext' hφe⟩
  let qC : LeafQM.AV.QMStr (A.baseChange ℂ) := ⟨e.comp q.iota, he.1.comp q.injective⟩
  have hdim : (A.baseChange ℂ).dim = 2 := by rw [PkgI3.AbVar.dim_baseChange]; exact hA
  exact yu_core hU hG hM (A.baseChange ℂ) hdim qC e he

/-- **`YuB6Alg` proved**: a field algebraic over `ℚ` embeds in `ℂ` (`IsAlgClosed.lift`). -/
theorem yuB6Alg_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hR : ZInQ.LeafPush2.T11b_Rigidity) : YuB6Alg := by
  intro k _ _ _ _ A hA q
  exact yuB6Emb_of hU hG hM hR k ⟨(IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom⟩ A hA q

/-- **`YuB6Alg` is a consequence of the bundle's `YuThm11`** (so it is never stronger than the published
statement): take `(a, b) = (2, −3)` and the embedding `B → End⁰(A)` of the QM structure; drop the splitting
clause. -/
theorem yuB6Alg_of_yuThm11 (h : QMSplit.Yu.YuThm11) : YuB6Alg := by
  intro k _ _ _ _ A hA q
  rcases h k A hA 2 (-3) PkgI3.quatIndefinite_two_neg_three G0FibreSimple.B6_isUnit
      (G0FibreSimple.qm_embeds_end0 q) with h1 | ⟨d, hd, h2, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨d, hd, h2⟩

/-- For the consumer `LTGoodRed.QM.qmEndRank_of` (`k = AlgebraicClosure L'`, `L'` finite over `ℚ`). -/
theorem isAlgebraic_algebraicClosure (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L] :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)

/-- **`YuB6Alg` from the three textbook fields alone**: T11(b) is proved in the chain
(`AVB2.t11b_of_exists` with the cloud worker's `HSyn.t11bExists_lf8`). -/
theorem yuB6Alg_of' (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : YuB6Alg :=
  yuB6Alg_of hU hG hM (AVB2.t11b_of_exists HSyn.t11bExists_lf8)

/-- `YuB6Emb` from the three textbook fields alone (T11(b) proved in the chain). -/
theorem yuB6Emb_of' (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : YuB6Emb :=
  yuB6Emb_of hU hG hM (AVB2.t11b_of_exists HSyn.t11bExists_lf8)

/-- `YuB6Emb` is a consequence of `YuThm11`. -/
theorem yuB6Emb_of_yuThm11 (h : QMSplit.Yu.YuThm11) : YuB6Emb := by
  intro k _ _ _ _ A hA q
  rcases h k A hA 2 (-3) PkgI3.quatIndefinite_two_neg_three G0FibreSimple.B6_isUnit
      (G0FibreSimple.qm_embeds_end0 q) with h1 | ⟨d, hd, h2, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨d, hd, h2⟩

end HDec.QMLattice

