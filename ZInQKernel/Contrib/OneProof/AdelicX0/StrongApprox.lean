import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import ZInQKernel.Contrib.TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# h33-g5: strong approximation for `GL₂` and the adelic modular curve `X_{U₀(N)}(ℂ)`

Task h33-g5 (2026-11-17). Report: `docs/research/h33-g5.md`; scratch and log: `scratch/h33-g5/`.

Tian–Yuan–Zhang (arXiv:1411.4728v1, §3.1, Period7.tex L1179–1181, L1236–1240, L1518–1520) work with
the adelic modular curves `X_U` and their complex uniformization
`X_U(ℂ) ⊇ GL₂(ℚ)₊ \ ℍ × GL₂(𝔸_f)/U` (cusps omitted), with the level
`U₀(N) = {g ∈ GL₂(ℤ̂) : N ∣ c}`. This file proves, from Mathlib and the vendored Tau Ceti library:

* `det_U0` : `det U₀(N) = ℤ̂ˣ`;
* `sl2_reduction_surjective` : `SL₂(ℤ) → SL₂(ℤ/N)` is onto (Tau Ceti);
* `strong_approx` : **`GL₂(𝔸_f) = GL₂(ℚ)⁺ · U₀(N)`** (strong approximation for `GL₂` in the form needed);
* `Sh U` : the double coset space `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U)`, as a quotient type, with
  `toSh U τ = [τ, 1]`;
* `toSh_eq_toSh_iff`, `toSh_surjective`, `gamma0Orbits_equiv` : `τ ↦ [τ, 1]` induces a bijection
  `Γ₀(N) \ ℍ ≃ GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(N))`.

Here `𝔸_f = FiniteAdeleRing ℤ ℚ` (Mathlib) and `ℤ̂ = integralAdeles ℤ ℚ` (Tau Ceti).

The proof of `strong_approx`:
1. clear denominators: `A = M g` and `B = M' g⁻¹` are integral, `A B = D` (Tau Ceti
   `mul_nonZeroDivisor_mem_integralAdeles`);
2. approximate `A ≡ m (mod D)` by an integer matrix (`ℤ` is dense in `ℤ̂`, Tau Ceti
   `closure_range_algebraMap`);
3. a basis `γ` of the lattice `m ℤ² + D ℤ²` (`Submodule.basisOfPid`) gives `γ⁻¹ A ∈ GL₂(ℤ̂)`;
4. for `k ∈ GL₂(ℤ̂)`, lift `k diag(1, det k⁻¹) mod N` to `σ ∈ SL₂(ℤ)` (Tau Ceti) to get
   `σ⁻¹ k ∈ U₀(N)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open IsDedekindDomain Matrix

namespace ZInQ.AdelicX0

/-- The finite adeles of `ℚ`. -/
abbrev Af := FiniteAdeleRing ℤ ℚ

/-- `ℤ̂ ⊂ 𝔸_f`, the integral finite adeles. -/
abbrev Zhat : Subalgebra ℤ Af := FiniteAdeleRing.integralAdeles ℤ ℚ

/-- `2 × 2` matrices. -/
abbrev M2 (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-! ## §1. `ℤ̂` -/

theorem intCast_mem (z : ℤ) : (z : Af) ∈ Zhat := Zhat.intCast_mem z

theorem algebraMap_int (z : ℤ) : algebraMap ℚ Af (z : ℚ) = (z : Af) := map_intCast _ z

/-- `ℚ ∩ ℤ̂ = ℤ`. -/
theorem exists_int_of_mem {r : ℚ} (h : algebraMap ℚ Af r ∈ Zhat) : ∃ z : ℤ, r = z := by
  obtain ⟨z, hz⟩ := (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff r).mp h
  exact ⟨z, by rw [← hz]; rfl⟩

theorem algebraMap_inv_mul (N : ℤ) (hN : N ≠ 0) : algebraMap ℚ Af ((N : ℚ)⁻¹) * (N : Af) = 1 := by
  rw [← algebraMap_int, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hN), map_one]

/-- `x ∈ N ℤ̂`. -/
def DvdZ (N : ℤ) (x : Af) : Prop := ∃ c ∈ Zhat, x = N * c

/-- An integer divisible by `N` in `ℤ̂` is divisible by `N` in `ℤ`. -/
theorem int_dvd_of_dvdZ {N z : ℤ} (hN : N ≠ 0) (h : DvdZ N (z : Af)) : N ∣ z := by
  obtain ⟨c, hc, hzc⟩ := h
  have hr : algebraMap ℚ Af ((z : ℚ) / N) ∈ Zhat := by
    have : algebraMap ℚ Af ((z : ℚ) / N) = c := by
      rw [div_eq_mul_inv, map_mul, algebraMap_int, hzc, mul_comm (N : Af) c, mul_assoc,
        mul_comm (N : Af), algebraMap_inv_mul N hN, mul_one]
    rw [this]; exact hc
  obtain ⟨w, hw⟩ := exists_int_of_mem hr
  refine ⟨w, ?_⟩
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have : (z : ℚ) = N * w := by rw [← hw]; field_simp
  exact_mod_cast this

/-- **`ℤ` is dense in `ℤ̂`, modulo `N`**: every `a ∈ ℤ̂` is congruent to an integer mod `N ℤ̂`. -/
theorem exists_int_sub_dvdZ (N : ℤ) (hN : N ≠ 0) {a : Af} (ha : a ∈ Zhat) :
    ∃ r : ℤ, DvdZ N (a - r) := by
  set c := algebraMap ℚ Af ((N : ℚ)⁻¹)
  set U : Set Af := (fun y => c * (y - a)) ⁻¹' (Zhat : Set Af)
  have hUo : IsOpen U := (FiniteAdeleRing.isOpen_integralAdeles ℤ ℚ).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))
  have haU : a ∈ U := by
    show c * (a - a) ∈ Zhat
    rw [sub_self, mul_zero]; exact Zhat.zero_mem
  have hcl : a ∈ closure (Set.range (algebraMap ℤ Af)) := by
    rw [FiniteAdeleRing.closure_range_algebraMap ℤ ℚ]; exact ha
  obtain ⟨y, hyU, r, rfl⟩ := mem_closure_iff_nhds.mp hcl U (hUo.mem_nhds haU)
  refine ⟨r, -(c * (algebraMap ℤ Af r - a)), neg_mem hyU, ?_⟩
  have : algebraMap ℤ Af r = (r : Af) := map_intCast _ r
  rw [this] at hyU ⊢
  have h1 : (N : Af) * c = 1 := by rw [mul_comm]; exact algebraMap_inv_mul N hN
  linear_combination (r - a) * h1

/-! ## §2. Integral matrices -/

/-- All entries in `ℤ̂`. -/
def IsZ (A : M2 Af) : Prop := ∀ i j, A i j ∈ Zhat

theorem IsZ.add {A B : M2 Af} (hA : IsZ A) (hB : IsZ B) : IsZ (A + B) := fun i j =>
  add_mem (hA i j) (hB i j)

theorem IsZ.sub {A B : M2 Af} (hA : IsZ A) (hB : IsZ B) : IsZ (A - B) := fun i j =>
  sub_mem (hA i j) (hB i j)

theorem IsZ.mul {A B : M2 Af} (hA : IsZ A) (hB : IsZ B) : IsZ (A * B) := fun i j => by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

theorem IsZ.smul_int {A : M2 Af} (hA : IsZ A) (z : ℤ) : IsZ ((z : Af) • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (intCast_mem z) (hA i j)

theorem isZ_one : IsZ (1 : M2 Af) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact Zhat.one_mem
  · exact Zhat.zero_mem

/-- An integer matrix in `𝔸_f`. -/
def toAf (m : M2 ℤ) : M2 Af := m.map (Int.castRingHom Af)

theorem isZ_toAf (m : M2 ℤ) : IsZ (toAf m) := fun i j => intCast_mem (m i j)

theorem toAf_mul (m n : M2 ℤ) : toAf (m * n) = toAf m * toAf n := Matrix.map_mul

theorem toAf_add (m n : M2 ℤ) : toAf (m + n) = toAf m + toAf n := Matrix.map_add _ (map_add _) m n

theorem toAf_smul (D : ℤ) (m : M2 ℤ) : toAf (D • m) = (D : Af) • toAf m := by
  ext i j
  simp only [toAf, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_mul]

theorem toAf_one : toAf 1 = 1 := by
  ext i j; simp [toAf, Matrix.one_apply]

theorem toAf_det (m : M2 ℤ) : (toAf m).det = (m.det : Af) := by
  rw [toAf, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

/-! ## §3. The level `U₀(N)` and its determinant -/

/-- **TYZ's `U₀(N) = {g ∈ GL₂(ℤ̂) : N ∣ c}`** (Period7.tex L1179–1181): `g` and `g⁻¹` have entries in
`ℤ̂`, and the lower-left entry of `g` lies in `N ℤ̂`. -/
def U0 (N : ℕ) : Subgroup (GL (Fin 2) Af) where
  carrier := {g | IsZ (g : M2 Af) ∧ IsZ ((g⁻¹ : GL (Fin 2) Af) : M2 Af) ∧ DvdZ N ((g : M2 Af) 1 0)}
  mul_mem' := by
    rintro g h ⟨hg, hg', c, hc, hgc⟩ ⟨hh, hh', c', hc', hhc⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul]; exact hg.mul hh
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact hh'.mul hg'
    · refine ⟨c * (h : M2 Af) 0 0 + (g : M2 Af) 1 1 * c',
        add_mem (mul_mem hc (hh 0 0)) (mul_mem (hg 1 1) hc'), ?_⟩
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hgc, hhc]; ring
  one_mem' := by
    refine ⟨?_, ?_, 0, Zhat.zero_mem, ?_⟩
    · rw [Units.val_one]; exact isZ_one
    · rw [inv_one, Units.val_one]; exact isZ_one
    · rw [Units.val_one, Matrix.one_apply_ne (by decide)]; ring
  inv_mem' := by
    rintro g ⟨hg, hg', c, hc, hgc⟩
    refine ⟨hg', by rw [inv_inv]; exact hg, ?_⟩
    set h : M2 Af := ((g⁻¹ : GL (Fin 2) Af) : M2 Af)
    have e := congrArg (fun A : M2 Af => A) (Units.inv_mul g)
    have e1 : h 0 0 * (g : M2 Af) 0 0 + h 0 1 * (g : M2 Af) 1 0 = 1 := by
      have := congrFun (congrFun e 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h] using this
    have e2 : h 1 0 * (g : M2 Af) 0 0 + h 1 1 * (g : M2 Af) 1 0 = 0 := by
      have := congrFun (congrFun e 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h] using this
    refine ⟨-(h 0 0 * h 1 1 - h 0 1 * h 1 0) * c,
      mul_mem (neg_mem (sub_mem (mul_mem (hg' 0 0) (hg' 1 1)) (mul_mem (hg' 0 1) (hg' 1 0)))) hc, ?_⟩
    show h 1 0 = _
    have key : h 1 0 = -(h 0 0 * h 1 1 - h 0 1 * h 1 0) * (g : M2 Af) 1 0 := by
      linear_combination (-(h 1 0)) * e1 + h 0 0 * e2
    conv_lhs => rw [key]
    rw [hgc]; ring

/-- `ℤ̂ˣ ⊂ 𝔸_fˣ`. -/
def ZhatU : Subgroup Afˣ where
  carrier := {u | (u : Af) ∈ Zhat ∧ ((u⁻¹ : Afˣ) : Af) ∈ Zhat}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [Units.val_mul]; exact mul_mem ha hb, ?_⟩
    rw [_root_.mul_inv_rev, Units.val_mul]; exact mul_mem hb' ha'
  one_mem' := ⟨by rw [Units.val_one]; exact Zhat.one_mem,
    by rw [inv_one, Units.val_one]; exact Zhat.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

theorem det_mem_of_isZ {A : M2 Af} (hA : IsZ A) : A.det ∈ Zhat := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hA 0 0) (hA 1 1)) (mul_mem (hA 0 1) (hA 1 0))

/-- `diag(1, u)` for a unit `u`. -/
def diagU (u : Afˣ) : GL (Fin 2) Af where
  val := !![1, 0; 0, (u : Af)]
  inv := !![1, 0; 0, ((u⁻¹ : Afˣ) : Af)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem det_diagU (u : Afˣ) : Matrix.GeneralLinearGroup.det (diagU u) = u := by
  ext; simp [diagU, Matrix.det_fin_two_of]

theorem diagU_mem {N : ℕ} {u : Afˣ} (hu : u ∈ ZhatU) : diagU u ∈ U0 N := by
  obtain ⟨hu, hu'⟩ := hu
  refine ⟨?_, ?_, 0, Zhat.zero_mem, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [diagU, hu, Zhat.one_mem, Zhat.zero_mem]
  · intro i j
    show ((diagU u)⁻¹ : GL (Fin 2) Af).val i j ∈ Zhat
    rw [show ((diagU u)⁻¹ : GL (Fin 2) Af).val = !![1, 0; 0, ((u⁻¹ : Afˣ) : Af)] from rfl]
    fin_cases i <;> fin_cases j <;> simp [hu', Zhat.one_mem, Zhat.zero_mem]
  · simp [diagU]

/-- **`det U₀(N) = ℤ̂ˣ`.** -/
theorem det_U0 (N : ℕ) : (U0 N).map Matrix.GeneralLinearGroup.det = ZhatU := by
  ext u
  constructor
  · rintro ⟨g, ⟨hg, hg', -⟩, rfl⟩
    refine ⟨det_mem_of_isZ hg, ?_⟩
    have : ((Matrix.GeneralLinearGroup.det g)⁻¹ : Afˣ) = Matrix.GeneralLinearGroup.det g⁻¹ :=
      (map_inv _ g).symm
    rw [this]; exact det_mem_of_isZ hg'
  · intro hu
    exact ⟨diagU u, diagU_mem hu, det_diagU u⟩

/-- **`SL₂(ℤ) → SL₂(ℤ/N)` is surjective** (Tau Ceti's `map_intCast_zmod_surjective`). -/
theorem sl2_reduction_surjective (N : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) :
      Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) :=
  Matrix.SpecialLinearGroup.map_intCast_zmod_surjective

/-! ## §4. A basis of the lattice `m ℤ² + D ℤ²` -/

/-- **The lattice `m ℤ² + D ℤ² ⊂ ℤ²` has a basis `γ`** (`ℤ` is a PID): `γ = m P + D Q`, `m = γ R`,
`D = γ S` for integer matrices `P, Q, R, S`. -/
theorem lattice_basis (m : M2 ℤ) (D : ℤ) (hD : D ≠ 0) :
    ∃ γ P Q R S : M2 ℤ, γ = m * P + D • Q ∧ m = γ * R ∧ D • (1 : M2 ℤ) = γ * S := by
  classical
  let v : Fin 2 ⊕ Fin 2 → (Fin 2 → ℤ) :=
    Sum.elim (fun j i => m i j) (fun j => D • Pi.single j 1)
  let L : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ (Set.range v)
  obtain ⟨n, b⟩ := L.basisOfPid (Pi.basisFun ℤ (Fin 2))
  have hvL : ∀ k, v k ∈ L := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hle : n ≤ 2 := by
    have h1 := Submodule.finrank_le L
    rw [Module.finrank_eq_card_basis b, Module.finrank_fin_fun] at h1
    simpa using h1
  have hge : 2 ≤ n := by
    let w : Fin 2 → L := fun j => ⟨v (Sum.inr j), hvL _⟩
    have hli : LinearIndependent ℤ w := by
      apply LinearIndependent.of_comp L.subtype
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := congrFun hc i
      simp [w, v, Finset.sum_apply, Pi.single_apply] at this
      tauto
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis b] at this
    simpa using this
  obtain rfl : n = 2 := le_antisymm hle hge
  have hb : ∀ j, (b j : Fin 2 → ℤ) ∈ L := fun j => (b j).2
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hb j)
  refine ⟨Matrix.of fun i j => (b j : Fin 2 → ℤ) i, Matrix.of fun i j => c j (Sum.inl i),
    Matrix.of fun i j => c j (Sum.inr i),
    Matrix.of fun k j => b.repr ⟨v (Sum.inl j), hvL _⟩ k,
    Matrix.of fun k j => b.repr ⟨v (Sum.inr j), hvL _⟩ k, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (hc j) i
    simp [Fintype.sum_sum_type, v, Finset.sum_apply, Pi.single_apply] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this ⊢
    linear_combination -this
  · ext i j
    have e := congrArg Subtype.val (b.sum_repr ⟨v (Sum.inl j), hvL _⟩)
    rw [Submodule.coe_sum] at e
    have := congrFun e i
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_two] at this
    simp [v] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two, v] at this ⊢
    linear_combination -this
  · ext i j
    have e := congrArg Subtype.val (b.sum_repr ⟨v (Sum.inr j), hvL _⟩)
    rw [Submodule.coe_sum] at e
    have := congrFun e i
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_two] at this
    simp [v, Pi.single_apply] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, v] at this ⊢
    linear_combination -this

/-- `lattice_basis` with `det γ > 0`. -/
theorem lattice_basis_pos (m : M2 ℤ) (D : ℤ) (hD : D ≠ 0) :
    ∃ γ P Q R S : M2 ℤ, 0 < γ.det ∧ γ = m * P + D • Q ∧ m = γ * R ∧ D • (1 : M2 ℤ) = γ * S := by
  obtain ⟨γ, P, Q, R, S, h1, h2, h3⟩ := lattice_basis m D hD
  have hdet : γ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h3
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one] at this
    simp [hD] at this
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · let J : M2 ℤ := !![1, 0; 0, -1]
    have hJ : J * J = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [J]
    refine ⟨γ * J, P * J, Q * J, J * R, J * S, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul]; simp [J, Matrix.det_fin_two_of]; linarith
    · rw [h1, Matrix.add_mul, Matrix.mul_assoc, Matrix.smul_mul]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc J J, hJ, Matrix.one_mul]; exact h2
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc J J, hJ, Matrix.one_mul]; exact h3
  · exact ⟨γ, P, Q, R, S, hpos, h1, h2, h3⟩

end ZInQ.AdelicX0
