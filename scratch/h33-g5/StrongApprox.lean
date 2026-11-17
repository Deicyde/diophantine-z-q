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

/-! ## §5. `GL₂(𝔸_f) = GL₂(ℚ)⁺ · GL₂(ℤ̂)` -/

/-- `GL₂(ℚ) → GL₂(𝔸_f)`. -/
abbrev mapQ : GL (Fin 2) ℚ →* GL (Fin 2) Af := Matrix.GeneralLinearGroup.map (algebraMap ℚ Af)

theorem mapQ_val (γ : GL (Fin 2) ℚ) : (mapQ γ : M2 Af) = (γ : M2 ℚ).map (algebraMap ℚ Af) := rfl

/-- A finite adele has an integer denominator (Tau Ceti). -/
theorem exists_den (a : Af) : ∃ M : ℤ, M ≠ 0 ∧ (M : Af) * a ∈ Zhat := by
  obtain ⟨b, hb0, hb⟩ := FiniteAdeleRing.mul_nonZeroDivisor_mem_integralAdeles (R := ℤ) (K := ℚ) a
  refine ⟨b, nonZeroDivisors.ne_zero hb0, ?_⟩
  simpa [algebraMap_int_eq, mul_comm] using hb

theorem exists_den_mat (A : M2 Af) : ∃ M : ℤ, M ≠ 0 ∧ IsZ ((M : Af) • A) := by
  classical
  choose M hM0 hM using fun i j => exists_den (A i j)
  refine ⟨∏ p : Fin 2 × Fin 2, M p.1 p.2, Finset.prod_ne_zero_iff.mpr fun p _ => hM0 _ _, ?_⟩
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  have : ((∏ p : Fin 2 × Fin 2, M p.1 p.2 : ℤ) : Af) * A i j =
      ((M i j : Af) * A i j) * ((∏ p ∈ Finset.univ.erase (i, j), M p.1 p.2 : ℤ) : Af) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun p : Fin 2 × Fin 2 => M p.1 p.2)
      (Finset.mem_univ (i, j))]
    push_cast; ring
  rw [this]; exact mul_mem (hM i j) (intCast_mem _)

theorem isUnit_intCast {z : ℤ} (hz : z ≠ 0) : IsUnit (z : Af) := by
  rw [← algebraMap_int]
  exact (IsUnit.mk0 _ (by exact_mod_cast hz : (z : ℚ) ≠ 0)).map _

/-- **`GL₂(𝔸_f) = GL₂(ℚ)⁺ · GL₂(ℤ̂)`** (`U0 1 = GL₂(ℤ̂)`). -/
theorem exists_GLpos_mul_GLZhat (g : GL (Fin 2) Af) :
    ∃ γ ∈ Matrix.GLPos (Fin 2) ℚ, ∃ k ∈ U0 1, g = mapQ γ * k := by
  classical
  obtain ⟨M1, hM1, hA⟩ := exists_den_mat (g : M2 Af)
  obtain ⟨M2', hM2, hB⟩ := exists_den_mat ((g⁻¹ : GL (Fin 2) Af) : M2 Af)
  set A := (M1 : Af) • (g : M2 Af) with hAdef
  set B := (M2' : Af) • ((g⁻¹ : GL (Fin 2) Af) : M2 Af) with hBdef
  set D : ℤ := M1 * M2' with hDdef
  have hD : D ≠ 0 := mul_ne_zero hM1 hM2
  have hAB : A * B = (D : Af) • (1 : M2 Af) := by
    rw [hAdef, hBdef, Matrix.smul_mul, Matrix.mul_smul, Units.mul_inv, smul_smul, hDdef,
      Int.cast_mul]
  choose r c hc hrc using fun i j => exists_int_sub_dvdZ D hD (hA i j)
  set m : M2 ℤ := Matrix.of r with hm
  set X : M2 Af := Matrix.of c with hX
  have hXZ : IsZ X := fun i j => hc i j
  have hAmX : A = toAf m + (D : Af) • X := by
    refine Matrix.ext fun i j => ?_
    have := hrc i j
    simp only [toAf, hm, hX, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom]
    linear_combination this
  obtain ⟨γ, P, Q, R, S, hdet, h1, h2, h3⟩ := lattice_basis_pos m D hD
  have e1 : toAf γ = toAf m * toAf P + (D : Af) • toAf Q := by
    rw [h1, toAf_add, toAf_mul, toAf_smul]
  have e2 : toAf m = toAf γ * toAf R := by rw [← toAf_mul, ← h2]
  have e3 : (D : Af) • (1 : M2 Af) = toAf γ * toAf S := by
    rw [← toAf_mul, ← h3, toAf_smul, toAf_one]
  set k := toAf R + toAf S * X with hkdef
  set k' := toAf P - B * X * toAf P + B * toAf Q with hk'def
  have hk : toAf γ * k = A := by
    rw [hkdef, Matrix.mul_add, ← Matrix.mul_assoc, ← e2, ← e3, Matrix.smul_mul, Matrix.one_mul,
      hAmX]
  have hΓ : IsUnit (toAf γ).det := by rw [toAf_det]; exact isUnit_intCast hdet.ne'
  have hkk' : k * k' = 1 := by
    have h0 : toAf γ * (k * k') = toAf γ * 1 := by
      rw [← Matrix.mul_assoc, hk, Matrix.mul_one, hk'def]
      simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hAB]
      rw [e1, hAmX]
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
      abel
    have := congrArg (fun Y => (toAf γ)⁻¹ * Y) h0
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_mul] using this
  let kU : GL (Fin 2) Af := ⟨k, k', hkk', mul_eq_one_comm.mp hkk'⟩
  have hkU : kU ∈ U0 1 := by
    refine ⟨(isZ_toAf R).add ((isZ_toAf S).mul hXZ),
      ((isZ_toAf P).sub ((hB.mul hXZ).mul (isZ_toAf P))).add (hB.mul (isZ_toAf Q)),
      k 1 0, ?_, by simp [kU]⟩
    exact (isZ_toAf R).add ((isZ_toAf S).mul hXZ) 1 0
  have hM1q : (M1 : ℚ) ≠ 0 := by exact_mod_cast hM1
  have hγdet : ((M1 : ℚ)⁻¹ • (γ.map (Int.castRingHom ℚ))).det ≠ 0 := by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp [hM1q, hdet.ne']
  let γq : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hγdet
  refine ⟨γq, ?_, kU, hkU, ?_⟩
  · rw [Matrix.mem_glpos]
    show 0 < ((M1 : ℚ)⁻¹ • (γ.map (Int.castRingHom ℚ))).det
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have : (0 : ℚ) < γ.det := by exact_mod_cast hdet
    simp only [Fintype.card_fin, eq_intCast]
    positivity
  · apply Units.ext
    show (g : M2 Af) = ((M1 : ℚ)⁻¹ • (γ.map (Int.castRingHom ℚ))).map (algebraMap ℚ Af) * k
    have hmap : ((M1 : ℚ)⁻¹ • (γ.map (Int.castRingHom ℚ))).map (algebraMap ℚ Af) =
        algebraMap ℚ Af ((M1 : ℚ)⁻¹) • toAf γ := by
      refine Matrix.ext fun i j => ?_; simp [toAf]
    rw [hmap, Matrix.smul_mul, hk, hAdef, smul_smul, ← algebraMap_int,
      ← map_mul, inv_mul_cancel₀ hM1q, map_one, one_smul]

/-! ## §6. `GL₂(ℤ̂) = SL₂(ℤ) · U₀(N)` and strong approximation -/

/-- `SL₂(ℤ) → GL₂(𝔸_f)`. -/
def mapZ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) Af where
  val := toAf σ
  inv := toAf ↑σ⁻¹
  val_inv := by
    rw [← toAf_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, toAf_one]
  inv_val := by
    rw [← toAf_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, toAf_one]

/-- `SL₂(ℤ) → GL₂(ℚ)⁺`. -/
def sigQ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℚ :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ)

theorem sigQ_mem (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : sigQ σ ∈ Matrix.GLPos (Fin 2) ℚ := by
  rw [Matrix.mem_glpos]
  simp [sigQ]

theorem mapQ_sigQ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : mapQ (sigQ σ) = mapZ σ := by
  apply Units.ext
  ext i j
  simp [sigQ, mapZ, toAf]

theorem mapZ_mem {N : ℕ} {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) : mapZ σ ∈ U0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ
  obtain ⟨t, ht⟩ := hσ
  refine ⟨isZ_toAf _, isZ_toAf _, t, intCast_mem t, ?_⟩
  show toAf σ 1 0 = _
  simp [toAf, ht]

theorem exists_SL2Z_mul (N : ℕ) (hN : N ≠ 0) {k : GL (Fin 2) Af} (hk : k ∈ U0 1) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ u ∈ U0 N, k = mapZ σ * u := by
  classical
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN
  set d := Matrix.GeneralLinearGroup.det k with hddef
  have hd : d ∈ ZhatU := by rw [← det_U0 1]; exact ⟨k, hk, rfl⟩
  set k1 := k * diagU d⁻¹ with hk1def
  have hk1det : (k1 : M2 Af).det = 1 := by
    have := congrArg Units.val (map_mul Matrix.GeneralLinearGroup.det k (diagU d⁻¹))
    rw [det_diagU, ← hddef, mul_inv_cancel, Units.val_one] at this
    rw [← this]; rfl
  have hk1 : k1 ∈ U0 1 := mul_mem hk (diagU_mem (inv_mem hd))
  obtain ⟨hk1Z, hk1'Z, -⟩ := hk1
  choose r c hc hrc using fun i j => exists_int_sub_dvdZ N hN' (hk1Z i j)
  set m : M2 ℤ := Matrix.of r with hm
  set Y : M2 Af := Matrix.of c with hY
  have hYZ : IsZ Y := fun i j => hc i j
  have hk1m : ∀ i j, (k1 : M2 Af) i j = (m i j : Af) + N * Y i j := fun i j => by
    have := hrc i j; push_cast at this; simp only [hm, hY, Matrix.of_apply]
    linear_combination this
  have hdetm : DvdZ N ((m.det - 1 : ℤ) : Af) := by
    set K := (k1 : M2 Af)
    refine ⟨-(K 0 0 * Y 1 1 + Y 0 0 * K 1 1 - K 0 1 * Y 1 0 - Y 0 1 * K 1 0) +
      N * (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0), ?_, ?_⟩
    · have hK := hk1Z
      exact add_mem (neg_mem (sub_mem (sub_mem (add_mem (mul_mem (hK 0 0) (hYZ 1 1))
        (mul_mem (hYZ 0 0) (hK 1 1))) (mul_mem (hK 0 1) (hYZ 1 0)))
        (mul_mem (hYZ 0 1) (hK 1 0)))) (mul_mem (intCast_mem N)
        (sub_mem (mul_mem (hYZ 0 0) (hYZ 1 1)) (mul_mem (hYZ 0 1) (hYZ 1 0))))
    · have hdK : K 0 0 * K 1 1 - K 0 1 * K 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hk1det
      rw [Int.cast_sub, Int.cast_one, Matrix.det_fin_two m]
      push_cast
      have e : ∀ i j, (m i j : Af) = K i j - N * Y i j := fun i j => by
        rw [hk1m i j]; ring
      rw [e 0 0, e 0 1, e 1 0, e 1 1]
      linear_combination hdK
  have hNd : (N : ℤ) ∣ m.det - 1 := int_dvd_of_dvdZ hN' hdetm
  let mbar : Matrix.SpecialLinearGroup (Fin 2) (ZMod N) :=
    ⟨m.map (Int.castRingHom (ZMod N)), by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (m.det - 1) N).mpr hNd
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      exact this⟩
  obtain ⟨σ, hσ⟩ := sl2_reduction_surjective N mbar
  have hσm : ∀ i j, (N : ℤ) ∣ σ i j - m i j := by
    intro i j
    have := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 2) (ZMod N) =>
      (s : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) hσ
    simp only [mbar, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this.symm
  choose t ht using hσm
  set Y' : M2 Af := Y - (Matrix.of fun i j => (t i j : Af)) with hY'
  have hY'Z : IsZ Y' := hYZ.sub fun i j => intCast_mem _
  have hk1σ : (k1 : M2 Af) = toAf σ + (N : Af) • Y' := by
    refine Matrix.ext fun i j => ?_
    have e := ht i j
    have e' : ((σ i j : ℤ) : Af) = (m i j : Af) + N * t i j := by
      have : σ i j = m i j + N * t i j := by linarith
      rw [this]; push_cast; ring
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hY', Matrix.sub_apply,
      Matrix.of_apply, toAf, Matrix.map_apply, Int.coe_castRingHom, hk1m i j, e']
    ring
  set u := (mapZ σ)⁻¹ * k1 with hudef
  have hu : u ∈ U0 N := by
    refine ⟨?_, ?_, ?_⟩
    · show IsZ (toAf ↑σ⁻¹ * (k1 : M2 Af))
      exact (isZ_toAf _).mul hk1Z
    · rw [hudef, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      exact hk1'Z.mul (isZ_toAf _)
    · refine ⟨(toAf ↑σ⁻¹ * Y') 1 0, ((isZ_toAf _).mul hY'Z) 1 0, ?_⟩
      show (toAf ↑σ⁻¹ * (k1 : M2 Af)) 1 0 = _
      have hinv : toAf ↑σ⁻¹ * toAf σ = 1 := (mapZ σ).inv_val
      rw [hk1σ, Matrix.mul_add, hinv, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (by decide), smul_eq_mul, zero_add]
      push_cast; ring
  refine ⟨σ, u * (diagU d⁻¹)⁻¹, mul_mem hu (inv_mem (diagU_mem (inv_mem hd))), ?_⟩
  rw [hudef, hk1def]; group

/-- **Strong approximation for `GL₂` (the form TYZ use): `GL₂(𝔸_f) = GL₂(ℚ)⁺ · U₀(N)`.** -/
theorem strong_approx (N : ℕ) (hN : N ≠ 0) (g : GL (Fin 2) Af) :
    ∃ γ ∈ Matrix.GLPos (Fin 2) ℚ, ∃ u ∈ U0 N, g = mapQ γ * u := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := exists_GLpos_mul_GLZhat g
  obtain ⟨σ, u, hu, rfl⟩ := exists_SL2Z_mul N hN hk
  exact ⟨γ * sigQ σ, mul_mem hγ (sigQ_mem σ), u, hu, by rw [map_mul, mapQ_sigQ, mul_assoc]⟩

/-! ## §7. The double coset space `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U)` and `Γ₀(N) \ ℍ` -/

open UpperHalfPlane

/-- `GL₂(ℚ) → GL₂(ℝ)`, acting on `ℍ` by Möbius transformations (Mathlib's action). -/
abbrev toGLR : GL (Fin 2) ℚ →* GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- The relation `(z, g) ~ (γ z, γ g u)` for `γ ∈ GL₂(ℚ)⁺`, `u ∈ U`. -/
def shSetoid (U : Subgroup (GL (Fin 2) Af)) : Setoid (ℍ × GL (Fin 2) Af) where
  r p q := ∃ γ ∈ Matrix.GLPos (Fin 2) ℚ, ∃ u ∈ U, q.1 = toGLR γ • p.1 ∧ q.2 = mapQ γ * p.2 * u
  iseqv := {
    refl := fun p => ⟨1, one_mem _, 1, one_mem _, by simp, by simp⟩
    symm := by
      rintro p q ⟨γ, hγ, u, hu, h1, h2⟩
      refine ⟨γ⁻¹, inv_mem hγ, u⁻¹, inv_mem hu, ?_, ?_⟩
      · rw [h1, map_inv, inv_smul_smul]
      · rw [h2, map_inv]; group
    trans := by
      rintro p q w ⟨γ, hγ, u, hu, h1, h2⟩ ⟨γ', hγ', u', hu', h1', h2'⟩
      refine ⟨γ' * γ, mul_mem hγ' hγ, u * u', mul_mem hu hu', ?_, ?_⟩
      · rw [h1', h1, map_mul, mul_smul]
      · rw [h2', h2, map_mul]; group }

/-- **The double coset space `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U)`**: TYZ's complex uniformization of the
adelic modular curve `X_U` without its cusps (Period7.tex L1518–1520, there with `ℍ ∪ ℙ¹(ℚ)`). -/
def Sh (U : Subgroup (GL (Fin 2) Af)) : Type := Quotient (shSetoid U)

/-- The point `[z, g]`. -/
def shMk (U : Subgroup (GL (Fin 2) Af)) (z : ℍ) (g : GL (Fin 2) Af) : Sh U :=
  Quotient.mk (shSetoid U) (z, g)

/-- `τ ↦ [τ, 1]`. -/
def toSh (U : Subgroup (GL (Fin 2) Af)) (τ : ℍ) : Sh U := shMk U τ 1

/-- The natural projection `X_V(ℂ) → X_U(ℂ)` for `V ≤ U` (TYZ's `f₀ : X_U → X₀(32)`, L1187). -/
def shMap {V U : Subgroup (GL (Fin 2) Af)} (h : V ≤ U) : Sh V → Sh U :=
  Quotient.map id fun _ _ ⟨γ, hγ, u, hu, h1, h2⟩ => ⟨γ, hγ, u, h hu, h1, h2⟩

theorem shMap_shMk {V U : Subgroup (GL (Fin 2) Af)} (h : V ≤ U) (z : ℍ) (g : GL (Fin 2) Af) :
    shMap h (shMk V z g) = shMk U z g := rfl

theorem shMap_toSh {V U : Subgroup (GL (Fin 2) Af)} (h : V ≤ U) (τ : ℍ) :
    shMap h (toSh V τ) = toSh U τ := rfl

/-- The `SL₂(ℤ)`-action on `ℍ` is the `GL₂(ℚ)`-action through `SL₂(ℤ) → GL₂(ℚ)`. -/
theorem sl_smul_eq (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) :
    σ • τ = toGLR (sigQ σ) • τ := by
  rw [ModularGroup.sl_moeb]
  congr 1
  apply Units.ext
  ext i j
  simp [sigQ]

/-- **`GL₂(ℚ)⁺ ∩ U₀(N) = Γ₀(N)`.** -/
theorem exists_gamma0_of_mapQ_mem {N : ℕ} (hN : N ≠ 0) {γ : GL (Fin 2) ℚ}
    (hγ : γ ∈ Matrix.GLPos (Fin 2) ℚ) (h : mapQ γ ∈ U0 N) :
    ∃ σ ∈ CongruenceSubgroup.Gamma0 N, sigQ σ = γ := by
  obtain ⟨hZ, hZ', c, hc, hdv⟩ := h
  have hent : ∀ i j, ∃ z : ℤ, (γ : M2 ℚ) i j = z := fun i j => exists_int_of_mem (hZ i j)
  have hent' : ∀ i j, ∃ z : ℤ, ((γ⁻¹ : GL (Fin 2) ℚ) : M2 ℚ) i j = z := fun i j => by
    have := hZ' i j
    rw [← map_inv, mapQ_val, Matrix.map_apply] at this
    exact exists_int_of_mem this
  choose a ha using hent
  choose b hb using hent'
  have hγa : (γ : M2 ℚ) = (Matrix.of a).map (Int.castRingHom ℚ) := by
    ext i j; simp [ha]
  have hγb : ((γ⁻¹ : GL (Fin 2) ℚ) : M2 ℚ) = (Matrix.of b).map (Int.castRingHom ℚ) := by
    ext i j; simp [hb]
  have hdet1 : (Matrix.of a).det * (Matrix.of b).det = 1 := by
    have h1 := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel γ))
    rw [Units.val_mul, Matrix.det_mul, hγa, hγb, Units.val_one, Matrix.det_one,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ← map_mul] at h1
    have h2 : (((Matrix.of a).det * (Matrix.of b).det : ℤ) : ℚ) = 1 := h1
    exact_mod_cast h2
  have hpos : 0 < (Matrix.of a).det := by
    have := (Matrix.mem_glpos γ).mp hγ
    rw [Matrix.GeneralLinearGroup.val_det_apply, hγa, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det] at this
    have h2 : (0 : ℚ) < (((Matrix.of a).det : ℤ) : ℚ) := this
    exact_mod_cast h2
  have hdeta : (Matrix.of a).det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet1 with h | h
    · exact h
    · omega
  let σ : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨Matrix.of a, hdeta⟩
  refine ⟨σ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply int_dvd_of_dvdZ (by exact_mod_cast hN)
    refine ⟨c, hc, ?_⟩
    rw [mapQ_val, Matrix.map_apply, ha 1 0, algebraMap_int] at hdv
    exact hdv
  · apply Units.ext
    ext i j
    simp [sigQ, σ, ha]
    rfl

/-- **`[τ, 1] = [τ', 1]` in `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(N))` iff `τ' ∈ Γ₀(N) τ`.** -/
theorem toSh_eq_toSh_iff {N : ℕ} (hN : N ≠ 0) (τ τ' : ℍ) :
    toSh (U0 N) τ = toSh (U0 N) τ' ↔ ∃ σ ∈ CongruenceSubgroup.Gamma0 N, τ' = σ • τ := by
  constructor
  · intro h
    obtain ⟨γ, hγ, u, hu, h1, h2⟩ := Quotient.exact h
    have hγU : mapQ γ ∈ U0 N := by
      have : mapQ γ = u⁻¹ := by
        simp only [mul_one] at h2
        exact eq_inv_of_mul_eq_one_left h2.symm
      rw [this]; exact inv_mem hu
    obtain ⟨σ, hσ, rfl⟩ := exists_gamma0_of_mapQ_mem hN hγ hγU
    exact ⟨σ, hσ, by rw [sl_smul_eq]; exact h1⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine Quotient.sound ⟨sigQ σ, sigQ_mem σ, (mapZ σ)⁻¹, inv_mem (mapZ_mem hσ), ?_, ?_⟩
    · exact sl_smul_eq σ τ
    · show (1 : GL (Fin 2) Af) = mapQ (sigQ σ) * 1 * (mapZ σ)⁻¹
      rw [mapQ_sigQ, mul_one, mul_inv_cancel]

/-- **Every point of `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(N))` is `[τ, 1]`** (strong approximation). -/
theorem toSh_surjective {N : ℕ} (hN : N ≠ 0) : Function.Surjective (toSh (U0 N)) := by
  intro P
  induction P using Quotient.inductionOn with
  | h p =>
    obtain ⟨z, g⟩ := p
    obtain ⟨γ, hγ, u, hu, rfl⟩ := strong_approx N hN g
    refine ⟨toGLR γ⁻¹ • z, Quotient.sound ⟨γ, hγ, u, hu, ?_, ?_⟩⟩
    · show z = toGLR γ • toGLR γ⁻¹ • z
      rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    · show mapQ γ * u = mapQ γ * 1 * u
      rw [mul_one]

/-- **The bijection `Γ₀(N) \ ℍ ≃ GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(N))`, `Γ₀(N) τ ↦ [τ, 1]`.** -/
def gamma0OrbitsEquiv (N : ℕ) (hN : N ≠ 0) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N) ℍ ≃ Sh (U0 N) :=
  Equiv.ofBijective
    (Quotient.lift (toSh (U0 N)) fun a b hab => by
      obtain ⟨g, hg⟩ := hab
      refine ((toSh_eq_toSh_iff hN b a).mpr ⟨g, g.2, ?_⟩).symm
      rw [← hg]; rfl)
    ⟨by
      intro P Q hPQ
      induction P using Quotient.inductionOn with
      | h a =>
      induction Q using Quotient.inductionOn with
      | h b =>
        obtain ⟨σ, hσ, hb⟩ := (toSh_eq_toSh_iff hN a b).mp hPQ
        apply Quotient.sound
        refine ⟨⟨σ, hσ⟩⁻¹, ?_⟩
        show (⟨σ, hσ⟩⁻¹ : CongruenceSubgroup.Gamma0 N) • b = a
        rw [hb, Subgroup.smul_def, Subgroup.coe_inv, inv_smul_smul],
    fun P => by
      obtain ⟨τ, rfl⟩ := toSh_surjective hN P
      exact ⟨Quotient.mk _ τ, rfl⟩⟩

theorem gamma0OrbitsEquiv_mk (N : ℕ) (hN : N ≠ 0) (τ : ℍ) :
    gamma0OrbitsEquiv N hN (Quotient.mk _ τ) = toSh (U0 N) τ := rfl

end ZInQ.AdelicX0
