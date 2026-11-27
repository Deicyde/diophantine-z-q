import ZInQKernel.Contrib.OneProof.RayClassShimura

/-! # The lattice step of Deligne's 4.12 for the kernel's PEL datum

PEL datum: `B = (2, −3 | ℚ)` (`LeafQM.B`), `V = B` with `B` acting by left multiplication,
`V_ℤ = 𝒪` (`LeafQM.O`, `LeafQM.InO`), `K = K₃` (`ShimuraCFT.K3Q`).

For `g ∈ (B ⊗ 𝔸_f)^×` the lattice of the point `[h, g]` is `L_g = B ∩ 𝒪̂ g⁻¹`
(`latticeAt g = {b ∈ B | b g ∈ 𝒪̂}`), the convention of the docstrings of `ModuliAtUnits` and
`ShimuraMainThmIDeligneY3AbU` (`RayClassShimura.lean`). This file proves:

* A0 `rat_mem_ZhatQ_iff`: `ℚ ∩ ℤ̂ = ℤ`;
* A1 `bEmb_mem_OhatQ_iff`: `B ∩ 𝒪̂ = 𝒪`;
* A2 `latticeAt_of_mem_OhatU`: `L_u = 𝒪` for `u ∈ 𝒪̂^×`;
* A3 `latticeAt` is an additive subgroup stable under left multiplication by `𝒪`
  (`latticeAt_add`, `latticeAt_zero`, `latticeAt_neg`, `latticeAt_mul_left`), squeezed between
  `N𝒪` and `N⁻¹𝒪` (`latticeAt_bounds`), and is a full `ℤ`-lattice: the `ℤ`-span of a `ℚ`-basis of
  `B` (`latticeAt_basis`);
* A4 `latticeAt_dc`, `latticeAt_of_DCRel`: `L_{γ g k} = L_g γ⁻¹` for `γ ∈ B^×`, `k ∈ K₃`.

The class-number-one statement `RayClassCFT.classNumberOneB_proof` (proved in the tree) gives
`L_g = 𝒪 α` (`latticeAt_eq_O_mul`), from which the basis is read off. -/

noncomputable section

namespace Y3Lattice412

open LeafQM ShimuraCFT RayClassCFT

/-! ## A0, A1 -/

/-- **A0. `ℚ ∩ ℤ̂ = ℤ`** in `𝔸_f`. -/
theorem rat_mem_ZhatQ_iff (r : ℚ) : algebraMap ℚ AQ r ∈ ZhatQ ↔ ∃ z : ℤ, r = z :=
  rat_mem_zhat_iff r

/-- **A1. `B ∩ 𝒪̂ = 𝒪`** in `B ⊗ 𝔸_f`. -/
theorem bEmb_mem_OhatQ_iff (b : LeafQM.B) : bEmb b ∈ OhatQ ↔ InO b :=
  ⟨inO_of_bEmb_mem, bEmb_mem_of_inO⟩

/-! ## A2. The lattice `L_g = B ∩ 𝒪̂ g⁻¹` -/

/-- **`L_g = B ∩ 𝒪̂ g⁻¹ = {b ∈ B | b g ∈ 𝒪̂}`**, the lattice of the point `[h, g]`. -/
def latticeAt (g : BAQˣ) : Set LeafQM.B := {b | bEmb b * (g : BAQ) ∈ OhatQ}

theorem mem_latticeAt {g : BAQˣ} {b : LeafQM.B} : b ∈ latticeAt g ↔ bEmb b * (g : BAQ) ∈ OhatQ :=
  Iff.rfl

/-- Right multiplication by a unit of `𝒪̂` preserves `𝒪̂`-membership. -/
theorem mul_mem_OhatQ_iff_of_OhatU {x : BAQ} {u : BAQˣ} (hu : u ∈ OhatU) :
    x * (u : BAQ) ∈ OhatQ ↔ x ∈ OhatQ := by
  refine ⟨fun h => ?_, fun h => OhatQ_mul h hu.1⟩
  have e : x = x * (u : BAQ) * ((u⁻¹ : BAQˣ) : BAQ) := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [e]
  exact OhatQ_mul h hu.2

/-- `L_{g u} = L_g` for `u ∈ 𝒪̂^×`. -/
theorem latticeAt_mul_OhatU (g : BAQˣ) {u : BAQˣ} (hu : u ∈ OhatU) :
    latticeAt (g * u) = latticeAt g := by
  ext b
  simp only [mem_latticeAt, Units.val_mul, ← mul_assoc]
  exact mul_mem_OhatQ_iff_of_OhatU hu

theorem latticeAt_one : latticeAt 1 = {b | InO b} := by
  ext b
  simp only [mem_latticeAt, Units.val_one, mul_one, Set.mem_ofPred_eq]
  exact bEmb_mem_OhatQ_iff b

/-- **A2. `L_u = 𝒪` for `u ∈ 𝒪̂^×`.** -/
theorem latticeAt_of_mem_OhatU {u : BAQˣ} (hu : u ∈ OhatU) : latticeAt u = {b | InO b} := by
  rw [← latticeAt_one, ← latticeAt_mul_OhatU 1 hu, one_mul]

/-! ## A3. `L_g` is a left `𝒪`-lattice -/

theorem latticeAt_zero (g : BAQˣ) : (0 : LeafQM.B) ∈ latticeAt g := by
  simp only [mem_latticeAt, map_zero, zero_mul]
  exact OhatQ_zero

theorem latticeAt_add {g : BAQˣ} {a b : LeafQM.B} (ha : a ∈ latticeAt g) (hb : b ∈ latticeAt g) :
    a + b ∈ latticeAt g := by
  simp only [mem_latticeAt, map_add, add_mul] at *
  exact OhatQ_add ha hb

theorem latticeAt_neg {g : BAQˣ} {a : LeafQM.B} (ha : a ∈ latticeAt g) : -a ∈ latticeAt g := by
  simp only [mem_latticeAt, map_neg, neg_mul] at *
  exact OhatQ_neg ha

/-- `L_g` is stable under left multiplication by `𝒪`. -/
theorem latticeAt_mul_left {g : BAQˣ} {a b : LeafQM.B} (ha : InO a) (hb : b ∈ latticeAt g) :
    a * b ∈ latticeAt g := by
  rw [mem_latticeAt, map_mul, mul_assoc]
  exact OhatQ_mul (bEmb_mem_of_inO ha) hb

/-- `L_g` as an additive subgroup of `B`. -/
def latticeAtAddSubgroup (g : BAQˣ) : AddSubgroup LeafQM.B where
  carrier := latticeAt g
  add_mem' := latticeAt_add
  zero_mem' := latticeAt_zero g
  neg_mem' := latticeAt_neg

/-- `D x ∈ 𝒪̂` and `D x⁻¹ ∈ 𝒪̂` for one `D ≥ 1` (a finite adele is integral at all but finitely many
places: `RayClassCFT.exists_den`). -/
theorem exists_den_unit (g : BAQˣ) : ∃ D : ℕ, 0 < D ∧ (D : BAQ) * (g : BAQ) ∈ OhatQ ∧
    (D : BAQ) * ((g⁻¹ : BAQˣ) : BAQ) ∈ OhatQ := by
  obtain ⟨D1, h1, e1⟩ := exists_den_B (g : BAQ)
  obtain ⟨D2, h2, e2⟩ := exists_den_B ((g⁻¹ : BAQˣ) : BAQ)
  refine ⟨D1 * D2, Nat.mul_pos h1 h2, ?_, ?_⟩
  · rw [show ((D1 * D2 : ℕ) : BAQ) = (D2 : BAQ) * D1 by rw [mul_comm D1 D2, Nat.cast_mul], mul_assoc]
    exact OhatQ_mul (OhatQ_natCast D2) e1
  · rw [Nat.cast_mul, mul_assoc]
    exact OhatQ_mul (OhatQ_natCast D1) e2

/-- **A3 (bounds). `N 𝒪 ⊆ L_g ⊆ N⁻¹ 𝒪`** for some integer `N ≥ 1`. -/
theorem latticeAt_bounds (g : BAQˣ) : ∃ N : ℕ, 0 < N ∧
    (∀ b : LeafQM.B, InO b → (N : ℚ) • b ∈ latticeAt g) ∧
    (∀ b ∈ latticeAt g, InO ((N : ℚ) • b)) := by
  obtain ⟨D, hD, hDg, hDh⟩ := exists_den_unit g
  refine ⟨D, hD, fun b hb => ?_, fun b hb => ?_⟩
  · rw [mem_latticeAt, bEmb_natSmul, Nat.cast_comm, mul_assoc]
    exact OhatQ_mul (bEmb_mem_of_inO hb) hDg
  · apply inO_of_bEmb_mem
    rw [bEmb_natSmul]
    have e : (D : BAQ) * bEmb b = (bEmb b * (g : BAQ)) * ((D : BAQ) * ((g⁻¹ : BAQˣ) : BAQ)) := by
      calc (D : BAQ) * bEmb b = (D : BAQ) * bEmb b * ((g : BAQ) * ((g⁻¹ : BAQˣ) : BAQ)) := by
            rw [Units.mul_inv, mul_one]
        _ = ((D : BAQ) * (bEmb b * g)) * ((g⁻¹ : BAQˣ) : BAQ) := by simp only [mul_assoc]
        _ = ((bEmb b * g) * (D : BAQ)) * ((g⁻¹ : BAQˣ) : BAQ) := by rw [Nat.cast_comm]
        _ = (bEmb b * (g : BAQ)) * ((D : BAQ) * ((g⁻¹ : BAQˣ) : BAQ)) := by simp only [mul_assoc]
    rw [e]
    exact OhatQ_mul hb hDh

/-! ## A4. Double cosets -/

theorem nrdQ_ne_zero_of_ne_zero {γ : LeafQM.B} (hγ : γ ≠ 0) : ShimuraGlue.nrdQ ℚ γ ≠ 0 := by
  have h := HDec.QMSplit.CNO.nrd_ne_zero hγ
  rw [ShimuraGlue.nrdQ_apply]
  simpa [HDec.QMSplit.CNO.nrd] using h

/-- `L_{γ g k} = L_g γ⁻¹` for `γ ∈ B`, `nrd γ ≠ 0`, `k ∈ 𝒪̂^×` (here `γ⁻¹ = binv γ`). -/
theorem latticeAt_dc_of_OhatU {γ : LeafQM.B} (hγ : ShimuraGlue.nrdQ ℚ γ ≠ 0) {g g' k : BAQˣ}
    (hk : k ∈ OhatU) (h : (g' : BAQ) = bEmb γ * (g : BAQ) * (k : BAQ)) :
    latticeAt g' = (fun b => b * binv γ) '' latticeAt g := by
  have key : ∀ b, b ∈ latticeAt g' ↔ b * γ ∈ latticeAt g := by
    intro b
    rw [mem_latticeAt, mem_latticeAt, h, map_mul, ← mul_assoc, ← mul_assoc, mul_assoc (bEmb b)]
    rw [← mul_assoc]
    exact mul_mem_OhatQ_iff_of_OhatU hk
  ext b
  constructor
  · intro hb
    refine ⟨b * γ, (key b).1 hb, ?_⟩
    show b * γ * binv γ = b
    rw [mul_assoc, mul_binv hγ, mul_one]
  · rintro ⟨x, hx, rfl⟩
    rw [key]
    show x * binv γ * γ ∈ latticeAt g
    rw [mul_assoc, binv_mul hγ, mul_one]
    exact hx

theorem K3Q_subset_OhatU {k : BAQˣ} (hk : k ∈ K3Q) : k ∈ OhatU := ⟨hk.1, hk.2.1⟩

/-- `binv γ` is the inverse of `γ` in `B` when `γ ≠ 0`. -/
theorem binv_spec {γ : LeafQM.B} (hγ : γ ≠ 0) : γ * binv γ = 1 ∧ binv γ * γ = 1 :=
  ⟨mul_binv (nrdQ_ne_zero_of_ne_zero hγ), binv_mul (nrdQ_ne_zero_of_ne_zero hγ)⟩

/-- **A4. Double cosets: `L_{γ g k} = L_g γ⁻¹`** for `γ ∈ B`, `γ ≠ 0`, `k ∈ K₃` (as in `DCRel`). -/
theorem latticeAt_dc {γ : LeafQM.B} (hγ : γ ≠ 0) {g g' k : BAQˣ} (hk : k ∈ K3Q)
    (h : (g' : BAQ) = bEmb γ * (g : BAQ) * (k : BAQ)) :
    latticeAt g' = (fun b => b * binv γ) '' latticeAt g :=
  latticeAt_dc_of_OhatU (nrdQ_ne_zero_of_ne_zero hγ) (K3Q_subset_OhatU hk) h

/-- A4 in the form of `DCRel`: related points have lattices related by the same `γ`. -/
theorem latticeAt_of_DCRel {τ τ' : UpperHalfPlane} {g g' : BAQˣ} (h : DCRel τ g τ' g') :
    ∃ γ : LeafQM.B, 0 < ShimuraGlue.nrdQ ℚ γ ∧
      latticeAt g' = (fun b => b * binv γ) '' latticeAt g := by
  obtain ⟨γ, hpos, -, k, hk, he⟩ := h
  exact ⟨γ, hpos, latticeAt_dc_of_OhatU hpos.ne' (K3Q_subset_OhatU hk) he⟩

/-! ## A3 (rank). `L_g = 𝒪 α` and a `ℚ`-basis of `B` spanning `L_g` over `ℤ` -/

/-- **`L_g = 𝒪 α`** with `nrd α ≠ 0`, from class number one (`classNumberOneB_proof`) and A2, A4. -/
theorem latticeAt_eq_O_mul (g : BAQˣ) : ∃ α : LeafQM.B, ShimuraGlue.nrdQ ℚ α ≠ 0 ∧
    latticeAt g = (fun b => b * α) '' {b | InO b} := by
  obtain ⟨γ, hγ, u, hu, hg⟩ := classNumberOneB_proof g
  refine ⟨binv γ, nrd_ne_zero_of_mul (binv_mul hγ), ?_⟩
  rw [latticeAt_dc_of_OhatU (g := 1) hγ hu (by rw [hg, Units.val_one, mul_one]), latticeAt_one]

/-- The basis `1, i, (1+j)/2, (i+k)/2` of `𝒪`. -/
def oVec (i : Fin 4) : LeafQM.B := LeafQM.ofInt (Pi.single i 1)

theorem ofInt_eq_sum (n : Fin 4 → ℤ) : LeafQM.ofInt n = ∑ i, ((n i : ℤ) : ℚ) • oVec i := by
  simp only [oVec, Fin.sum_univ_four]
  ext <;> simp [LeafQM.ofInt] <;> ring

theorem eq_sum_oVec (y : LeafQM.B) : y = ∑ i, cQ y i • oVec i := by
  simp only [oVec, Fin.sum_univ_four]
  ext <;> simp [LeafQM.ofInt, cQ] <;> ring

theorem oVec_linearIndependent : LinearIndependent ℚ oVec := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [oVec, Fin.sum_univ_four] at hc
  have h0 := congrArg QuaternionAlgebra.re hc
  have h1 := congrArg QuaternionAlgebra.imI hc
  have h2 := congrArg QuaternionAlgebra.imJ hc
  have h3 := congrArg QuaternionAlgebra.imK hc
  simp [LeafQM.ofInt] at h0 h1 h2 h3
  intro i
  fin_cases i <;> simp <;> linarith

/-- **A3 (rank). `L_g` is a full `ℤ`-lattice in `B`**: there are `e₀, …, e₃ ∈ B`, linearly independent
over `ℚ` and spanning `B` over `ℚ`, with `L_g = ℤe₀ ⊕ ℤe₁ ⊕ ℤe₂ ⊕ ℤe₃`. -/
theorem latticeAt_basis (g : BAQˣ) : ∃ e : Fin 4 → LeafQM.B,
    LinearIndependent ℚ e ∧ Submodule.span ℚ (Set.range e) = ⊤ ∧
    latticeAt g = {x | ∃ n : Fin 4 → ℤ, x = ∑ i, ((n i : ℤ) : ℚ) • e i} := by
  obtain ⟨α, hα, hL⟩ := latticeAt_eq_O_mul g
  have hmul : ∀ c : Fin 4 → ℚ, ∑ i, c i • (oVec i * α) = (∑ i, c i • oVec i) * α := by
    intro c
    rw [Finset.sum_mul]
    simp only [smul_mul_assoc]
  refine ⟨fun i => oVec i * α, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [hmul] at hc
    have h2 : ∑ i, c i • oVec i = 0 := by
      have := congrArg (· * binv α) hc
      simp only [mul_assoc, mul_binv hα, mul_one, zero_mul] at this
      exact this
    exact (Fintype.linearIndependent_iff.1 oVec_linearIndependent) c h2
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, cQ (x * binv α) i • (oVec i * α) := by
      rw [hmul, ← eq_sum_oVec, mul_assoc, binv_mul hα, mul_one]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hL]
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [hmul, ← ofInt_eq_sum]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨LeafQM.ofInt n, ⟨n, rfl⟩, by rw [hmul, ← ofInt_eq_sum]⟩

end Y3Lattice412
