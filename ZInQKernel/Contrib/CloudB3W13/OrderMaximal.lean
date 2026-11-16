/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.Contrib.CloudB3W13.Source.Definitions.Def_QuaternionAlgebra_EichlerOrder

/-!
# W13 order bridge (1): the kernel's order `𝒪` is a maximal order of `ℍ[ℚ, 2, -3]`

`LeafQM.O` (`ZInQKernel/HDecomp/QM/Structures.lean`, unchanged) is the subring
`ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of `LeafQM.B = QuaternionAlgebra ℚ 2 0 (-3) = ℍ[ℚ, 2, -3]`.
Here it is viewed as a `ℤ`-submodule (`oLattice`) and shown to satisfy the vendored
Anthropic-FLT predicate `ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsMaximalOrder` (`Def_QuaternionAlgebra_EichlerOrder`).

Proof: every element `y` of any order has integral reduced trace `2·re y` and reduced norm
`re² - 2 imI² + 3 imJ² - 6 imK²` (it is integral over `ℤ`, and Gauss's lemma applies to its
quadratic relation). For `x` in an order containing `𝒪`, the traces of `x, x·i, x·j, x·k,
x·(1+j)/2, x·(i+k)/2` and the norm of `x` are integers; the congruence lemma
`int_conditions` (checked modulo 3 and modulo 8) then puts `x` in `𝒪`. The dual lattice of `𝒪`
for the trace form has index 36 = 6², and the norm is non-integral on each of its 35 nonzero
classes.
-/

open scoped Quaternion
open Polynomial

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura

open LeafQM

/-- The kernel's order `𝒪 = LeafQM.O` as a `ℤ`-lattice in `ℍ[ℚ, 2, -3]`. -/
def oLattice : Submodule ℤ ℍ[ℚ, 2, -3] := LeafQM.O.toAddSubgroup.toIntSubmodule

theorem mem_oLattice {x : ℍ[ℚ, 2, -3]} : x ∈ oLattice ↔ x ∈ LeafQM.O := Iff.rfl

theorem ofInt_mem (n : Fin 4 → ℤ) : ofInt n ∈ oLattice := ⟨n, rfl⟩

/-- `ℤ`-span presentation of `oLattice`. -/
theorem oLattice_eq_span :
    oLattice = Submodule.span ℤ {ofInt ![1, 0, 0, 0], ofInt ![0, 1, 0, 0], ofInt ![0, 0, 1, 0],
      ofInt ![0, 0, 0, 1]} := by
  apply le_antisymm
  · rintro x ⟨n, rfl⟩
    have h : ofInt n = n 0 • ofInt ![1, 0, 0, 0] + n 1 • ofInt ![0, 1, 0, 0] +
        n 2 • ofInt ![0, 0, 1, 0] + n 3 • ofInt ![0, 0, 0, 1] := by
      ext <;> simp [ofInt] <;> ring
    rw [h]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ofInt_mem _

theorem oLattice_isOrder : ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsOrder oLattice where
  one_mem := LeafQM.O.one_mem
  mul_mem := fun _ _ hx hy => LeafQM.O.mul_mem hx hy
  spanTop := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = x.re • ofInt ![1, 0, 0, 0] + x.imI • ofInt ![0, 1, 0, 0] +
        x.imJ • ofInt ![-1, 0, 2, 0] + x.imK • ofInt ![0, -1, 0, 2] := by
      ext <;> simp [ofInt]
    rw [hx]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (ofInt_mem _))
  fg := by
    rw [oLattice_eq_span]
    exact Submodule.fg_span (Set.toFinite _)

/-- The reduced norm of `ℍ[ℚ, 2, -3]` in coordinates. -/
def nrd (y : ℍ[ℚ, 2, -3]) : ℚ := y.re ^ 2 - 2 * y.imI ^ 2 + 3 * y.imJ ^ 2 - 6 * y.imK ^ 2

/-- The quadratic relation `y² - (2 re y) y + nrd y = 0`. -/
theorem aeval_charpoly (y : ℍ[ℚ, 2, -3]) :
    aeval y (X ^ 2 - C (2 * y.re) * X + C (nrd y)) = 0 := by
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    QuaternionAlgebra.coe_algebraMap]
  ext <;> simp [nrd, pow_two, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

theorem charpoly_monic (t n : ℚ) : (X ^ 2 - C t * X + C n : ℚ[X]).Monic := by
  have : (X ^ 2 - C t * X + C n : ℚ[X]) = X ^ 2 + (C (-t) * X + C n) := by
    simp only [map_neg, neg_mul]; ring
  rw [this]
  refine monic_X_pow_add ?_
  exact lt_of_le_of_lt degree_linear_le (by norm_num)

theorem charpoly_natDegree (t n : ℚ) : (X ^ 2 - C t * X + C n : ℚ[X]).natDegree = 2 := by
  compute_degree!

/-- **Integrality of reduced trace and norm on an order.** -/
theorem trd_nrd_int {Λ' : Submodule ℤ ℍ[ℚ, 2, -3]} (h : ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsOrder Λ')
    {y : ℍ[ℚ, 2, -3]} (hy : y ∈ Λ') : (∃ t : ℤ, 2 * y.re = t) ∧ (∃ n : ℤ, nrd y = n) := by
  let S : Subalgebra ℤ ℍ[ℚ, 2, -3] :=
    { carrier := Λ'
      mul_mem' := fun ha hb => h.mul_mem ha hb
      one_mem' := h.one_mem
      add_mem' := fun ha hb => Λ'.add_mem ha hb
      zero_mem' := Λ'.zero_mem
      algebraMap_mem' := fun z => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Λ'.smul_mem z h.one_mem }
  have hS : Subalgebra.toSubmodule S = Λ' := Submodule.ext fun _ => Iff.rfl
  have hint : IsIntegral ℤ y := IsIntegral.of_mem_of_fg S (hS ▸ h.fg) y hy
  by_cases hsc : y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0
  · obtain ⟨h1, h2, h3⟩ := hsc
    let f : ℚ →ₐ[ℤ] ℍ[ℚ, 2, -3] := (Algebra.ofId ℚ ℍ[ℚ, 2, -3]).restrictScalars ℤ
    have hf : Function.Injective f := by
      intro r s hrs
      have := congrArg QuaternionAlgebra.re hrs
      simpa [f, QuaternionAlgebra.coe_algebraMap] using this
    have hyf : f y.re = y := by
      ext <;> simp [f, QuaternionAlgebra.coe_algebraMap, h1, h2, h3]
    have hre : IsIntegral ℤ y.re := (isIntegral_algHom_iff f hf).mp (hyf ▸ hint)
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hre
    simp only [algebraMap_int_eq, eq_intCast] at hz
    refine ⟨⟨2 * z, by rw [← hz]; push_cast; ring⟩, ⟨z ^ 2, ?_⟩⟩
    simp [nrd, h1, h2, h3, ← hz]
  · obtain ⟨p, hpm, hp⟩ := hint
    set t := 2 * y.re
    set n := nrd y
    set q : ℚ[X] := X ^ 2 - C t * X + C n with hqdef
    have hqm : q.Monic := charpoly_monic t n
    have hqd : q.natDegree = 2 := charpoly_natDegree t n
    have hq1 : q ≠ 1 := by intro h1; rw [h1, natDegree_one] at hqd; norm_num at hqd
    set P : ℚ[X] := p.map (algebraMap ℤ ℚ)
    have hP : aeval y P = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    set r := P %ₘ q
    have hr : aeval y r = 0 := by
      have h0 := modByMonic_add_div P q
      have h1 : aeval y q = 0 := aeval_charpoly y
      have := congrArg (aeval y) h0
      rw [map_add, map_mul, h1, zero_mul, add_zero, hP] at this
      exact this
    have hrd : r.natDegree ≤ 1 := by
      have : r.natDegree < q.natDegree := natDegree_modByMonic_lt P hqm hq1
      omega
    have hrlin := eq_X_add_C_of_natDegree_le_one hrd
    rw [hrlin] at hr
    simp only [map_add, map_mul, aeval_X, aeval_C, QuaternionAlgebra.coe_algebraMap] at hr
    have hI := congrArg QuaternionAlgebra.imI hr
    have hJ := congrArg QuaternionAlgebra.imJ hr
    have hK := congrArg QuaternionAlgebra.imK hr
    have hR := congrArg QuaternionAlgebra.re hr
    simp at hI hJ hK hR
    have hα : r.coeff 1 = 0 := by
      by_contra hne
      apply hsc
      refine ⟨?_, ?_, ?_⟩
      · rcases hI with h | h
        · exact absurd h hne
        · exact h
      · rcases hJ with h | h
        · exact absurd h hne
        · exact h
      · rcases hK with h | h
        · exact absurd h hne
        · exact h
    have hβ : r.coeff 0 = 0 := by rw [hα] at hR; simpa using hR
    have hr0 : r = 0 := by rw [hrlin, hα, hβ]; simp
    have hdvd : q ∣ P := (modByMonic_eq_zero_iff_dvd hqm).mp hr0
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hpm hdvd
    rw [hqm.leadingCoeff, C_1, mul_one] at hg
    have c1 : q.coeff 1 = -t := by simp [hqdef, coeff_X, coeff_C]
    have c0 : q.coeff 0 = n := by simp [hqdef, coeff_X, coeff_C]
    rw [← hg, coeff_map] at c1 c0
    simp only [algebraMap_int_eq, eq_intCast] at c1 c0
    exact ⟨⟨-g.coeff 1, by push_cast; linarith⟩, ⟨g.coeff 0, c0.symm⟩⟩

/-- **The congruence core.** -/
theorem int_conditions (A B C D : ℤ) (h1 : 2 ∣ A - C) (h2 : 2 ∣ B - D)
    (h3 : 24 ∣ 6 * A ^ 2 - 3 * B ^ 2 + 2 * C ^ 2 - D ^ 2) :
    3 ∣ C ∧ 6 ∣ D ∧ 6 ∣ 3 * A - C ∧ 12 ∣ 3 * B - D := by
  have m3 : ∀ c d : ZMod 3, 2 * c ^ 2 - d ^ 2 = 0 → c = 0 ∧ d = 0 := by decide
  have m8a : ∀ a c : ZMod 8, 4 * (a - c) = 0 → 6 * a ^ 2 + 2 * c ^ 2 = 0 := by decide
  have m8b : ∀ b d : ZMod 8, 4 * (b - d) = 0 → -3 * b ^ 2 - d ^ 2 = 0 →
      2 * (3 * b - d) = 0 ∧ 4 * d = 0 := by decide
  have h3' : (3 : ℤ) ∣ 6 * A ^ 2 - 3 * B ^ 2 + 2 * C ^ 2 - D ^ 2 := dvd_trans (by norm_num) h3
  have h8' : (8 : ℤ) ∣ 6 * A ^ 2 - 3 * B ^ 2 + 2 * C ^ 2 - D ^ 2 := dvd_trans (by norm_num) h3
  -- modulo 3
  have e3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3'
  push_cast at e3
  have e3' : 2 * (C : ZMod 3) ^ 2 - (D : ZMod 3) ^ 2 = 0 := by
    have h6 : (6 : ZMod 3) = 0 := by decide
    have h33 : (3 : ZMod 3) = 0 := by decide
    rw [h6, h33] at e3; linear_combination e3
  obtain ⟨c3, d3⟩ := m3 _ _ e3'
  have hC3 : (3 : ℤ) ∣ C := (ZMod.intCast_zmod_eq_zero_iff_dvd C 3).mp c3
  have hD3 : (3 : ℤ) ∣ D := (ZMod.intCast_zmod_eq_zero_iff_dvd D 3).mp d3
  -- modulo 8
  have e8 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h8'
  push_cast at e8
  have p1 : 4 * ((A : ZMod 8) - C) = 0 := by
    obtain ⟨k, hk⟩ := h1
    have : (4 : ℤ) * (A - C) = 8 * k := by rw [hk]; ring
    have := congrArg (fun z : ℤ => (z : ZMod 8)) this
    push_cast at this
    rw [this, show (8 : ZMod 8) = 0 from rfl, zero_mul]
  have p2 : 4 * ((B : ZMod 8) - D) = 0 := by
    obtain ⟨k, hk⟩ := h2
    have : (4 : ℤ) * (B - D) = 8 * k := by rw [hk]; ring
    have := congrArg (fun z : ℤ => (z : ZMod 8)) this
    push_cast at this
    rw [this, show (8 : ZMod 8) = 0 from rfl, zero_mul]
  have hac := m8a _ _ p1
  have hbd : -3 * (B : ZMod 8) ^ 2 - (D : ZMod 8) ^ 2 = 0 := by linear_combination e8 - hac
  obtain ⟨q1, q2⟩ := m8b _ _ p2 hbd
  have hBD8 : (8 : ℤ) ∣ 2 * (3 * B - D) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact q1)
  have hD8 : (8 : ℤ) ∣ 4 * D :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact q2)
  have hBD4 : (4 : ℤ) ∣ 3 * B - D := by
    obtain ⟨k, hk⟩ := hBD8; exact ⟨k, by linarith⟩
  have hD2 : (2 : ℤ) ∣ D := by
    obtain ⟨k, hk⟩ := hD8; exact ⟨k, by linarith⟩
  refine ⟨hC3, ?_, ?_, ?_⟩
  · exact IsCoprime.mul_dvd (show IsCoprime (2 : ℤ) 3 by norm_num [Int.isCoprime_iff_gcd_eq_one])
      hD2 hD3 |> fun h => by simpa using h
  · have h2' : (2 : ℤ) ∣ 3 * A - C := by
      obtain ⟨k, hk⟩ := h1; exact ⟨A + k, by linarith⟩
    have h3'' : (3 : ℤ) ∣ 3 * A - C := dvd_sub (dvd_mul_right 3 A) hC3
    exact IsCoprime.mul_dvd (show IsCoprime (2 : ℤ) 3 by norm_num [Int.isCoprime_iff_gcd_eq_one])
      h2' h3'' |> fun h => by simpa using h
  · have h3'' : (3 : ℤ) ∣ 3 * B - D := dvd_sub (dvd_mul_right 3 B) hD3
    exact IsCoprime.mul_dvd (show IsCoprime (4 : ℤ) 3 by norm_num [Int.isCoprime_iff_gcd_eq_one])
      hBD4 h3'' |> fun h => by simpa using h

/-- **`𝒪` is a maximal order of `ℍ[ℚ, 2, -3]`** (vendored Anthropic-FLT predicate). -/
theorem oLattice_isMaximalOrder : ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsMaximalOrder oLattice := by
  refine ⟨oLattice_isOrder, fun Λ' hΛ' hle => le_antisymm (fun x hx => ?_) hle⟩
  have mem : ∀ v : Fin 4 → ℤ, ofInt v ∈ Λ' := fun v => hle (ofInt_mem v)
  obtain ⟨⟨A, hA⟩, ⟨N, hN⟩⟩ := trd_nrd_int hΛ' hx
  obtain ⟨⟨B, hB⟩, -⟩ := trd_nrd_int hΛ' (hΛ'.mul_mem hx (mem ![0, 1, 0, 0]))
  obtain ⟨⟨C', hC⟩, -⟩ := trd_nrd_int hΛ' (hΛ'.mul_mem hx (mem ![-1, 0, 2, 0]))
  obtain ⟨⟨D, hD⟩, -⟩ := trd_nrd_int hΛ' (hΛ'.mul_mem hx (mem ![0, -1, 0, 2]))
  obtain ⟨⟨P, hP⟩, -⟩ := trd_nrd_int hΛ' (hΛ'.mul_mem hx (mem ![0, 0, 1, 0]))
  obtain ⟨⟨Q, hQ⟩, -⟩ := trd_nrd_int hΛ' (hΛ'.mul_mem hx (mem ![0, 0, 0, 1]))
  simp [ofInt] at hB hC hD hP hQ
  simp only [nrd] at hN
  -- `A = 2a`, `B = 4b`, `C = -C' = 6c`, `D = 12d`, `P = a - 3c`, `Q = 2b + 6d`, `N = nrd x`
  have i1 : (2 : ℤ) ∣ A - (-C') := ⟨P, by
    have : ((A - (-C') : ℤ) : ℚ) = ((2 * P : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this⟩
  have i2 : (2 : ℤ) ∣ B - D := ⟨Q - D, by
    have : ((B - D : ℤ) : ℚ) = ((2 * (Q - D) : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this⟩
  have i3 : (24 : ℤ) ∣ 6 * A ^ 2 - 3 * B ^ 2 + 2 * (-C') ^ 2 - D ^ 2 := ⟨N, by
    have : ((6 * A ^ 2 - 3 * B ^ 2 + 2 * (-C') ^ 2 - D ^ 2 : ℤ) : ℚ) = ((24 * N : ℤ) : ℚ) := by
      push_cast; rw [← hA, ← hB, ← hC, ← hD, ← hN]; ring
    exact_mod_cast this⟩
  obtain ⟨⟨k2, hk2⟩, ⟨k3, hk3⟩, ⟨k0, hk0⟩, ⟨k1, hk1⟩⟩ := int_conditions A B (-C') D i1 i2 i3
  refine ⟨![k0, k1, k2, k3], ?_⟩
  have qk2 : ((-C' : ℤ) : ℚ) = 3 * k2 := by exact_mod_cast hk2
  have qk3 : ((D : ℤ) : ℚ) = 6 * k3 := by exact_mod_cast hk3
  have qk0 : ((3 * A - (-C') : ℤ) : ℚ) = 6 * k0 := by exact_mod_cast hk0
  have qk1 : ((3 * B - D : ℤ) : ℚ) = 12 * k1 := by exact_mod_cast hk1
  push_cast at qk2 qk3 qk0 qk1
  ext <;> simp [ofInt] <;> linarith

end ZInQ.Contrib.CloudB2Shimura
