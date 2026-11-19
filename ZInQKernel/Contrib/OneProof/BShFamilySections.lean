import ZInQKernel.Contrib.OneProof.BShTracesMeromorphic
import ZInQKernel.Contrib.OneProof.BShStandardWeber

/-! ON THE SPOT (provenance (c)): a modular change of basis realizes every
nonzero prime torsion section as the fixed Weber mark in another basis. -/

noncomputable section

namespace BShFamily

open Complex UpperHalfPlane Filter PeriodPair T5Glue X1Igusa.Weber BShTraces
open scoped MatrixGroups Topology Pointwise

/-- The complex Möbius reparametrization associated to an integral matrix. -/
def mobius (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))

/-- The homothety taking the transformed lattice to the original lattice. -/
def factor (g : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  (g 1 0 : ℂ) * τ + (g 1 1 : ℂ)

theorem factor_ne (g : SL(2, ℤ)) (τ : ℍ) : factor g τ ≠ 0 := by
  simpa [factor, UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL] using
    UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) τ

theorem coe_smul_eq_mobius (g : SL(2, ℤ)) (τ : ℍ) : ↑(g • τ) = mobius g τ := by
  rw [coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast, mobius]

theorem scale_smul (g : SL(2, ℤ)) (τ : ℍ) :
    IsScale (pp τ) (pp (g • τ)) (factor g τ) := by
  have hm : factor g τ * (↑(g • τ) : ℂ) = (g 0 0 : ℂ) * τ + (g 0 1 : ℂ) := by
    rw [coe_smul_eq_mobius]
    exact mul_div_cancel₀ _ (factor_ne g τ)
  refine ⟨factor_ne g τ, ?_⟩
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hdC : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast hd
  ext z
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, pp]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨_, ⟨m * g 0 0 - n * g 0 1, n * g 1 1 - m * g 1 0, rfl⟩, ?_⟩
    simp only [Int.cast_sub, Int.cast_mul, mul_one, mul_add]
    rw [show factor g τ * (((n : ℂ) * (g 1 1 : ℂ) - (m : ℂ) * (g 1 0 : ℂ)) * (↑(g • τ) : ℂ)) =
      ((n : ℂ) * (g 1 1 : ℂ) - (m : ℂ) * (g 1 0 : ℂ)) *
        (factor g τ * (↑(g • τ) : ℂ)) by ring, hm]
    unfold factor
    linear_combination ((m : ℂ) + (n : ℂ) * τ) * hdC
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    refine ⟨m * g 1 1 + n * g 0 1, m * g 1 0 + n * g 0 0, ?_⟩
    simp only [Int.cast_add, Int.cast_mul, mul_one, mul_add]
    rw [show factor g τ * ((n : ℂ) * (↑(g • τ) : ℂ)) =
      (n : ℂ) * (factor g τ * (↑(g • τ) : ℂ)) by ring, hm]
    unfold factor
    ring

theorem mobius_analyticAt (g : SL(2, ℤ)) (τ : ℍ) :
    AnalyticAt ℂ (mobius g) (τ : ℂ) := by
  unfold mobius
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const) (factor_ne g τ)

/-- The affine x-coordinate in the normalized short curve. -/
def normX (τ : ℍ) (z : ℂ) : ℂ :=
  (pp τ).g₂ / (pp τ).g₃ * (pp τ).weierstrassP z

theorem normX_period (τ : ℍ) (z : ℂ) (l : (pp τ).lattice) :
    normX τ (z + l) = normX τ z := by
  rw [normX, (pp τ).weierstrassP_add_coe, normX]

theorem normX_scale_smul (g : SL(2, ℤ)) (τ : ℍ) (z : ℂ) :
    normX τ (factor g τ * z) = normX (g • τ) z := by
  let h := scale_smul g τ
  have hc := factor_ne g τ
  unfold normX
  rw [h.g₂, h.g₃, h.weierstrassP]
  by_cases hz : (pp (g • τ)).g₃ = 0
  · simp only [hz, mul_zero, div_zero, zero_mul]
  field_simp [hc, hz]
  <;> ring

/-- A meromorphic representative of the normalized torsion x-coordinate in the
original lattice, with the section obtained by applying the matrix to the mark. -/
def mobiusX (p : ℕ) (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (G2f / G3f * Pf p) (mobius g z)

theorem mobiusX_meromorphicAt {p : ℕ} (hp : 2 ≤ p) (g : SL(2, ℤ)) (τ : ℍ) :
    MeromorphicAt (mobiusX p g) (τ : ℂ) := by
  have hw : mobius g (τ : ℂ) ∈ Hs := by
    rw [← coe_smul_eq_mobius]
    exact (g • τ).coe_im_pos
  have h₂ := diffOn_G2f.analyticOnNhd isOpen_Hs _ hw
  have h₃ := diffOn_G3f.analyticOnNhd isOpen_Hs _ hw
  have hP := (diffOn_Pf hp).analyticOnNhd isOpen_Hs _ hw
  have hm := mobius_analyticAt g τ
  exact ((h₂.comp hm).meromorphicAt.div (h₃.comp hm).meromorphicAt).mul
    (hP.comp hm).meromorphicAt

theorem mobiusX_eq_normX (p : ℕ) (g : SL(2, ℤ)) (τ : ℍ) :
    mobiusX p g τ = normX τ (factor g τ * (1 / (p : ℂ))) := by
  rw [normX_scale_smul]
  simp [mobiusX, ← coe_smul_eq_mobius, normX, G2f, G3f, Pf, ofComplex_apply]

/-- A choice of direction: horizontal or indexed by the slope of a triangular branch. -/
abbrev Line (p : ℕ) := Option (Fin p)

/-- Nonzero multiples of a generator of a prime kernel. -/
abbrev Multiple (p : ℕ) := {k : Fin p // k.val ≠ 0}

/-- The affine section giving the generator of the corresponding prime kernel. -/
def generator (p : ℕ) (i : Line p) (z : ℂ) : ℂ :=
  i.elim (1 / (p : ℂ)) fun j => (z + (j.val : ℂ)) / p

/-- Bezout produces an integral basis whose transformed mark represents the
chosen multiple, up to an original period. -/
theorem exists_matrix {p : ℕ} (hp : p.Prime) (i : Line p) (k : Multiple p) :
    ∃ g : SL(2, ℤ), ∀ τ : ℍ,
      factor g τ * (1 / (p : ℂ)) - (k.val.val : ℂ) * generator p i τ ∈ (pp τ).lattice := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hk : 0 < k.val.val := Nat.pos_of_ne_zero k.property
  have hc : p.Coprime k.val.val :=
    hp.coprime_iff_not_dvd.mpr (fun hd => (not_lt_of_ge (Nat.le_of_dvd hk hd)) k.val.isLt)
  rcases i with _ | i
  · have hci : IsCoprime (p : ℤ) (k.val.val : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hc)
    obtain ⟨g, hg, hg'⟩ := hci.exists_SL2_row 1
    have hgC : (g 1 0 : ℂ) = (p : ℂ) := by exact_mod_cast hg
    have hgC' : (g 1 1 : ℂ) = (k.val.val : ℂ) := by exact_mod_cast hg'
    refine ⟨g, fun τ => PeriodPair.mem_lattice.mpr ⟨0, 1, ?_⟩⟩
    simp only [pp, generator, Option.elim_none, factor, hgC, hgC',
      Int.cast_one, Int.cast_zero, mul_one, one_mul, zero_add]
    field_simp
    <;> ring
  · have hc' : Nat.Coprime k.val.val (p + k.val.val * i.val) :=
      by simpa only [Nat.mul_comm i.val k.val.val] using
        (Nat.coprime_add_mul_right_right k.val.val p i.val).mpr hc.symm
    have hci : IsCoprime (k.val.val : ℤ) ((p + k.val.val * i.val : ℕ) : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hc')
    obtain ⟨g, hg, hg'⟩ := hci.exists_SL2_row 1
    have hgC : (g 1 0 : ℂ) = (k.val.val : ℂ) := by exact_mod_cast hg
    have hgC' : (g 1 1 : ℂ) = (p : ℂ) + (k.val.val : ℂ) * (i.val : ℂ) := by exact_mod_cast hg'
    refine ⟨g, fun τ => PeriodPair.mem_lattice.mpr ⟨1, 0, ?_⟩⟩
    simp only [pp, generator, Option.elim_some, factor, hgC, hgC',
      Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero]
    field_simp
    <;> ring

/-- Every nonzero multiple of each prime generator has a meromorphic x-section
at every parameter, including at an exceptional parameter. -/
theorem exists_torsion_section {p : ℕ} (hp : p.Prime) (i : Line p) (k : Multiple p)
    (τ : ℍ) :
    ∃ r : MeromorphicGerm (τ : ℂ),
      meromorphicIncl _ r =
        ((fun z : ℂ => normX (ofComplex z) ((k.val.val : ℂ) * generator p i z)) :
          ShimuraPointDict.PuncturedGerm (τ : ℂ)) := by
  obtain ⟨g, hg⟩ := exists_matrix hp i k
  refine ⟨⟨(mobiusX p g : ShimuraPointDict.PuncturedGerm (τ : ℂ)),
    ⟨mobiusX p g, rfl, mobiusX_meromorphicAt hp.two_le g τ⟩⟩, ?_⟩
  apply Germ.coe_eq.mpr
  filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds τ.coe_im_pos)] with z hz
  have hz' : (↑(ofComplex z) : ℂ) = z := ofComplex_coe hz
  let s := ofComplex z
  change (s : ℂ) = z at hz'
  let w := (k.val.val : ℂ) * generator p i (s : ℂ)
  let a := factor g s * (1 / (p : ℂ))
  change mobiusX p g z = normX s ((k.val.val : ℂ) * generator p i z)
  calc
    mobiusX p g z = normX s a := by
      simpa only [hz'] using mobiusX_eq_normX p g s
    _ = normX s (w + (a - w)) := by congr 1 <;> ring
    _ = normX s w := normX_period s w ⟨_, hg s⟩
    _ = _ := by change normX s ((k.val.val : ℂ) * generator p i (s : ℂ)) = _; rw [hz']

#print axioms factor_ne
#print axioms coe_smul_eq_mobius
#print axioms scale_smul
#print axioms mobius_analyticAt
#print axioms normX_period
#print axioms normX_scale_smul
#print axioms mobiusX_meromorphicAt
#print axioms mobiusX_eq_normX
#print axioms exists_matrix
#print axioms exists_torsion_section

end BShFamily
