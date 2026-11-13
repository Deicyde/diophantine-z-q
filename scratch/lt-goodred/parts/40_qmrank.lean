/-! ## lt-goodred §4: `QMEndRank` reduced to I3.M1, T27 and one algebraic glue Prop

* `rank ≥ 4` (proved, `four_le_finrank`): `𝒪 ≅ ℤ⁴` (`ofIntHom`) and `endBC ∘ endBC ∘ ι` is an
  injective ring map `𝒪 → End(A')`; `End(A')` is finite over `ℤ` by I3.M1.
* `rank ≤ rank End(A'_Ω)` (proved, `finrank_le_baseChange`): `endBC` is injective, I3.M1.
* T27 at `A'' = A'_Ω`, `Ω = \bar{L'}`: its hypotheses are proved here: `dim A'' = 2`
  (`pkgI3_dim_baseChange`, three times), `B = (2,−3)` is a division algebra (`quatB6_isUnit`: the
  norm form `x₀² − 2x₁² + 3x₂² − 6x₃²` is anisotropic over `ℚ`, 3-adic descent), and
  `B →ₐ[ℚ] End⁰(A'')` (`quatEmbed`, from `ι` and base change).
* Case `End⁰(A'') ≅ B`: `rank End(A'') = dim_ℚ End⁰(A'') = 4` (proved).
* Case `End⁰(A'') ≅ M₂(ℚ(√d))`, `d < 0`: the named glue Prop `QMSplitCaseRank`. -/

section LTQMRankSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField LeafQM
open scoped Quaternion TensorProduct

/-! ### `𝒪 ≅ ℤ⁴` and the lower bound -/

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [ofInt] at h0 h1 h2 h3
  have e2 : (n 2 : ℚ) = m 2 := by linarith
  have e3 : (n 3 : ℚ) = m 3 := by linarith
  have e0 : (n 0 : ℚ) = m 0 := by linarith
  have e1 : (n 1 : ℚ) = m 1 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

/-- `n ↦ ofInt n`, an additive bijection `ℤ⁴ → 𝒪`. -/
def ofIntHom : (Fin 4 → ℤ) →+ O where
  toFun n := ⟨ofInt n, n, rfl⟩
  map_zero' := Subtype.ext ofInt_zero
  map_add' n m := Subtype.ext (ofInt_add n m).symm

theorem ofIntHom_injective : Function.Injective ofIntHom :=
  fun n m h => ofInt_injective (congrArg Subtype.val h)

/-- **`rank End(A) ≥ 4` for a QM abelian variety** (proved; I3.M1 for finiteness). -/
theorem four_le_finrank (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k)
    (φ : O →+* PkgI3.AbVar.End A) (hφ : Function.Injective φ) :
    4 ≤ Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 k A A
  let F : (Fin 4 → ℤ) →+ PkgI3.AbVar.End A := φ.toAddMonoidHom.comp ofIntHom
  have hF : Function.Injective F := hφ.comp ofIntHom_injective
  have := LinearMap.finrank_le_finrank_of_injective (f := F.toIntLinearMap) hF
  rwa [Module.finrank_fin_fun] at this

/-- **`rank End(A) ≤ rank End(A_Ω)`** (proved; `endBC` is injective, I3.M1). -/
theorem finrank_le_baseChange (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k]
    (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [Algebra k Ω] :
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤
      Module.finrank ℤ (PkgI3.AbVar.End (A.baseChange Ω)) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (HSyn.LinkedTate.endBC A Ω).toAddMonoidHom.toIntLinearMap)
    (HSyn.LinkedTate.endBC_injective A Ω)

/-- `rank_ℤ End(A) = dim_ℚ End⁰(A)` (I3.M1: `End(A)` is free). -/
theorem finrank_end0 (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k) :
    Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨hfree, -, -, -⟩ := hM1 k A A
  exact Module.finrank_baseChange

/-! ### `B = (2, −3)` is a division algebra -/

theorem mod3_step (a b e : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * e = 0) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hc := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at hc
  have h' : ((a : ZMod 3)) ^ 2 + ((b : ZMod 3)) ^ 2 = 0 := by
    linear_combination hc + ((b : ZMod 3) ^ 2 - (e : ZMod 3)) * h3
  have key : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  obtain ⟨ha, hb⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb⟩

theorem pow3_dvd (k : ℕ) : ∀ a b c d : ℤ, a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 →
    3 ^ k ∣ a ∧ 3 ^ k ∣ b ∧ 3 ^ k ∣ c ∧ 3 ^ k ∣ d := by
  induction k with
  | zero => intro a b c d _; simp
  | succ k ih =>
    intro a b c d h
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := mod3_step a b (c ^ 2 - 2 * d ^ 2) (by linear_combination h)
    have h' : (3 : ℤ) * (c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2)) = 0 := by
      linear_combination h
    obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := mod3_step c d (a' ^ 2 - 2 * b' ^ 2)
      ((mul_eq_zero.mp h').resolve_left (by norm_num))
    have h'' : (9 : ℤ) * (a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2) = 0 := by
      linear_combination h
    obtain ⟨h1, h2, h3, h4⟩ := ih a' b' c' d' ((mul_eq_zero.mp h'').resolve_left (by norm_num))
    rw [pow_succ']
    exact ⟨mul_dvd_mul_left 3 h1, mul_dvd_mul_left 3 h2, mul_dvd_mul_left 3 h3,
      mul_dvd_mul_left 3 h4⟩

theorem eq_zero_of_pow3_dvd (a : ℤ) (h : ∀ k : ℕ, 3 ^ k ∣ a) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h a.natAbs)
  rw [Int.natAbs_pow]
  exact Nat.lt_pow_self (by norm_num)

/-- The norm form of `B` is anisotropic over `ℤ`. -/
theorem norm6_int (a b c d : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨eq_zero_of_pow3_dvd a fun k => (pow3_dvd k a b c d h).1,
    eq_zero_of_pow3_dvd b fun k => (pow3_dvd k a b c d h).2.1,
    eq_zero_of_pow3_dvd c fun k => (pow3_dvd k a b c d h).2.2.1,
    eq_zero_of_pow3_dvd d fun k => (pow3_dvd k a b c d h).2.2.2⟩

/-- The norm form of `B` is anisotropic over `ℚ`. -/
theorem norm6_rat (q0 q1 q2 q3 : ℚ) (h : q0 ^ 2 - 2 * q1 ^ 2 + 3 * q2 ^ 2 - 6 * q3 ^ 2 = 0) :
    q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  have hd0 : (q0.den : ℚ) ≠ 0 := by exact_mod_cast q0.den_nz
  have hd1 : (q1.den : ℚ) ≠ 0 := by exact_mod_cast q1.den_nz
  have hd2 : (q2.den : ℚ) ≠ 0 := by exact_mod_cast q2.den_nz
  have hd3 : (q3.den : ℚ) ≠ 0 := by exact_mod_cast q3.den_nz
  set D : ℚ := q0.den * q1.den * q2.den * q3.den with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 hd1) hd2) hd3
  have e0 : ((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ) = q0 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q0]; ring
  have e1 : ((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ) = q1 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q1]; ring
  have e2 : ((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ) = q2 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q2]; ring
  have e3 : ((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ) = q3 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q3]; ring
  have hZ := norm6_int (q0.num * q1.den * q2.den * q3.den) (q1.num * q0.den * q2.den * q3.den)
    (q2.num * q0.den * q1.den * q3.den) (q3.num * q0.den * q1.den * q2.den) (by
      have : (((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          - 2 * (((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          + 3 * (((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ)) ^ 2
          - 6 * (((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ)) ^ 2 = 0 := by
        rw [e0, e1, e2, e3]; linear_combination D ^ 2 * h
      exact_mod_cast this)
  obtain ⟨z0, z1, z2, z3⟩ := hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e0; rw [z0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e1; rw [z1, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e2; rw [z2, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e3; rw [z3, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0

/-- **`B = (2,−3)_ℚ` is a division algebra** (proved): `x · x̄ = n(x)` with `n` anisotropic. -/
theorem quatB6_isUnit : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x := by
  intro x hx
  have hn : (x * star x).re = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
    simp [QuaternionAlgebra.re_mul]; ring
  have hn0 : (x * star x).re ≠ 0 := by
    intro h0
    rw [hn] at h0
    obtain ⟨z0, z1, z2, z3⟩ := norm6_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext z0 z1 z2 z3)
  set n := (x * star x).re with hndef
  have hxs : x * star x = (n : ℍ[ℚ, 2, -3]) := QuaternionAlgebra.mul_star_eq_coe x
  have hsx : star x * x = (n : ℍ[ℚ, 2, -3]) := by rw [← hxs]; exact (star_comm_self' x)
  have hinv : (n⁻¹ : ℚ) • (n : ℍ[ℚ, 2, -3]) = 1 := by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hn0,
      QuaternionAlgebra.coe_one]
  refine isUnit_iff_exists.mpr ⟨n⁻¹ • star x, ?_, ?_⟩
  · rw [mul_smul_comm, hxs, hinv]
  · rw [smul_mul_assoc, hsx, hinv]

/-! ### `B →ₐ[ℚ] End⁰(A)` from a QM structure -/

/-- `i ∈ 𝒪`. -/
def oI' : O := ⟨ofInt ![0, 1, 0, 0], _, rfl⟩
/-- `j = 2·(1+j)/2 − 1 ∈ 𝒪`. -/
def oJ' : O := ⟨ofInt ![-1, 0, 2, 0], _, rfl⟩

theorem oI'_mul_oI' : oI' * oI' = 2 := by
  apply Subtype.ext
  show ofInt ![0, 1, 0, 0] * ofInt ![0, 1, 0, 0] = 2
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oJ' : oJ' * oJ' = -3 := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![-1, 0, 2, 0] = -3
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oI' : oJ' * oI' = -(oI' * oJ') := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![0, 1, 0, 0] = -(ofInt ![0, 1, 0, 0] * ofInt ![-1, 0, 2, 0])
  ext <;> simp [ofInt] <;> norm_num

/-- **`B →ₐ[ℚ] End⁰(A)` from a ring map `𝒪 → End(A)`** (proved: `i ↦ 1 ⊗ φ(i)`, `j ↦ 1 ⊗ φ(j)`,
Mathlib's `QuaternionAlgebra.Basis.liftHom`). -/
theorem quatEmbed {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : O →+* PkgI3.AbVar.End A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) := by
  let ψ : O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End0 A).toRingHom.comp φ
  refine ⟨QuaternionAlgebra.Basis.liftHom
    { i := ψ oI', j := ψ oJ', k := ψ oI' * ψ oJ',
      i_mul_i := ?_, j_mul_j := ?_, i_mul_j := rfl, j_mul_i := ?_ }⟩
  · rw [← map_mul, oI'_mul_oI', map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oJ', map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oI', map_neg, map_mul, zero_smul, zero_sub]

/-! ### The reduction -/

/-- **Glue (algebra; Albert's classification for simple abelian surfaces in characteristic 0,
Mumford §21, numbering UNVERIFIED): the split geometric case.** For an abelian surface `A` over a
field `k` of characteristic `0` with an injective ring map `ι : 𝒪 → End_k(A)` and `EndDivision A`,
if `End⁰(A_Ω) ≅ M₂(ℚ(√d))` (`d < 0`) for an algebraically closed `Ω ⊇ k`, then
`rank_ℤ End_k(A) ≤ 4`. Route (STANDARD): `End⁰(A)` embeds in `End⁰(A_Ω)` (`endBC`, flatness of
`ℚ/ℤ`) as a subalgebra `S ⊇ ι(B)`; `S` is a left `B`-vector space, so `dim_ℚ S ∈ {4, 8}`; if
`dim S = 8` then `S = M₂(ℚ(√d))` contains a nonzero nilpotent, whose integer multiple in
`End(A)` is a nonzero nilpotent endomorphism; a nilpotent endomorphism of a positive-dimensional
abelian variety is not surjective, contradicting `EndDivision`. GLUE. -/
def QMSplitCaseRank : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] (φ : O →+* PkgI3.AbVar.End A), Function.Injective φ → A.dim = 2 →
    PkgI3.EndDivision A → ∀ d : ℚ, d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤ 4

/-- **`QMEndRank`, proved** from the leaves I3.M1 (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3) and
T27 (`PkgI3.QMDichotomyYu`, Yu 2013 Thm 1.1) and the glue `QMSplitCaseRank`. -/
theorem qmEndRank_of (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu)
    (hS : QMSplitCaseRank) : HSyn.LinkedTate.QMEndRank := by
  intro K L L' _ hKL hLL' PK hdiv
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  set A' : PkgI3.AbVar L' := @PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL') with hA'
  let φ : O →+* PkgI3.AbVar.End A' :=
    (HSyn.LinkedTate.endBC (PK.A.baseChange L) L').comp
      ((HSyn.LinkedTate.endBC PK.A L).comp PK.q.iota)
  have hφ : Function.Injective φ :=
    (HSyn.LinkedTate.endBC_injective _ L').comp
      ((HSyn.LinkedTate.endBC_injective _ L).comp PK.q.injective)
  have hdimA' : A'.dim = 2 := by
    rw [hA', G0Dim.pkgI3_dim_baseChange, G0Dim.pkgI3_dim_baseChange]
    exact PK.surface
  refine le_antisymm ?_ (four_le_finrank hM1 A' φ hφ)
  -- the geometric endomorphism algebra
  let Ω := AlgebraicClosure L'
  let A'' : PkgI3.AbVar Ω := A'.baseChange Ω
  have hdimA'' : A''.dim = 2 := by
    show (A'.baseChange Ω).dim = 2
    rw [G0Dim.pkgI3_dim_baseChange]; exact hdimA'
  let φ'' : O →+* PkgI3.AbVar.End A'' := (HSyn.LinkedTate.endBC A' Ω).comp φ
  rcases hT27 Ω A'' hdimA'' 2 (-3) PkgI3.quatIndefinite_two_neg_three quatB6_isUnit
      (quatEmbed A'' φ'') with he | ⟨d, hd, he⟩
  · obtain ⟨e⟩ := he
    calc Module.finrank ℤ (PkgI3.AbVar.End A')
        ≤ Module.finrank ℤ (PkgI3.AbVar.End A'') := finrank_le_baseChange hM1 A' Ω
      _ = Module.finrank ℚ (PkgI3.AbVar.End0 A'') := (finrank_end0 hM1 A'').symm
      _ = Module.finrank ℚ ℍ[ℚ, 2, -3] := e.toLinearEquiv.finrank_eq
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  · exact hS L' A' Ω φ hφ hdimA' hdiv d hd he

end LTGoodRed.QM

end

end LTQMRankSec

#print axioms LTGoodRed.QM.quatB6_isUnit
#print axioms LTGoodRed.QM.quatEmbed
#print axioms LTGoodRed.QM.four_le_finrank
#print axioms LTGoodRed.QM.qmEndRank_of
