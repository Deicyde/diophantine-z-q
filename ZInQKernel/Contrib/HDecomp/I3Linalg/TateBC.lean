import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Finite
import ZInQKernel.HDecomp.Objects

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-I3-linalg/TateBC.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-
glue-I3-linalg: comparison of Tate modules along an injective map of groups (the algebraic core of
"`T_ℓ` under base change of the field"). Section 1 is copied verbatim from `scratch/pkg-I3/I3.lean`
(the Tate module `Tate.T ℓ M` of an abelian group, as a `ℤ_ℓ`-module); section 2 is new.
-/

noncomputable section
/-! §1 (pkg-I3's Tate module, copied verbatim in the draft) is imported from
`ZInQKernel.HDecomp.Objects`. -/

/-! ## 2. Injective maps of groups: saturation and bijectivity on Tate modules -/

namespace PkgI3.Tate

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

lemma map_injective (φ : M →+ N) (hφ : Function.Injective φ) :
    Function.Injective (map (ℓ := ℓ) φ) := by
  intro x y h
  apply Subtype.ext; funext n
  exact hφ (by simpa using congrArg (fun z : T ℓ N => z.1 n) h)

/-- `(ℓ • x)ₙ₊₁ = xₙ`. -/
lemma ell_smul_succ (x : T ℓ M) (n : ℕ) : ((ℓ : ℤ_[ℓ]) • x).1 (n + 1) = x.1 n := by
  rw [← x.2.2 n]
  exact smulSeq_congr x.2 (n + 1) (c := ℓ) (by simp)

/-- **Saturation.** If `ℓ • x` lies in the image of `T_ℓ M → T_ℓ N`, so does `x`. -/
lemma mem_range_of_ell_smul (φ : M →+ N) (hφ : Function.Injective φ) (x : T ℓ N)
    (h : (ℓ : ℤ_[ℓ]) • x ∈ LinearMap.range (map (ℓ := ℓ) φ)) :
    x ∈ LinearMap.range (map (ℓ := ℓ) φ) := by
  obtain ⟨y, hy⟩ := h
  have hy' : ∀ n, φ (y.1 (n + 1)) = x.1 n := fun n => by
    rw [← ell_smul_succ x n, ← hy]; rfl
  refine ⟨⟨fun n => y.1 (n + 1), ?_, fun n => ?_⟩, ?_⟩
  · exact hφ (by rw [hy', x.2.1, map_zero])
  · apply hφ
    change φ (ℓ • y.1 (n + 1 + 1)) = φ (y.1 (n + 1))
    rw [map_nsmul, hy', hy', x.2.2]
  · apply Subtype.ext; funext n; exact hy' n

lemma mem_range_of_pow_smul (φ : M →+ N) (hφ : Function.Injective φ) (k : ℕ) :
    ∀ x : T ℓ N, ((ℓ : ℤ_[ℓ]) ^ k) • x ∈ LinearMap.range (map (ℓ := ℓ) φ) →
      x ∈ LinearMap.range (map (ℓ := ℓ) φ) := by
  induction k with
  | zero => intro x h; simpa using h
  | succ k ih =>
    intro x h
    rw [pow_succ, mul_smul] at h
    exact mem_range_of_ell_smul φ hφ x (ih _ h)

/-- The cokernel of `T_ℓ M → T_ℓ N` is torsion-free. -/
lemma mem_range_of_smul (φ : M →+ N) (hφ : Function.Injective φ) (x : T ℓ N) {a : ℤ_[ℓ]}
    (ha : a ≠ 0) (h : a • x ∈ LinearMap.range (map (ℓ := ℓ) φ)) :
    x ∈ LinearMap.range (map (ℓ := ℓ) φ) := by
  apply mem_range_of_pow_smul φ hφ a.valuation
  have : ((ℓ : ℤ_[ℓ]) ^ a.valuation) • x =
      ((PadicInt.unitCoeff ha)⁻¹ : ℤ_[ℓ]ˣ) • (a • x) := by
    have hspec := PadicInt.unitCoeff_spec ha
    have key : (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * a = (ℓ : ℤ_[ℓ]) ^ a.valuation :=
      calc _ = (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) *
            ((PadicInt.unitCoeff ha : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ a.valuation) :=
            congrArg (fun t => (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * t) hspec
        _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [Units.smul_def, smul_smul, key]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ h

/-- **Comparison of Tate modules (GLUE, proved).** If `φ : M → N` is injective, `T_ℓ M` and
`T_ℓ N` are finite over `ℤ_ℓ` of the same rank, and `T_ℓ M` is free, then
`T_ℓ(φ) : T_ℓ M → T_ℓ N` is bijective. Applied to `A(K̄) → A(L̄) = A_L(L̄)` with
`TateModuleFree` over `K` and over `L` and `dim A_L = dim A`, it identifies `T_ℓ(A)` with
`T_ℓ(A_L)`. -/
theorem map_bijective (φ : M →+ N) (hφ : Function.Injective φ)
    [Module.Free ℤ_[ℓ] (T ℓ M)] [Module.Finite ℤ_[ℓ] (T ℓ M)] [Module.Finite ℤ_[ℓ] (T ℓ N)]
    (hrank : Module.finrank ℤ_[ℓ] (T ℓ M) = Module.finrank ℤ_[ℓ] (T ℓ N)) :
    Function.Bijective (map (ℓ := ℓ) φ) := by
  refine ⟨map_injective φ hφ, ?_⟩
  set R := LinearMap.range (map (ℓ := ℓ) φ)
  have h1 := Submodule.finrank_quotient_add_finrank R
  have h2 : Module.finrank ℤ_[ℓ] R = Module.finrank ℤ_[ℓ] (T ℓ M) :=
    LinearMap.finrank_range_of_inj (map_injective φ hφ)
  have h0 : Module.finrank ℤ_[ℓ] (T ℓ N ⧸ R) = 0 := by omega
  rw [Module.finrank_eq_zero_iff] at h0
  intro x
  obtain ⟨a, ha, hax⟩ := h0 (Submodule.Quotient.mk x)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact mem_range_of_smul φ hφ x ha hax

end PkgI3.Tate

