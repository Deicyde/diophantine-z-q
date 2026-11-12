/-
glue-I3-linalg: comparison of Tate modules along an injective map of groups (the algebraic core of
"`T_ℓ` under base change of the field"). Section 1 is copied verbatim from `scratch/pkg-I3/I3.lean`
(the Tate module `Tate.T ℓ M` of an abelian group, as a `ℤ_ℓ`-module); section 2 is new.
-/
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- `T_ℓ(M) = lim_n M[ℓⁿ]` (transition maps: multiplication by `ℓ`), realized as the
sequences `(xₙ)` with `x₀ = 0` and `ℓ • xₙ₊₁ = xₙ`; then `xₙ ∈ M[ℓⁿ]`. -/
def T : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp [smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp [hx n]

variable {ℓ M}

omit hℓ in
lemma pow_smul_eq_zero {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) : (ℓ ^ n) • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih => rw [pow_succ, mul_smul, hx.2 n, ih]

omit hℓ in
lemma nsmul_congr {y : M} {n : ℕ} (hy : (ℓ ^ n) • y = 0) {c d : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = (d : ZMod (ℓ ^ n))) : c • y = d • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div' c (ℓ ^ n), ← Nat.mod_add_div' d (ℓ ^ n), add_smul, add_smul,
    mul_smul, mul_smul, hy, smul_zero, smul_zero, h]

instance (n : ℕ) : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

lemma val_cast (a : ℤ_[ℓ]) (n : ℕ) :
    (((PadicInt.toZModPow (n + 1) a).val : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, ZMod.natCast_val]

/-- The `ℤ_ℓ`-action: `(a • x)ₙ = (a mod ℓⁿ) • xₙ`. -/
def smulSeq (a : ℤ_[ℓ]) (x : ℕ → M) : ℕ → M :=
  fun n => (PadicInt.toZModPow n a).val • x n

lemma smulSeq_mem (a : ℤ_[ℓ]) {x : ℕ → M} (hx : x ∈ T ℓ M) : smulSeq a x ∈ T ℓ M := by
  refine ⟨by simp [smulSeq, hx.1], fun n => ?_⟩
  simp only [smulSeq]
  rw [smul_comm, hx.2 n]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [val_cast, ZMod.natCast_zmod_val]

lemma smulSeq_congr {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) {a : ℤ_[ℓ]} {c : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) : smulSeq a x n = c • x n := by
  simp only [smulSeq]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [ZMod.natCast_zmod_val, h]

instance : Module ℤ_[ℓ] (T ℓ M) where
  smul a x := ⟨smulSeq a x.1, smulSeq_mem a x.2⟩
  one_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 1 x.1 n = x.1 n
    rw [smulSeq_congr x.2 n (c := 1) (by simp), one_smul]
  mul_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a * b) x.1 n = smulSeq a (smulSeq b x.1) n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n b).val)
      (by push_cast; simp), mul_smul]
    rfl
  smul_zero a := Subtype.ext <| funext fun n => by
    change smulSeq a 0 n = 0
    simp [smulSeq]
  smul_add a x y := Subtype.ext <| funext fun n => by
    change smulSeq a (x.1 + y.1) n = smulSeq a x.1 n + smulSeq a y.1 n
    simp [smulSeq, smul_add]
  add_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a + b) x.1 n = smulSeq a x.1 n + smulSeq b x.1 n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val + (PadicInt.toZModPow n b).val)
      (by push_cast; simp), add_smul]
    rfl
  zero_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 0 x.1 n = 0
    simp [smulSeq]

@[simp] lemma smul_apply (a : ℤ_[ℓ]) (x : T ℓ M) (n : ℕ) :
    (a • x).1 n = (PadicInt.toZModPow n a).val • x.1 n := rfl

variable {N : Type*} [AddCommGroup N]

/-- Functoriality: a group homomorphism `M → N` induces a `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N`. -/
def map (φ : M →+ N) : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ N where
  toFun x := ⟨fun n => φ (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_add' x y := Subtype.ext <| funext fun n => by simp
  map_smul' a x := Subtype.ext <| funext fun n => by simp [map_nsmul]

@[simp] lemma map_apply (φ : M →+ N) (x : T ℓ M) (n : ℕ) : (map φ x).1 n = φ (x.1 n) := rfl

end PkgI3.Tate

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

#print axioms PkgI3.Tate.map_bijective
