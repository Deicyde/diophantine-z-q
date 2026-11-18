import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceCharacters

/-!
# Exact affine lines in a two-dimensional determinant fibre

For a nonzero row T over a field, every row U with det(T,U)=d is uniquely
U₀+tT. The same explicit parametrization identifies the zero determinant
kernel with the scalar multiples of T.
-/

noncomputable section
set_option autoImplicit false

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

abbrev Pair (K : Type*) := K × K

def det {K : Type*} [CommRing K] (T U : Pair K) : K := T.1 * U.2 - T.2 * U.1

def scale {K : Type*} [Mul K] (s : K) (T : Pair K) : Pair K := (s * T.1, s * T.2)

def lineBase {K : Type*} [Field K] (T : Pair K) (d : K) : Pair K := by
  classical
  exact if T.1 = 0 then (-d / T.2, 0) else (0, d / T.1)

def coordinate {K : Type*} [Field K] (T V : Pair K) : K := by
  classical
  exact if T.1 = 0 then V.2 / T.2 else V.1 / T.1

lemma det_scale_left {K : Type*} [CommRing K] (s : K) (T U : Pair K) :
    det (scale s T) U = s * det T U := by simp [det, scale]; ring

lemma det_scale_right {K : Type*} [CommRing K] (s : K) (T U : Pair K) :
    det T (scale s U) = s * det T U := by simp [det, scale]; ring

lemma det_swap {K : Type*} [CommRing K] (T U : Pair K) : det T U = -det U T := by
  simp [det]; ring

lemma det_self {K : Type*} [CommRing K] (T : Pair K) : det T T = 0 := by simp [det, mul_comm]

lemma det_add_right {K : Type*} [CommRing K] (T U V : Pair K) :
    det T (U + V) = det T U + det T V := by simp [det]; ring

lemma det_lineBase {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0) (d : K) :
    det T (lineBase T d) = d := by
  by_cases h1 : T.1 = 0
  · have h2 : T.2 ≠ 0 := by intro h; apply hT; exact Prod.ext h1 h
    simp only [lineBase, h1, ↓reduceIte, det, Prod.fst, Prod.snd, zero_mul, zero_sub]
    field_simp
  · simp only [lineBase, h1, ↓reduceIte, det, Prod.fst, Prod.snd, mul_zero, sub_zero]
    field_simp

lemma coordinate_line {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0) (d t : K) :
    coordinate T (lineBase T d + scale t T) = t := by
  by_cases h1 : T.1 = 0
  · have h2 : T.2 ≠ 0 := by intro h; apply hT; exact Prod.ext h1 h
    simp [coordinate, lineBase, h1, scale, h2]
  · simp [coordinate, lineBase, h1, scale]

lemma row_eq_line {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0) (d : K)
    (U : Pair K) (hU : det T U = d) : U = lineBase T d + scale (coordinate T U) T := by
  by_cases h1 : T.1 = 0
  · have h2 : T.2 ≠ 0 := by intro h; apply hT; exact Prod.ext h1 h
    simp only [det, h1, zero_mul, zero_sub] at hU
    apply Prod.ext
    · simp only [lineBase, coordinate, h1, ↓reduceIte, scale, Prod.fst, Prod.fst_add,
        mul_zero, add_zero]
      field_simp
      linear_combination -hU
    · simp [lineBase, coordinate, h1, scale, h2]
  · apply Prod.ext
    · simp [lineBase, coordinate, h1, scale]
    · simp only [lineBase, coordinate, h1, ↓reduceIte, scale, Prod.snd, Prod.snd_add]
      field_simp
      dsimp [det] at hU
      linear_combination hU

/-- Genuine bijective enumeration of the determinant fibre. -/
def affineLineEquiv {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0) (d : K) :
    K ≃ {U : Pair K // det T U = d} where
  toFun t := ⟨lineBase T d + scale t T, by rw [det_add_right, det_lineBase T hT,
    det_scale_right, det_self, mul_zero, add_zero]⟩
  invFun U := coordinate T U
  left_inv t := coordinate_line T hT d t
  right_inv U := Subtype.ext (row_eq_line T hT d U U.property).symm

lemma lineBase_zero {K : Type*} [Field K] (T : Pair K) : lineBase T 0 = 0 := by
  by_cases h1 : T.1 = 0 <;> simp [lineBase, h1]

/-- The vanishing determinant kernel is exactly the scalar line, with a proved unique coordinate. -/
theorem determinant_kernel {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0) (V : Pair K) :
    det T V = 0 ↔ V = scale (coordinate T V) T := by
  constructor
  · intro hv
    simpa only [lineBase_zero, zero_add] using row_eq_line T hT 0 V hv
  · intro hv
    rw [hv, det_scale_right, det_self, mul_zero]

lemma scale_injective {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0) :
    Function.Injective (fun s : K => scale s T) := by
  intro s t he
  by_cases h1 : T.1 = 0
  · have h2 : T.2 ≠ 0 := by intro h; apply hT; exact Prod.ext h1 h
    exact mul_right_cancel₀ h2 (congrArg Prod.snd he)
  · exact mul_right_cancel₀ h1 (congrArg Prod.fst he)

/-- Every zero-kernel row has a unique actual scalar parameter. -/
theorem determinant_kernel_exists_unique {K : Type*} [Field K] (T : Pair K) (hT : T ≠ 0)
    (V : Pair K) (hV : det T V = 0) : ∃! s : K, V = scale s T := by
  refine ⟨coordinate T V, (determinant_kernel T hT V).mp hV, ?_⟩
  intro s hs
  exact scale_injective T hT (hs.symm.trans ((determinant_kernel T hT V).mp hV))

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
