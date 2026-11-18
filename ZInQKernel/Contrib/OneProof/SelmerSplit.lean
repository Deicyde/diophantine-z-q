import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroup
import ZInQKernel.Contrib.TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import ZInQKernel.Hypotheses.PoleManuscript

/-!
# The explicit `2`-Selmer group of `E_ℓ` in the manuscript's Kummer coordinates

For `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` over a field `K` of characteristic zero with `ℓ ≠ 0`, the cubic
`f = x(x − ℓ)(x + 3ℓ)` splits with the distinct roots `e = (−3ℓ, ℓ, 0)`, so the étale algebra
`K[X]/(f)` is `K³` (evaluation at the roots) and its square classes `M` are `(K*/K*²)³`
(`coord`, `coord_injective`, `coord_surjective`). In these coordinates

* the norm class is the product of the three coordinates (`normM_eq_coord_mul`);
* restriction to an extension field is the coordinatewise map (`coord_localRes`);
* the `x − T` descent map sends `x` to `(x + 3ℓ, x − ℓ, x)`, with the corrected values
  `(3, −ℓ, −3ℓ)`, `(ℓ, 1, ℓ)`, `(3ℓ, −ℓ, −3)` at the three roots (`coord_μX`);
* the class with coordinates `(a, b, ab)` is in the image of `E_ℓ(K)` exactly when the
  manuscript's "x-form" condition `LocM K ℓ a b` holds (`exists_coord_μ_iff_locM`).

Over `ℚ`, square classes are squarefree integers (`sqfreeEquiv`), and the local condition at the
finite place `v = (p)` is the one over `ℚ_p` (`locM_adicCompletion_iff`).
-/

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ZInQ.Manuscript.SelmerSplit

/-! ### Square classes -/

/-- **Square classes** `K*/K*²`. -/
abbrev SqCl (K : Type*) [Field K] : Type _ := Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range

/-- The square class of a nonzero element. -/
def sq {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : SqCl K :=
  QuotientGroup.mk (Units.mk0 a ha)

/-- The map on square classes induced by a field homomorphism. -/
def SqCl.map {K L : Type*} [Field K] [Field L] (φ : K →+* L) : SqCl K →* SqCl L :=
  QuotientGroup.map _ _ (Units.map φ.toMonoidHom) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map φ.toMonoidHom u, by simp [powMonoidHom]⟩

theorem SqCl.map_sq {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a : K) (ha : a ≠ 0) :
    SqCl.map φ (sq a ha) = sq (φ a) (by simpa using ha) := by
  simp only [SqCl.map, sq, QuotientGroup.map_mk]
  congr 1
  ext
  simp

/-! ### The curves `E_ℓ` -/

/-- **`W` is `E_ℓ : y² = x(x − ℓ)(x + 3ℓ) = x³ + 2ℓx² − 3ℓ²x`.** -/
structure IsCurveM {K : Type*} [Field K] (W : WeierstrassCurve K) (ℓ : K) : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 2 * ℓ
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = -3 * ℓ ^ 2
  a₆ : W.a₆ = 0

/-- The roots `(−3ℓ, ℓ, 0)` of `x(x − ℓ)(x + 3ℓ)`, in the order of the manuscript's Kummer
coordinates `(x + 3ℓ, x − ℓ, x)`. -/
def roots {K : Type*} [Field K] (ℓ : K) : Fin 3 → K := ![-3 * ℓ, ℓ, 0]

/-- The corrected coordinate of the descent map at the root `roots ℓ i`: the product of its
differences with the other two roots, `(12ℓ², 4ℓ², −3ℓ²)`. -/
def rootValue {K : Type*} [Field K] (ℓ : K) : Fin 3 → K := ![12 * ℓ ^ 2, 4 * ℓ ^ 2, -3 * ℓ ^ 2]

section Curve

variable {K : Type*} [Field K] {W : WeierstrassCurve K} {ℓ : K}

theorem IsCurveM.f_eq (h : IsCurveM W ℓ) : W.toAffine.f = ∏ i, (X - C (roots ℓ i)) := by
  simp [WeierstrassCurve.Affine.f, h.a₂, h.a₄, h.a₆, Fin.prod_univ_three,
    roots, map_mul, map_pow, C_ofNat]
  ring

theorem IsCurveM.isCharNeTwoNF (h : IsCurveM W ℓ) : W.toAffine.IsCharNeTwoNF :=
  ⟨h.a₁, h.a₃⟩

theorem IsCurveM.isElliptic [CharZero K] (h : IsCurveM W ℓ) (hℓ : ℓ ≠ 0) : W.IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  have hΔ : W.Δ = 2304 * ℓ ^ 6 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, h.a₁, h.a₂, h.a₃, h.a₄, h.a₆]
    ring
  rw [hΔ]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hℓ)

theorem IsCurveM.baseChange (h : IsCurveM W ℓ) (L : Type*) [Field L] [Algebra K L] :
    IsCurveM (W⁄L) (algebraMap K L ℓ) := by
  constructor <;>
    simp [WeierstrassCurve.baseChange, h.a₁, h.a₂, h.a₃, h.a₄, h.a₆, map_ofNat]

theorem roots_injective [CharZero K] (hℓ : ℓ ≠ 0) : Function.Injective (roots ℓ) := by
  have h01 : (-3 : K) * ℓ ≠ ℓ := by
    intro he
    have he' : (-3 : K) = 1 := mul_right_cancel₀ hℓ (by simpa using he)
    norm_num at he'
  have h02 : (-3 : K) * ℓ ≠ 0 := mul_ne_zero (by norm_num) hℓ
  intro i j hij
  fin_cases i <;> fin_cases j <;> dsimp [roots] at hij ⊢ <;>
    first | exact (h01 hij).elim | exact (h01 hij.symm).elim |
      exact (h02 hij).elim | exact (h02 hij.symm).elim |
      exact (hℓ hij).elim | exact (hℓ hij.symm).elim

theorem rootValue_ne_zero [CharZero K] (hℓ : ℓ ≠ 0) (i : Fin 3) : rootValue ℓ i ≠ 0 := by
  fin_cases i <;> dsimp [rootValue] <;>
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hℓ)

end Curve

/-! ### Coordinates on the étale algebra and its square classes -/

section Coordinates

variable {K : Type*} [Field K] {W : WeierstrassCurve K} {ℓ : K} (h : IsCurveM W ℓ)
include h

theorem IsCurveM.eval₂_f_root (i : Fin 3) :
    W.toAffine.f.eval₂ (RingHom.id K) (roots ℓ i) = 0 := by
  rw [eval₂_id, h.f_eq, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]
  simp

/-- **Evaluation at the root `roots ℓ i`**, a ring homomorphism `K[X]/(f) → K`. -/
def evA (i : Fin 3) : W.toAffine.A →+* K :=
  AdjoinRoot.lift (RingHom.id K) (roots ℓ i) (h.eval₂_f_root i)

@[simp]
theorem evA_mk (i : Fin 3) (p : K[X]) :
    evA h i (AdjoinRoot.mk W.toAffine.f p) = p.eval (roots ℓ i) := by
  simp [evA, AdjoinRoot.lift_mk, eval₂_id]

/-- **The `i`-th coordinate of a square class** of the étale algebra: the square class of the value
at the root `roots ℓ i`. -/
def coord (i : Fin 3) : (W.toAffine.M) →* SqCl K :=
  QuotientGroup.map _ _ (Units.map (evA h i).toMonoidHom) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map (evA h i).toMonoidHom u, by simp [powMonoidHom]⟩

theorem coord_mk (i : Fin 3) (u : W.toAffine.Aˣ) :
    coord h i (QuotientGroup.mk u) = QuotientGroup.mk (Units.map (evA h i).toMonoidHom u) :=
  QuotientGroup.map_mk _ _ _ _ u

private theorem evA_ext [CharZero K] (hℓ : ℓ ≠ 0) {a b : W.toAffine.A}
    (hab : ∀ i, evA h i a = evA h i b) : a = b := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  apply AdjoinRoot.mk_eq_mk.mpr
  rw [h.f_eq]
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact (Polynomial.pairwise_coprime_X_sub_C (roots_injective hℓ)) hij
  · intro i _
    apply Polynomial.dvd_iff_isRoot.mpr
    change (p - q).eval (roots ℓ i) = 0
    rw [eval_sub, sub_eq_zero]
    simpa only [evA_mk] using hab i

private theorem exists_evA [CharZero K] (hℓ : ℓ ≠ 0) (v : Fin 3 → K) :
    ∃ a : W.toAffine.A, ∀ i, evA h i a = v i := by
  let p : K[X] :=
    C (v 0 / (12 * ℓ ^ 2)) * X * (X - C ℓ) +
    C (v 1 / (4 * ℓ ^ 2)) * X * (X + C (3 * ℓ)) +
    C (v 2 / (-3 * ℓ ^ 2)) * (X + C (3 * ℓ)) * (X - C ℓ)
  refine ⟨AdjoinRoot.mk W.toAffine.f p, ?_⟩
  intro i
  rw [evA_mk]
  fin_cases i <;> simp [p, roots] <;> field_simp <;> ring

private theorem exists_units_evA [CharZero K] (hℓ : ℓ ≠ 0) (v : Fin 3 → Kˣ) :
    ∃ u : W.toAffine.Aˣ, ∀ i, Units.map (evA h i).toMonoidHom u = v i := by
  obtain ⟨a, ha⟩ := exists_evA h hℓ (fun i => (v i : K))
  obtain ⟨b, hb⟩ := exists_evA h hℓ (fun i => ((v i)⁻¹ : Kˣ))
  have hab : a * b = 1 := by
    apply evA_ext h hℓ
    intro i
    rw [map_mul, map_one, ha i, hb i]
    simp
  refine ⟨Units.mkOfMulEqOne a b hab, ?_⟩
  intro i
  apply Units.ext
  exact ha i

/-- **The coordinates determine the square class**: an element of `K[X]/(f)` whose three
values are squares is a square (interpolation at the three distinct roots). -/
theorem coord_injective [CharZero K] (hℓ : ℓ ≠ 0) :
    Function.Injective (fun m : W.toAffine.M => fun i => coord h i m) := by
  classical
  intro m n hmn
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective n
  have hs : ∀ i, ∃ t : Kˣ, t ^ 2 = Units.map (evA h i).toMonoidHom (u⁻¹ * v) := by
    intro i
    have hi := congrFun hmn i
    change coord h i (QuotientGroup.mk u) = coord h i (QuotientGroup.mk v) at hi
    rw [coord_mk, coord_mk, QuotientGroup.eq] at hi
    obtain ⟨t, ht⟩ := hi
    refine ⟨t, ?_⟩
    simpa only [powMonoidHom_apply, map_inv, map_mul] using ht
  choose t ht using hs
  obtain ⟨z, hz⟩ := exists_units_evA h hℓ t
  apply QuotientGroup.eq.mpr
  refine ⟨z, ?_⟩
  change z ^ 2 = u⁻¹ * v
  apply Units.ext
  apply evA_ext h hℓ
  intro i
  have hi : Units.map (evA h i).toMonoidHom (z ^ 2) =
      Units.map (evA h i).toMonoidHom (u⁻¹ * v) := by
    rw [map_pow, hz i, ht i]
  exact congrArg Units.val hi

/-- **Every triple of square classes is the coordinate triple of a square class.** -/
theorem coord_surjective [CharZero K] (hℓ : ℓ ≠ 0) :
    Function.Surjective (fun m : W.toAffine.M => fun i => coord h i m) := by
  classical
  intro c
  choose v hv using fun i => QuotientGroup.mk_surjective (c i)
  obtain ⟨u, hu⟩ := exists_units_evA h hℓ v
  refine ⟨QuotientGroup.mk u, funext fun i => ?_⟩
  change coord h i (QuotientGroup.mk u) = c i
  rw [coord_mk, hu i, hv i]

/-- **The norm class is the product of the coordinates** (the norm of `K[X]/(f) = K³` is the
product of the values at the roots: Tau Ceti's `AdjoinRoot.norm_mk_eq_prod_eval`). -/
theorem normM_eq_coord_mul (m : W.toAffine.M) :
    normM (W := W.toAffine) m = coord h 0 m * coord h 1 m * coord h 2 m := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
  rw [normM_mk, coord_mk, coord_mk, coord_mk,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  change Algebra.norm K (u : W.toAffine.A) =
    evA h 0 (u : W.toAffine.A) * evA h 1 (u : W.toAffine.A) * evA h 2 (u : W.toAffine.A)
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (u : W.toAffine.A)
  rw [← hp, AdjoinRoot.norm_mk_eq_prod_eval h.f_eq p, Fin.prod_univ_three,
    evA_mk, evA_mk, evA_mk]

/-- **Restriction to an extension field is coordinatewise.** -/
theorem coord_localRes (L : Type*) [Field L] [Algebra K L] (i : Fin 3) (m : W.toAffine.M) :
    coord (h.baseChange L) i (W.toAffine.localRes L m) = SqCl.map (algebraMap K L) (coord h i m) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
  rw [localRes_mk, coord_mk, coord_mk]
  simp only [SqCl.map, QuotientGroup.map_mk]
  congr 1
  apply Units.ext
  change evA (h.baseChange L) i (W.toAffine.mapA L (u : W.toAffine.A)) =
    algebraMap K L (evA h i (u : W.toAffine.A))
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (u : W.toAffine.A)
  rw [← hp, mapA_mk, evA_mk, evA_mk]
  have hr : roots (algebraMap K L ℓ) i = algebraMap K L (roots ℓ i) := by
    fin_cases i <;> simp [roots, map_ofNat]
  rw [hr, Polynomial.eval_map, Polynomial.eval₂_at_apply]

private lemma coord_unit_mk (i : Fin 3) {p : K[X]}
    (hp : IsUnit (AdjoinRoot.mk W.toAffine.f p)) {a : K} (ha : a ≠ 0)
    (heval : p.eval (roots ℓ i) = a) :
    coord h i (QuotientGroup.mk hp.unit) = sq a ha := by
  rw [coord_mk]
  unfold sq
  congr 1
  apply Units.ext
  change evA h i (hp.unit : W.toAffine.A) = a
  rw [IsUnit.unit_spec, evA_mk, heval]

open scoped Classical in
/-- **The `x − T` map in coordinates**: off the roots, `x` goes to the classes of
`x − roots ℓ i = (x + 3ℓ, x − ℓ, x)`; at the root `roots ℓ j` the `j`-th coordinate is the corrected
value `rootValue ℓ j` and the others are `roots ℓ j − roots ℓ i`. -/
theorem coord_μX [CharZero K] (hℓ : ℓ ≠ 0) (x : K) (i : Fin 3) :
    haveI := h.isCharNeTwoNF
    haveI := h.isElliptic hℓ
    coord h i (W.toAffine.μX x) =
      if hx : x = roots ℓ i then sq (rootValue ℓ i) (rootValue_ne_zero hℓ i)
      else sq (x - roots ℓ i) (sub_ne_zero.mpr hx) := by
  classical
  let _ := h.isCharNeTwoNF
  let _ := h.isElliptic hℓ
  have hroot (j : Fin 3) : W.toAffine.f.eval (roots ℓ j) = 0 := by
    simpa only [eval₂_id] using h.eval₂_f_root j
  by_cases hx : x = roots ℓ i
  · have hxf : W.toAffine.f.eval x = 0 := by
      rw [hx]
      exact hroot i
    rw [dite_eq_left hx, μX_of_eval_f_eq_zero hxf]
    apply coord_unit_mk h i
    rw [hx]
    simp only [eval_add, eval_sub, eval_C, eval_X, sub_self, zero_add, h.a₂, h.a₄]
    fin_cases i <;> simp [roots, rootValue] <;> ring
  · rw [dite_eq_right hx]
    by_cases hxf : W.toAffine.f.eval x = 0
    · rw [μX_of_eval_f_eq_zero hxf]
      apply coord_unit_mk h i
      have heval := congrArg (fun p : K[X] => p.eval (roots ℓ i))
        (W.toAffine.fCofactor_mul_eq x)
      simp only [eval_mul, eval_sub, eval_X, eval_C, hroot i, hxf, sub_self] at heval
      have hcf : (W.toAffine.fCofactor x).eval (roots ℓ i) = 0 :=
        (mul_eq_zero.mp heval).resolve_right (sub_ne_zero.mpr (Ne.symm hx))
      simp only [eval_add, eval_sub, eval_C, eval_X, hcf, add_zero]
    · rw [μX_of_eval_f_ne_zero hxf]
      apply coord_unit_mk h i
      simp

end Coordinates

/-! ### The local image in the manuscript's x-form -/

/-- **The Kummer image of `E_ℓ(K)` in x-form** (the same condition as the descent lane's
`ZInQ.Manuscript.PoleRC.LocM`, `diophantine_zq.tex` line 1061): either `a` and `b` are squares
(the point `O`), or some `x ∈ K` makes `(x + 3ℓ)/a`, `(x − ℓ)/b` and `x/(ab)` squares (zero
allowed). -/
def LocM (K : Type*) [Field K] (ℓ a b : K) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : K, IsSquare ((x + 3 * ℓ) / a) ∧ IsSquare ((x - ℓ) / b) ∧ IsSquare (x / (a * b))

section LocalImage

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] {W : WeierstrassCurve K} {ℓ : K}
  (h : IsCurveM W ℓ) (hℓ : ℓ ≠ 0)

omit [CharZero K] [DecidableEq K] in
private lemma sq_eq_one_iff_isSquare (a : K) (ha : a ≠ 0) :
    sq a ha = 1 ↔ IsSquare a := by
  unfold sq
  rw [TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow, isSquare_iff_exists_sq]
  constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨z, hz.symm⟩

omit [CharZero K] [DecidableEq K] in
private lemma sq_mul_eq (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    sq (a * b) (mul_ne_zero ha hb) = sq a ha * sq b hb := by
  unfold sq
  rw [← QuotientGroup.mk_mul]
  congr 1
  ext
  simp

omit [CharZero K] [DecidableEq K] in
private lemma sq_div_eq (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    sq (a / b) (div_ne_zero ha hb) = sq a ha / sq b hb := by
  unfold sq
  rw [← QuotientGroup.mk_div]
  congr 1
  ext
  simp

omit [CharZero K] [DecidableEq K] in
private lemma sq_eq_sq_iff_isSquare_div (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    sq a ha = sq b hb ↔ IsSquare (a / b) := by
  rw [← div_eq_one, ← sq_div_eq a b ha hb, sq_eq_one_iff_isSquare]

omit [CharZero K] [DecidableEq K] in
private lemma sqCl_mul_self (m : SqCl K) : m * m = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
  rw [← pow_two, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

private lemma eq_of_prod_eq_of_eq_off {G : Type*} [CommGroup G] (f g : Fin 3 → G) (i : Fin 3)
    (hprod : ∏ j, f j = ∏ j, g j) (heq : ∀ j, j ≠ i → f j = g j) : f i = g i := by
  have he : (∏ j ∈ Finset.univ.erase i, f j) = ∏ j ∈ Finset.univ.erase i, g j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact heq j (Finset.mem_erase.mp hj).1
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), he] at hprod
  exact mul_right_cancel hprod

include h hℓ in
/-- **The local image in x-form**: the square class with coordinates `(a, b, ab)` is the image
of a point of `E_ℓ(K)` under the descent map exactly when `LocM K ℓ a b`. -/
theorem exists_coord_μ_iff_locM (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    haveI := h.isCharNeTwoNF
    haveI := h.isElliptic hℓ
    (∃ P : W.toAffine.Point, ∀ i, coord h i (μ (W := W.toAffine) (.ofAdd P)) =
        ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)] i) ↔ LocM K ℓ a b := by
  let := h.isCharNeTwoNF
  let := h.isElliptic hℓ
  constructor
  · rintro ⟨P, hP⟩
    simp only [μ_apply] at hP
    match P with
    | 0 =>
      left
      constructor
      · apply (sq_eq_one_iff_isSquare a ha).mp
        simpa using (hP 0).symm
      · apply (sq_eq_one_iff_isSquare b hb).mp
        simpa using (hP 1).symm
    | .some x y hp =>
      right
      have hs (i : Fin 3) (c : K) (hc : c ≠ 0)
          (hci : coord h i (W.toAffine.μX x) = sq c hc) :
          IsSquare ((x - roots ℓ i) / c) := by
        by_cases hxi : x = roots ℓ i
        · rw [hxi, sub_self, zero_div]
          exact ⟨0, by simp⟩
        · apply (sq_eq_sq_iff_isSquare_div _ c (sub_ne_zero.mpr hxi) hc).mp
          have hcoord := coord_μX h hℓ x i
          rw [dite_eq_right hxi] at hcoord
          exact hcoord.symm.trans hci
      have hs₀ := hs 0 a ha (by simpa using hP 0)
      have hs₁ := hs 1 b hb (by simpa using hP 1)
      have hs₂ := hs 2 (a * b) (mul_ne_zero ha hb) (by simpa using hP 2)
      refine ⟨x, ?_⟩
      simpa [roots, sub_neg_eq_add] using And.intro hs₀ (And.intro hs₁ hs₂)
  · intro hloc
    rcases hloc with hab | ⟨x, hx₀, hx₁, hx₂⟩
    · refine ⟨0, ?_⟩
      intro i
      simp only [μ_apply, μ₀_zero, map_one]
      fin_cases i
      · exact ((sq_eq_one_iff_isSquare a ha).mpr hab.1).symm
      · exact ((sq_eq_one_iff_isSquare b hb).mpr hab.2).symm
      · exact ((sq_eq_one_iff_isSquare (a * b) (mul_ne_zero ha hb)).mpr
          (hab.1.mul hab.2)).symm
    · obtain ⟨u, hu⟩ := hx₀.exists_sq
      obtain ⟨v, hv⟩ := hx₁.exists_sq
      obtain ⟨w, hw⟩ := hx₂.exists_sq
      have hu' : x + 3 * ℓ = u ^ 2 * a := (div_eq_iff ha).mp hu
      have hv' : x - ℓ = v ^ 2 * b := (div_eq_iff hb).mp hv
      have hw' : x = w ^ 2 * (a * b) := (div_eq_iff (mul_ne_zero ha hb)).mp hw
      have heq : W.toAffine.Equation x (u * v * w * (a * b)) := by
        rw [equation_iff_eval_f_eq_sq, eval_f, h.a₂, h.a₄, h.a₆]
        calc
          x ^ 3 + 2 * ℓ * x ^ 2 + -3 * ℓ ^ 2 * x + 0 =
              x * (x - ℓ) * (x + 3 * ℓ) := by ring
          _ = (u * v * w * (a * b)) ^ 2 := by
            rw [hu', hv', hw']
            ring
      let P : W.toAffine.Point := .some x (u * v * w * (a * b))
        (equation_iff_nonsingular.mp heq)
      let c : Fin 3 → K := ![a, b, a * b]
      have hc (i : Fin 3) : c i ≠ 0 := by
        fin_cases i <;> simp [c, ha, hb]
      have hcs (i : Fin 3) : sq (c i) (hc i) =
          ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)] i := by
        fin_cases i <;> rfl
      have hxs (i : Fin 3) : IsSquare ((x - roots ℓ i) / c i) := by
        fin_cases i
        · simpa [roots, c, sub_neg_eq_add] using hx₀
        · simpa [roots, c] using hx₁
        · simpa [roots, c] using hx₂
      have hgood (i : Fin 3) (hxi : x ≠ roots ℓ i) :
          coord h i (μ (W := W.toAffine) (.ofAdd P)) = sq (c i) (hc i) := by
        rw [μ_apply]
        change coord h i (W.toAffine.μX x) = sq (c i) (hc i)
        rw [coord_μX h hℓ x i, dite_eq_right hxi]
        exact (sq_eq_sq_iff_isSquare_div _ _ (sub_ne_zero.mpr hxi) (hc i)).mpr (hxs i)
      have hPprod : (∏ i, coord h i (μ (W := W.toAffine) (.ofAdd P))) = 1 := by
        rw [Fin.prod_univ_three, ← normM_eq_coord_mul h, μ_apply]
        exact normM_μ₀_eq_one P
      have hcprod : (∏ i, sq (c i) (hc i)) = 1 := by
        rw [Fin.prod_univ_three]
        change sq a ha * sq b hb * sq (a * b) (mul_ne_zero ha hb) = 1
        rw [sq_mul_eq]
        exact sqCl_mul_self _
      refine ⟨P, ?_⟩
      intro i
      rw [← hcs i]
      by_cases hxi : x = roots ℓ i
      · apply eq_of_prod_eq_of_eq_off _ _ i (hPprod.trans hcprod.symm)
        intro j hji
        apply hgood j
        intro hxj
        exact hji (roots_injective hℓ (hxi.symm.trans hxj)).symm
      · exact hgood i hxi

set_option linter.unusedSectionVars false in
private lemma isSquare_mul_sq_iff_of_ne_zero (a s : K) (hs : s ≠ 0) :
    IsSquare (a * s ^ 2) ↔ IsSquare a := by
  constructor
  · intro h
    simpa only [mul_div_cancel_right₀ a (pow_ne_zero 2 hs)] using h.div (IsSquare.sq s)
  · intro h
    exact h.mul (IsSquare.sq s)

set_option linter.unusedSectionVars false in
private lemma isSquare_div_sq_iff_of_ne_zero (a s : K) (hs : s ≠ 0) :
    IsSquare (a / s ^ 2) ↔ IsSquare a := by
  constructor
  · intro h
    simpa only [div_mul_cancel₀ a (pow_ne_zero 2 hs)] using h.mul (IsSquare.sq s)
  · intro h
    exact h.div (IsSquare.sq s)

private lemma isSquare_div_mul_sq_iff_of_ne_zero (x a s : K) (hs : s ≠ 0) :
    IsSquare (x / (a * s ^ 2)) ↔ IsSquare (x / a) := by
  rw [div_mul_eq_div_div, isSquare_div_sq_iff_of_ne_zero _ s hs]

/-- **`LocM` depends only on the square classes of `a` and `b`.** -/
theorem locM_mul_sq (a b s t : K) (hs : s ≠ 0) (ht : t ≠ 0) :
    LocM K ℓ (a * s ^ 2) (b * t ^ 2) ↔ LocM K ℓ a b := by
  unfold LocM
  rw [isSquare_mul_sq_iff_of_ne_zero a s hs, isSquare_mul_sq_iff_of_ne_zero b t ht]
  simp_rw [isSquare_div_mul_sq_iff_of_ne_zero _ a s hs,
    isSquare_div_mul_sq_iff_of_ne_zero _ b t ht,
    show (a * s ^ 2) * (b * t ^ 2) = (a * b) * (s * t) ^ 2 by ring,
    isSquare_div_mul_sq_iff_of_ne_zero _ (a * b) (s * t) (mul_ne_zero hs ht)]

end LocalImage

/-! ### Over `ℚ`: squarefree representatives and the `p`-adic local conditions -/

/-- Every `p : Nat.Primes` is prime. -/
instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **Square classes of `ℚ` are squarefree integers.** -/
theorem sqfree_bijective :
    Function.Bijective (fun z : {z : ℤ // Squarefree z} =>
      sq (z : ℚ) (by exact_mod_cast z.2.ne_zero)) := by
  -- two nonzero rationals have the same square class iff their ratio is a square
  have key : ∀ (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0), sq x hx = sq y hy ↔ IsSquare (y / x) := by
    intro x y hx hy
    rw [sq, sq, QuotientGroup.eq]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      have h := congrArg Units.val hu
      simp [powMonoidHom] at h
      rw [div_eq_inv_mul, ← h, pow_two]
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp [hx, hy] at hc
      refine ⟨Units.mk0 c hc0, ?_⟩
      ext
      simp [powMonoidHom]
      rw [pow_two, ← hc, div_eq_inv_mul]
  constructor
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne_zero
    have h' : IsSquare ((t : ℚ) / s) := (key _ _ _ _).mp h
    have h2 : IsSquare (s * t) := by
      rw [← Rat.isSquare_intCast_iff]
      obtain ⟨c, hc⟩ := h'
      refine ⟨s * c, ?_⟩
      have ht' : (t : ℚ) = c * c * s := (div_eq_iff hs0).mp hc
      push_cast
      rw [ht']
      ring
    rcases Int.associated_iff.mp (hs.associated_of_isSquare_mul ht h2) with h3 | h3
    · exact Subtype.ext h3
    · exfalso
      have h4 := h2.nonneg
      rw [h3, neg_mul] at h4
      have h5 : 0 < t * t := mul_self_pos.mpr ht.ne_zero
      linarith
  · intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, d, hed, hd⟩ := exists_sq_mul_squarefree ((u : ℚ).num * (u : ℚ).den)
    refine ⟨⟨d, hd⟩, ?_⟩
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
    have hu : (QuotientGroup.mk u : SqCl ℚ) = sq (u : ℚ) u.ne_zero := by
      rw [sq, Units.mk0_val]
    show sq (d : ℚ) hd0 = _
    rw [hu, key]
    refine ⟨e / (u : ℚ).den, ?_⟩
    have hden : ((u : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (u : ℚ).den_nz
    have hed' : (((u : ℚ).num : ℚ) * (u : ℚ).den) = (e : ℚ) ^ 2 * d := by exact_mod_cast hed.symm
    have hq : (u : ℚ) / d = ((u : ℚ).num / (u : ℚ).den) / d := by rw [Rat.num_div_den]
    rw [hq, div_div, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hden hd0) (mul_ne_zero hden hden)]
    linear_combination ((u : ℚ).den : ℚ) * hed'

/-- **`LocM` along a field isomorphism.** -/
theorem locM_ringEquiv {K L : Type*} [Field K] [Field L] (φ : K ≃+* L) (ℓ a b : K) :
    LocM L (φ ℓ) (φ a) (φ b) ↔ LocM K ℓ a b := by
  -- squares are preserved and reflected by a ring isomorphism
  have key : ∀ y : K, IsSquare (φ y) ↔ IsSquare y := fun y =>
    ⟨fun h => by simpa using h.map φ.symm, fun h => h.map φ⟩
  unfold LocM
  refine or_congr (and_congr (key a) (key b)) ?_
  rw [φ.surjective.exists]
  refine exists_congr fun x => ?_
  have e1 : (φ x + 3 * φ ℓ) / φ a = φ ((x + 3 * ℓ) / a) := by
    rw [map_div₀, map_add, map_mul, map_ofNat]
  have e2 : (φ x - φ ℓ) / φ b = φ ((x - ℓ) / b) := by rw [map_div₀, map_sub]
  have e3 : φ x / (φ a * φ b) = φ (x / (a * b)) := by rw [map_div₀, map_mul]
  rw [e1, e2, e3, key, key, key]

open IsDedekindDomain in
/-- **The local condition at `v = (p)` is the one over `ℚ_p`.** -/
theorem locM_adicCompletion_iff (v : HeightOneSpectrum ℤ) (ℓ a b : ℚ) :
    LocM (v.adicCompletion ℚ) (algebraMap ℚ _ ℓ) (algebraMap ℚ _ a) (algebraMap ℚ _ b) ↔
      LocM ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ℓ a b := by
  -- the continuous `ℚ`-algebra isomorphism `v.adicCompletion ℚ ≃ ℚ_[p]`, as a ring isomorphism
  let φ : v.adicCompletion ℚ ≃+* ℚ_[Rat.HeightOneSpectrum.primesEquiv v] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv
  have hφ : ∀ q : ℚ, φ (algebraMap ℚ _ q) = (q : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) :=
    fun q => by rw [eq_ratCast (algebraMap ℚ _), map_ratCast]
  rw [← locM_ringEquiv φ, hφ, hφ, hφ]

open IsDedekindDomain in
/-- **The finite places of `ℚ` are the primes.** -/
theorem forall_locM_adicCompletion_iff (ℓ a b : ℚ) :
    (∀ v : HeightOneSpectrum ℤ,
      LocM (v.adicCompletion ℚ) (algebraMap ℚ _ ℓ) (algebraMap ℚ _ a) (algebraMap ℚ _ b)) ↔
      ∀ (p : ℕ) [Fact p.Prime], LocM ℚ_[p] ℓ a b := by
  constructor
  · intro h p hp
    obtain ⟨v, hv⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).surjective ⟨p, hp.out⟩
    have h' := (locM_adicCompletion_iff v ℓ a b).mp (h v)
    rw [hv] at h'
    exact h'
  · intro h v
    exact (locM_adicCompletion_iff v ℓ a b).mpr (h _)

/-! ### The local conditions of `E_ℓ` in x-form -/

section LocalConditions

variable {K : Type*} [Field K] [CharZero K] {W : WeierstrassCurve K} {ℓ : K}
  (h : IsCurveM W ℓ) (hℓ : ℓ ≠ 0)

open scoped Classical in
include h hℓ in
/-- **The local `2`-descent condition at `L` in x-form**: a square class with coordinates
`(a, b, ab)` satisfies the local condition at an extension field `L` (of characteristic zero)
exactly when `LocM L ℓ a b` holds over `L`. -/
theorem mem_localCondition_iff_locM (L : Type*) [Field L] [CharZero L] [Algebra K L]
    (m : W.toAffine.M) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : ∀ i, coord h i m = ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)] i) :
    haveI := h.isCharNeTwoNF
    haveI := h.isElliptic hℓ
    m ∈ W.toAffine.localCondition L ↔
      LocM L (algebraMap K L ℓ) (algebraMap K L a) (algebraMap K L b) := by
  have := h.isCharNeTwoNF
  have := h.isElliptic hℓ
  have hL := h.baseChange L
  have hℓL : algebraMap K L ℓ ≠ 0 := (_root_.map_ne_zero _).mpr hℓ
  have haL : algebraMap K L a ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have hbL : algebraMap K L b ≠ 0 := (_root_.map_ne_zero _).mpr hb
  rw [mem_localCondition_iff, MonoidHom.mem_range]
  have key : ∀ P : (W⁄L).toAffine.Point,
      μ (W := (W⁄L).toAffine) (.ofAdd P) = W.toAffine.localRes L m ↔
        ∀ i, coord hL i (μ (W := (W⁄L).toAffine) (.ofAdd P)) =
          ![sq _ haL, sq _ hbL, sq _ (mul_ne_zero haL hbL)] i := by
    intro P
    have hinj := coord_injective hL hℓL
    constructor
    · intro hP i
      rw [hP, coord_localRes h L i m, hm i]
      fin_cases i <;> simp [SqCl.map_sq]
    · intro hP
      apply hinj
      funext i
      show coord hL i _ = coord hL i _
      rw [hP i, coord_localRes h L i m, hm i]
      fin_cases i <;> simp [SqCl.map_sq]
  constructor
  · rintro ⟨P, hP⟩
    exact (exists_coord_μ_iff_locM hL hℓL _ _ haL hbL).mp ⟨Multiplicative.toAdd P, (key _).mp hP⟩
  · intro hloc
    obtain ⟨P, hP⟩ := (exists_coord_μ_iff_locM hL hℓL _ _ haL hbL).mpr hloc
    exact ⟨Multiplicative.ofAdd P, (key P).mpr hP⟩

end LocalConditions

/-! ### Over `ℚ`: `SelM ℓ` is the explicit `2`-Selmer group of `E_ℓ` -/

theorem isCurveM_curve (ℓ : ℚ) : IsCurveM (ZInQ.Manuscript.curve ℓ) ℓ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The explicit `2`-Selmer system of `E_ℓ`** (`diophantine_zq.tex` lines 1033–1074; the
descent lane's `ZInQ.Manuscript.PoleRC.SelM`): the pairs `(a, b)` of squarefree integers whose
class is in the local Kummer image over `ℝ` and over every `ℚ_p`. -/
def SelM (ℓ : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ LocM ℝ ℓ ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], LocM ℚ_[p] ℓ ab.1 ab.2}

theorem sq_mul_sq_mul {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    sq a ha * sq b hb * sq (a * b) (mul_ne_zero ha hb) = 1 := by
  simp only [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  refine ⟨Units.mk0 (a * b) (mul_ne_zero ha hb), ?_⟩
  ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul]
  ring

theorem cast_locM_iff {L : Type*} [Field L] [Algebra ℚ L] (ℓ a b : ℚ) :
    LocM L (algebraMap ℚ L ℓ) (algebraMap ℚ L a) (algebraMap ℚ L b) ↔ LocM L ℓ a b := by
  simp only [eq_ratCast]

open IsDedekindDomain in
open scoped Classical in
/-- **Membership in the explicit `2`-Selmer group of `E_ℓ` in x-form**: a square class with
coordinates `(a, b, ab)` is in `Sel₂(E_ℓ/ℚ)` exactly when `LocM` holds over `ℝ` and every `ℚ_p`. -/
theorem mem_selmerGroup₂_iff_locM {ℓ : ℚ} (hℓ : ℓ ≠ 0)
    (m : (ZInQ.Manuscript.curve ℓ).toAffine.M) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : ∀ i, coord (isCurveM_curve ℓ) i m =
      ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)] i) :
    haveI := (isCurveM_curve ℓ).isCharNeTwoNF
    haveI := (isCurveM_curve ℓ).isElliptic hℓ
    m ∈ (ZInQ.Manuscript.curve ℓ).toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ) ↔
      LocM ℝ ℓ a b ∧ ∀ (p : ℕ) [Fact p.Prime], LocM ℚ_[p] ℓ a b := by
  have h := isCurveM_curve ℓ
  have := h.isCharNeTwoNF
  have := h.isElliptic hℓ
  rw [mem_selmerGroup₂_iff]
  have hn : normM (W := (ZInQ.Manuscript.curve ℓ).toAffine) m = 1 := by
    rw [normM_eq_coord_mul h m, hm 0, hm 1, hm 2]
    exact sq_mul_sq_mul a b ha hb
  have hfin : (∀ v : HeightOneSpectrum ℤ,
      m ∈ (ZInQ.Manuscript.curve ℓ).toAffine.localCondition (v.adicCompletion ℚ)) ↔
      ∀ (p : ℕ) [Fact p.Prime], LocM ℚ_[p] ℓ a b := by
    rw [← forall_locM_adicCompletion_iff]
    refine forall_congr' fun v => ?_
    let _ : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v
    have : CharZero (v.adicCompletion ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
    rw [mem_localCondition_iff_locM h hℓ (v.adicCompletion ℚ) m a b ha hb hm]
  have hinf : (∀ i : Unit, m ∈ (ZInQ.Manuscript.curve ℓ).toAffine.localCondition ℝ) ↔
      LocM ℝ ℓ a b := by
    rw [← cast_locM_iff, ← mem_localCondition_iff_locM h hℓ ℝ m a b ha hb hm]
    exact ⟨fun h' => h' (), fun h' _ => h'⟩
  rw [hfin, hinf]
  exact ⟨fun h' => ⟨h'.2.2, h'.2.1⟩, fun h' => ⟨hn, h'.2, h'.1⟩⟩

theorem sq_mul {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    sq a ha * sq b hb = sq (a * b) (mul_ne_zero ha hb) := by
  simp only [sq, ← QuotientGroup.mk_mul]
  congr 1
  ext
  simp

theorem SqCl.mul_self {K : Type*} [Field K] (c : SqCl K) : c * c = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact ⟨u, by simp [powMonoidHom_apply, pow_two]⟩

/-- The squarefree representative of a square class of `ℚ`. -/
noncomputable def sqfreeRep : SqCl ℚ ≃ {z : ℤ // Squarefree z} :=
  (Equiv.ofBijective _ sqfree_bijective).symm

theorem sq_sqfreeRep (c : SqCl ℚ) :
    sq ((sqfreeRep c : ℤ) : ℚ) (by exact_mod_cast (sqfreeRep c).2.ne_zero) = c :=
  (Equiv.ofBijective _ sqfree_bijective).apply_symm_apply c

theorem sqfreeRep_sq (z : ℤ) (hz : Squarefree z) :
    sqfreeRep (sq (z : ℚ) (by exact_mod_cast hz.ne_zero)) = ⟨z, hz⟩ :=
  (Equiv.ofBijective _ sqfree_bijective).symm_apply_apply ⟨z, hz⟩

theorem locM_cast_iff_real (ℓ : ℕ) (a b : ℤ) :
    LocM ℝ (((ℓ : ℚ)) : ℝ) ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) ↔ LocM ℝ ℓ a b := by
  simp only [Rat.cast_natCast, Rat.cast_intCast]

theorem locM_cast_iff_padic (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (a b : ℤ) :
    LocM ℚ_[p] (((ℓ : ℚ)) : ℚ_[p]) ((a : ℚ) : ℚ_[p]) ((b : ℚ) : ℚ_[p]) ↔ LocM ℚ_[p] ℓ a b := by
  simp only [Rat.cast_natCast, Rat.cast_intCast]

section Rat

variable {ℓ : ℕ} [NeZero ℓ]

theorem natCast_ne_zero' : (ℓ : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ

instance : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.IsCharNeTwoNF :=
  (isCurveM_curve _).isCharNeTwoNF

instance : (ZInQ.Manuscript.curve (ℓ : ℚ)).IsElliptic :=
  (isCurveM_curve _).isElliptic natCast_ne_zero'

/-- The square class of the étale algebra of `E_ℓ` with coordinates `(a, b, ab)`. -/
noncomputable def cls (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M :=
  Classical.choose (coord_surjective (isCurveM_curve (ℓ : ℚ)) natCast_ne_zero'
    ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)])

theorem coord_cls (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    coord (isCurveM_curve (ℓ : ℚ)) i (cls (ℓ := ℓ) a b ha hb) =
      ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)] i :=
  congrFun (Classical.choose_spec (coord_surjective (isCurveM_curve (ℓ : ℚ)) natCast_ne_zero'
    ![sq a ha, sq b hb, sq (a * b) (mul_ne_zero ha hb)])) i

theorem coord_two_eq (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M)
    (hn : normM (W := (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine) m = 1) :
    coord (isCurveM_curve (ℓ : ℚ)) 2 m =
      coord (isCurveM_curve (ℓ : ℚ)) 0 m * coord (isCurveM_curve (ℓ : ℚ)) 1 m := by
  rw [normM_eq_coord_mul (isCurveM_curve (ℓ : ℚ)) m] at hn
  rw [eq_inv_of_mul_eq_one_right hn]
  exact inv_eq_of_mul_eq_one_right (SqCl.mul_self _)

/-- The squarefree representatives of the first two coordinates. -/
noncomputable def rep01 (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M) : ℤ × ℤ :=
  ((sqfreeRep (coord (isCurveM_curve (ℓ : ℚ)) 0 m) : ℤ),
    (sqfreeRep (coord (isCurveM_curve (ℓ : ℚ)) 1 m) : ℤ))

theorem rep01_fst_ne_zero (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M) :
    ((rep01 m).1 : ℚ) ≠ 0 := by
  exact_mod_cast (sqfreeRep _).2.ne_zero

theorem rep01_snd_ne_zero (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M) :
    ((rep01 m).2 : ℚ) ≠ 0 := by
  exact_mod_cast (sqfreeRep _).2.ne_zero

open scoped Classical in
theorem coord_eq_rep01 (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M)
    (hm : m ∈ (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ))
    (i : Fin 3) :
    coord (isCurveM_curve (ℓ : ℚ)) i m =
      ![sq _ (rep01_fst_ne_zero m), sq _ (rep01_snd_ne_zero m),
        sq _ (mul_ne_zero (rep01_fst_ne_zero m) (rep01_snd_ne_zero m))] i := by
  have h0 : sq _ (rep01_fst_ne_zero m) = coord (isCurveM_curve (ℓ : ℚ)) 0 m := sq_sqfreeRep _
  have h1 : sq _ (rep01_snd_ne_zero m) = coord (isCurveM_curve (ℓ : ℚ)) 1 m := sq_sqfreeRep _
  fin_cases i
  · exact h0.symm
  · exact h1.symm
  · show coord (isCurveM_curve (ℓ : ℚ)) 2 m = _
    rw [← sq_mul _ _ (rep01_fst_ne_zero m) (rep01_snd_ne_zero m), h0, h1]
    exact coord_two_eq m ((mem_selmerGroup₂_iff _ _ _).mp hm).1

open scoped Classical in
theorem cls_mem (ab : SelM ℓ) :
    cls (ℓ := ℓ) (ab.1.1 : ℚ) (ab.1.2 : ℚ) (by exact_mod_cast ab.2.1.ne_zero)
        (by exact_mod_cast ab.2.2.1.ne_zero) ∈
      (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ) := by
  rw [mem_selmerGroup₂_iff_locM natCast_ne_zero' _ _ _ _ _ (coord_cls _ _ _ _)]
  exact ⟨(locM_cast_iff_real ℓ _ _).mpr ab.2.2.2.1, fun p _ =>
    (locM_cast_iff_padic p ℓ _ _).mpr (ab.2.2.2.2 p)⟩

open scoped Classical in
theorem rep01_mem (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ)) :
    rep01 (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M) ∈ SelM ℓ := by
  refine ⟨(sqfreeRep _).2, (sqfreeRep _).2, ?_⟩
  have hl := (mem_selmerGroup₂_iff_locM natCast_ne_zero' (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M)
    _ _ _ _ (coord_eq_rep01 _ m.2)).mp m.2
  exact ⟨(locM_cast_iff_real ℓ _ _).mp hl.1, fun p _ => (locM_cast_iff_padic p ℓ _ _).mp (hl.2 p)⟩

open scoped Classical in
/-- **`SelM ℓ` is the explicit `2`-Selmer group of `E_ℓ`** (Silverman X.1.4): the pair `(a, b)` of
squarefree integers corresponds to the square class of the étale algebra with coordinates
`(a, b, ab)` in the manuscript's Kummer coordinates `(x + 3ℓ, x − ℓ, x)`. -/
noncomputable def selMEquiv :
    SelM ℓ ≃ (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ) where
  toFun ab := ⟨_, cls_mem ab⟩
  invFun m := ⟨_, rep01_mem m⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    simp only [rep01, coord_cls, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [sqfreeRep_sq a hab.1, sqfreeRep_sq b hab.2.1]
  right_inv := by
    rintro ⟨m, hm⟩
    apply Subtype.ext
    apply coord_injective (isCurveM_curve (ℓ : ℚ)) natCast_ne_zero'
    funext i
    show coord _ i (cls _ _ _ _) = coord _ i m
    rw [coord_cls, coord_eq_rep01 m hm i]

/-- **`#SelM ℓ = #Sel₂(E_ℓ/ℚ)`** for the explicit `2`-Selmer group of the étale algebra. -/
theorem ncard_selM :
    (SelM ℓ).ncard = Nat.card ((ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.selmerGroup₂ ℤ
      (fun _ : Unit => ℝ)) := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr selMEquiv

end Rat

end ZInQ.Manuscript.SelmerSplit
