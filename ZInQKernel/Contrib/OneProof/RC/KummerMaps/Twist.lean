import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Model
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Lane RC29 (Kummer maps), part 1: the quadratic-twist identification `E^{(h)}[m] ≅ E[m](χ_h)`

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-local-kummer` (tex 3413–3438): "For the
actual local twist `B = E^{(h)}` over `F = K_v`, the condition `U_F = B(F)^∧_2[−1] → RΓ(F, T_2B)`
… At `v ∣ 2N`, `Ψ_i` is trivial, so derived coefficient extension defines the scalar `A_i`
condition for this actual twist", with the coefficient module `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)` of tex
2724–2727. Restricted to `G_{K_v}` (where `Ψ_i = 1`), `M_i` is `(E[2^i] ⊗ A_i)(χ_h)`, and the
text's tacit identification `T_2B ≅ T_2E(χ_h)` (at finite level `B[2^i] ≅ E[2^i](χ_h)`) is what
carries the local condition of `B = E^{(h)}` into the cochains of `M_i`.

This file proves that identification at finite level, explicitly, for a curve `W` over a field
`F` with `2 ≠ 0` and the twist `twistK W h` of lane RC18 (`y² = x³ + h b₂/4 x² + h² b₄/2 x +
h³ b₆/4`, the blueprint's `qtwist`):

* `twistVariableChange W q hq`: for `q ≠ 0`, the admissible change of variables
  `u = q⁻¹, r = 0, s = −a₁/2, t = −a₃/2`; `twistVariableChange_smul`: it carries `W` to
  `twistK W (q²)` (PROVED; this is the quadratic-twist isomorphism over `F(√h)`).
* `twistPointEquiv`: the resulting group isomorphism `(twistK W d)(L) ≃+ W(L)` over any field `L`
  with `2 ≠ 0` and `q² = d` (the vendored Tau Ceti change-of-variables isomorphism of point
  groups); on coordinates `(x, y) ↦ (x/q², y/q³ − (a₁ x/q² + a₃)/2)` (`twistPointEquiv_some`).
* Over `F̄` (Mathlib's `AlgebraicClosure F`), for a square root `q ∈ F̄` of `h`:
  `twistPt : B(F̄) ≃+ E(F̄)` (`B = twistK W h`, in lane RC28's `PtAlg`), and its restriction
  `twistTors : B(F̄)[m] ≃+ E(F̄)[m]` (lane RC28's `TorsAlg`).
* `twistSign q σ ∈ {±1}`: the quadratic character of `F(√h)/F` read on `G_F`, `σ q = ±q`
  (`twistSign_spec`); **`twistPt_smul`, `twistTors_smul`: `ι(σ t) = χ_h(σ) · σ ι(t)`** — the
  identification is `G_F`-equivariant from `B[m]` to `E[m](χ_h)` (PROVED).

Kinds: definitions and PROVED (no hypotheses beyond `2 ≠ 0`, `h ≠ 0`, `q² = h`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open WeierstrassCurve ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.TwistDictionary

/-! ### The twist as a change of variables -/

section General

variable {L : Type*} [Field L]

/-- Definition (tex 3413–3416: the twist `B = E^{(h)}` against `E` over `F(√h)`). **The change of
variables of the quadratic twist**: for `q ≠ 0` (a square root of the twisting parameter),
`u = q⁻¹`, `r = 0`, `s = −a₁/2`, `t = −a₃/2`, i.e. `(x, y) ↦ (u²x, u³y − (a₁u²x + a₃)/2)`. -/
def twistVariableChange (W : WeierstrassCurve L) (q : L) (hq : q ≠ 0) : VariableChange L where
  u := Units.mk0 q⁻¹ (inv_ne_zero hq)
  r := 0
  s := -W.a₁ / 2
  t := -W.a₃ / 2

theorem twistVariableChange_u_inv (W : WeierstrassCurve L) {q : L} (hq : q ≠ 0) :
    (((twistVariableChange W q hq).u⁻¹ : Lˣ) : L) = q := by
  simp [twistVariableChange]

theorem twistVariableChange_u (W : WeierstrassCurve L) {q : L} (hq : q ≠ 0) :
    (((twistVariableChange W q hq).u : Lˣ) : L) = q⁻¹ := by
  simp [twistVariableChange]

/-- PROVED (tex 3413–3416). **The change of variables `twistVariableChange W q` carries `W` to its
quadratic twist by `q²`** (lane RC18's `twistK`), for `2 ≠ 0`. -/
theorem twistVariableChange_smul (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) {q d : L}
    (hq : q ≠ 0) (hqd : q ^ 2 = d) : twistVariableChange W q hq • W = twistK W d := by
  subst hqd
  have hu := twistVariableChange_u_inv W hq
  have h4 : (4 : L) ≠ 0 := four_ne_zero_of_two h2
  ext
  · rw [variableChange_a₁, hu]
    simp only [twistVariableChange, twistK]
    field_simp
    ring
  · rw [variableChange_a₂, hu]
    simp only [twistVariableChange, twistK, b₂]
    field_simp
    ring
  · rw [variableChange_a₃, hu]
    simp only [twistVariableChange, twistK]
    field_simp
    ring
  · rw [variableChange_a₄, hu]
    simp only [twistVariableChange, twistK, b₄]
    field_simp
    ring
  · rw [variableChange_a₆, hu]
    simp only [twistVariableChange, twistK, b₆]
    field_simp
    ring

variable [DecidableEq L]

/-- Definition (tex 3413–3416). **The quadratic-twist isomorphism of point groups**
`(twistK W d)(L) ≃+ W(L)` for `q² = d`, `q ≠ 0`, `2 ≠ 0` in `L`: transport along
`twistVariableChange_smul`, then the change-of-variables isomorphism (vendored Tau Ceti
`Affine.Point.addEquivVariableChange`, a group isomorphism over a field). -/
def twistPointEquiv (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) {q d : L} (hq : q ≠ 0)
    (hqd : q ^ 2 = d) : (twistK W d).toAffine.Point ≃+ W.toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve L => V.toAffine.Point)
    (twistVariableChange_smul h2 W hq hqd).symm).trans
    (Affine.Point.addEquivVariableChange W (twistVariableChange W q hq))

/-- PROVED (tex 3413–3416). The twist isomorphism fixes the point at infinity. -/
theorem twistPointEquiv_zero (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) {q d : L} (hq : q ≠ 0)
    (hqd : q ^ 2 = d) : twistPointEquiv h2 W hq hqd 0 = 0 :=
  map_zero _

/-- PROVED (tex 3413–3416). **The twist isomorphism on coordinates**:
`(x, y) ↦ (q⁻² x, q⁻³ y + q⁻² (−a₁/2) x − a₃/2)`. -/
theorem twistPointEquiv_some (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) {q d : L} (hq : q ≠ 0)
    (hqd : q ^ 2 = d) {x y : L} (hxy : (twistK W d).toAffine.Nonsingular x y)
    (hxy' : W.toAffine.Nonsingular (q⁻¹ ^ 2 * x)
      (q⁻¹ ^ 3 * y + q⁻¹ ^ 2 * (-W.a₁ / 2) * x + -W.a₃ / 2)) :
    twistPointEquiv h2 W hq hqd (.some x y hxy) = .some _ _ hxy' := by
  have hns : (twistVariableChange W q hq • W).toAffine.Nonsingular x y :=
    (twistVariableChange_smul h2 W hq hqd).symm ▸ hxy
  have e1 : twistPointEquiv h2 W hq hqd (.some x y hxy) =
      Affine.Point.equivVariableChange W (twistVariableChange W q hq) (.some x y hns) := by
    simp only [twistPointEquiv, AddEquiv.trans_apply, AddEquiv.cast_apply,
      Affine.Point.coe_addEquivVariableChange]
    congr 1
    exact Affine.Point.cast_some (twistVariableChange_smul h2 W hq hqd).symm hxy
  rw [e1, Affine.Point.equivVariableChange_some]
  simp [twistVariableChange]

omit [DecidableEq L] in
/-- PROVED (tex 3413–3416). The target coordinates of the twist isomorphism are a nonsingular
point of `W` (from the change-of-variables formula). -/
theorem twistPointEquiv_nonsingular (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) {q d : L}
    (hq : q ≠ 0) (hqd : q ^ 2 = d) {x y : L} (hxy : (twistK W d).toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (q⁻¹ ^ 2 * x) (q⁻¹ ^ 3 * y + q⁻¹ ^ 2 * (-W.a₁ / 2) * x + -W.a₃ / 2) := by
  have hns : (twistVariableChange W q hq • W).toAffine.Nonsingular x y :=
    (twistVariableChange_smul h2 W hq hqd).symm ▸ hxy
  have h := (Affine.variableChange_nonsingular W (twistVariableChange W q hq) x y).mpr hns
  simpa [twistVariableChange_u, twistVariableChange] using h

end General

/-! ### Over the algebraic closure of `F`, with the Galois action -/

section Galois

variable {F : Type} [Field F] (W : WeierstrassCurve F) (h : F)

/-- PROVED (tex 3413–3416). Over `F̄`, `twistVariableChange` carries the base change of `W` to the
base change of the twist `twistK W h` (lane RC18's `twistK_map`), for `q² = h`. -/
theorem twistVariableChange_smul_baseChange (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F}
    (hq : q ≠ 0) (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) :
    twistVariableChange (W.baseChange (AlgebraicClosure F)) q hq • W.baseChange (AlgebraicClosure F)
      = (twistK W h).baseChange (AlgebraicClosure F) := by
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (AlgebraicClosure F)) 2]
    exact (map_ne_zero _).2 h2
  rw [twistVariableChange_smul h2' _ hq hqh]
  exact (twistK_map W (algebraMap F (AlgebraicClosure F)) h).symm

open scoped Classical in
/-- Definition (tex 3413–3416, 3430–3432). **The twist identification `B(F̄) ≃+ E(F̄)`** for
`B = twistK W h` and a square root `q ∈ F̄` of `h ≠ 0` (lane RC28's `PtAlg`, the points over
`F̄ = AlgebraicClosure F` with the Galois action). -/
def twistPt (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) : PtAlg F (twistK W h) ≃+ PtAlg F W :=
  ((ptEquiv F (twistK W h)).symm.trans
    (AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure F) => V.toAffine.Point)
      (twistVariableChange_smul_baseChange W h h2 hq hqh).symm)).trans
    ((Affine.Point.addEquivVariableChange (W.baseChange (AlgebraicClosure F))
      (twistVariableChange (W.baseChange (AlgebraicClosure F)) q hq)).trans (ptEquiv F W))

open scoped Classical in
/-- PROVED (tex 3413–3416). `twistPt` on coordinates: `(x, y) ↦ (q⁻² x, q⁻³ y − (a₁ q⁻² x + a₃)/2)`
(with `a₁, a₃` the coefficients of `W` in `F̄`). -/
theorem twistPt_some (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) {x y : AlgebraicClosure F}
    (hxy : ((twistK W h).baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y)
    (hxy' : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular (q⁻¹ ^ 2 * x)
        (q⁻¹ ^ 3 * y + q⁻¹ ^ 2 * (-(algebraMap F (AlgebraicClosure F) W.a₁) / 2) * x +
          -(algebraMap F (AlgebraicClosure F) W.a₃) / 2)) :
    twistPt W h h2 hq hqh (ptEquiv F (twistK W h) (.some x y hxy)) =
      ptEquiv F W (.some _ _ hxy') := by
  have hns : (twistVariableChange (W.baseChange (AlgebraicClosure F)) q hq •
      W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y :=
    (twistVariableChange_smul_baseChange W h h2 hq hqh).symm ▸ hxy
  have e1 : twistPt W h h2 hq hqh (ptEquiv F (twistK W h) (.some x y hxy)) =
      ptEquiv F W (Affine.Point.equivVariableChange (W.baseChange (AlgebraicClosure F))
        (twistVariableChange (W.baseChange (AlgebraicClosure F)) q hq) (.some x y hns)) := by
    simp only [twistPt, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, AddEquiv.cast_apply,
      Affine.Point.coe_addEquivVariableChange]
    congr 2
    exact Affine.Point.cast_some (twistVariableChange_smul_baseChange W h h2 hq hqh).symm hxy
  rw [e1, Affine.Point.equivVariableChange_some]
  congr 1
  simp [twistVariableChange, WeierstrassCurve.baseChange]

/-- PROVED (tex 3413–3416). Over `F̄`, the target coordinates of `twistPt` are a nonsingular point
of `W`. -/
theorem twistPt_nonsingular (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) {x y : AlgebraicClosure F}
    (hxy : ((twistK W h).baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
    (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular (q⁻¹ ^ 2 * x)
        (q⁻¹ ^ 3 * y + q⁻¹ ^ 2 * (-(algebraMap F (AlgebraicClosure F) W.a₁) / 2) * x +
          -(algebraMap F (AlgebraicClosure F) W.a₃) / 2) := by
  have hns : (twistVariableChange (W.baseChange (AlgebraicClosure F)) q hq •
      W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y :=
    (twistVariableChange_smul_baseChange W h h2 hq hqh).symm ▸ hxy
  have h := (Affine.variableChange_nonsingular (W.baseChange (AlgebraicClosure F))
    (twistVariableChange (W.baseChange (AlgebraicClosure F)) q hq) x y).mpr hns
  simpa [twistVariableChange_u, twistVariableChange, WeierstrassCurve.baseChange] using h

/-! ### The quadratic character and the equivariance -/

open scoped Classical in
/-- Definition (tex 2726, 3431–3433: `χ_h` on the decomposition group). **The quadratic character
of `F(√h)/F` on `G_F`**, read on a square root `q ∈ F̄` of `h`: `σ ↦ 1` if `σ q = q`, else `−1`. -/
def twistSign (q : AlgebraicClosure F) (σ : Field.absoluteGaloisGroup F) : ℤˣ :=
  if σ.toAlgHom q = q then 1 else -1

/-- PROVED. `σ(√h) = ±√h`, and `twistSign` records the sign. -/
theorem twistSign_cases {q : AlgebraicClosure F}
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) (σ : Field.absoluteGaloisGroup F) :
    (twistSign q σ = 1 ∧ σ.toAlgHom q = q) ∨ (twistSign q σ = -1 ∧ σ.toAlgHom q = -q) := by
  classical
  by_cases h' : σ.toAlgHom q = q
  · left
    exact ⟨by simp [twistSign, h'], h'⟩
  · right
    have hsq : (σ.toAlgHom q) ^ 2 = q ^ 2 := by
      rw [← map_pow, hqh, AlgHom.commutes]
    refine ⟨by simp [twistSign, h'], ?_⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact absurd h1 h'
    · exact h1

/-- PROVED (tex 3431–3433). **`σ(√h) = χ_h(σ) √h`** on `G_F`. -/
theorem twistSign_spec {q : AlgebraicClosure F}
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) (σ : Field.absoluteGaloisGroup F) :
    σ.toAlgHom q = ((twistSign q σ : ℤˣ) : ℤ) • q := by
  rcases twistSign_cases h hqh σ with ⟨hs, hq'⟩ | ⟨hs, hq'⟩
  · rw [hs, hq', Units.val_one, one_smul]
  · rw [hs, hq', Units.val_neg, Units.val_one, neg_one_zsmul]

open scoped Classical in
/-- PROVED (tex 3413–3416). `twistPt` on a point given by coordinates, with the target
nonsingularity supplied by `twistPt_nonsingular`. -/
theorem twistPt_some' (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) {x y : AlgebraicClosure F}
    (hxy : ((twistK W h).baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
    twistPt W h h2 hq hqh (ptEquiv F (twistK W h) (.some x y hxy)) =
      ptEquiv F W (.some _ _ (twistPt_nonsingular W h h2 hq hqh hxy)) :=
  twistPt_some W h h2 hq hqh hxy _

open scoped Classical in
/-- PROVED (tex 3413–3432). **The twist identification is `G_F`-equivariant from `B(F̄)` to
`E(F̄)(χ_h)`**: `twistPt (σ P) = χ_h(σ) · σ (twistPt P)` for `σ ∈ G_F`, `χ_h = twistSign q`. -/
theorem twistPt_smul (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) (σ : Field.absoluteGaloisGroup F)
    (P : PtAlg F (twistK W h)) :
    twistPt W h h2 hq hqh (σ • P) =
      ((twistSign q σ : ℤˣ) : ℤ) • (σ • twistPt W h h2 hq hqh P) := by
  obtain ⟨P, rfl⟩ := (ptEquiv F (twistK W h)).surjective P
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, smul_zero, map_zero, smul_zero, smul_zero]
  · rw [smul_ptEquiv, Affine.Point.map_some, twistPt_some', twistPt_some', smul_ptEquiv,
      Affine.Point.map_some]
    have h1 : σ.toAlgHom (algebraMap F (AlgebraicClosure F) W.a₁) =
        algebraMap F (AlgebraicClosure F) W.a₁ := AlgHom.commutes _ _
    have h3 : σ.toAlgHom (algebraMap F (AlgebraicClosure F) W.a₃) =
        algebraMap F (AlgebraicClosure F) W.a₃ := AlgHom.commutes _ _
    rcases twistSign_cases h hqh σ with ⟨hs, hσq⟩ | ⟨hs, hσq⟩
    · rw [hs, Units.val_one, one_smul]
      congr 1
      simp only [Affine.Point.some.injEq]
      constructor
      · simp only [map_mul, map_pow, map_inv₀, hσq]
      · simp only [map_add, map_mul, map_pow, map_inv₀, map_div₀, map_neg, map_ofNat, hσq, h1, h3]
    · rw [hs, Units.val_neg, Units.val_one, neg_one_zsmul, ← map_neg (ptEquiv F W),
        Affine.Point.neg_some]
      congr 1
      simp only [Affine.Point.some.injEq]
      constructor
      · simp only [map_mul, map_pow, map_inv₀, hσq, inv_neg, even_two, Even.neg_pow]
      · simp only [map_add, map_mul, map_pow, map_inv₀, map_div₀, map_neg, map_ofNat, hσq, h1, h3,
          Affine.negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
        have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
          rw [← map_ofNat (algebraMap F (AlgebraicClosure F)) 2]
          exact (map_ne_zero _).2 h2
        field_simp
        ring

/-! ### Restriction to the `m`-torsion -/

open scoped Classical in
/-- Definition (tex 3415–3417, 3430–3432). **The twist identification on `m`-torsion**,
`B(F̄)[m] ≃+ E(F̄)[m]` (lane RC28's `TorsAlg`), the restriction of `twistPt`. -/
def twistTors (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) (m : ℕ) :
    TorsAlg F (twistK W h) m ≃+ TorsAlg F W m where
  toFun t := ⟨twistPt W h h2 hq hqh (t : PtAlg F (twistK W h)), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 t.2,
      map_zero]⟩
  invFun t := ⟨(twistPt W h h2 hq hqh).symm (t : PtAlg F W), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 t.2,
      map_zero]⟩
  left_inv t := Subtype.ext ((twistPt W h h2 hq hqh).symm_apply_apply (t : PtAlg F (twistK W h)))
  right_inv t := Subtype.ext ((twistPt W h h2 hq hqh).apply_symm_apply (t : PtAlg F W))
  map_add' s t := Subtype.ext (map_add (twistPt W h h2 hq hqh) (s : PtAlg F (twistK W h)) t)

/-- PROVED. `twistTors` on underlying points is `twistPt`. -/
theorem coe_twistTors (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) (m : ℕ) (t : TorsAlg F (twistK W h) m) :
    (twistTors W h h2 hq hqh m t : PtAlg F W) = twistPt W h h2 hq hqh (t : PtAlg F (twistK W h)) :=
  rfl

/-- PROVED (tex 3413–3432). **`B[m] ≅ E[m](χ_h)` as `G_F`-modules**:
`twistTors (σ t) = χ_h(σ) · σ (twistTors t)`. -/
theorem twistTors_smul (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) h) (m : ℕ) (σ : Field.absoluteGaloisGroup F)
    (t : TorsAlg F (twistK W h) m) :
    twistTors W h h2 hq hqh m (σ • t) =
      ((twistSign q σ : ℤˣ) : ℤ) • (σ • twistTors W h h2 hq hqh m t) := by
  apply Subtype.ext
  rw [coe_twistTors, coe_smul_torsAlg, twistPt_smul, AddSubgroup.coe_zsmul, coe_smul_torsAlg,
    coe_twistTors]


end Galois

end ZInQ.Manuscript.RC.KummerMaps
