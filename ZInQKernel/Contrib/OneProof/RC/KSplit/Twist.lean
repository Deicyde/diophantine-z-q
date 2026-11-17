import ZInQKernel.RouteK.Rank.LFunctionCd
import ZInQKernel.Contrib.PoleRC.KummerF

/-!
# Lane RC3: the reductions of `E^{(k)}` and `E_ℓ` are isomorphic when `k` is a square mod `p`

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:sec7-ksplit-seed`, tex 2645–2647 ("Because `k`
is a square modulo `p`, the reductions of `E^{(k)}` and `E_ℓ` are isomorphic over `𝔽_p`"), and
Proposition `ex:app-nonempty-seeds`, tex 10488–10490.

The twist `E^{(k)}` of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` is `y² = x(x − kℓ)(x + 3kℓ)`; over a field in
which `k = s²`, its reduction `curveF (s² L)` is the change of variables of `curveF L` by
`(x, y) ↦ (s² x, s³ y)`, i.e. by `u = s⁻¹` (`curveF_sq_mul_eq_smul`). Isomorphic Weierstrass curves
have the same number of points (`natCard_curveF_sq_mul`, through the tree's
`ZInQ.Literature.natCard_point_variableChange`). All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.KSplit

open WeierstrassCurve ZInQ.Manuscript.PoleRC

variable {F : Type*} [Field F]

/-- The change of variables `u = s⁻¹`, `r = s = t = 0`, i.e. `(x, y) ↦ (s² x, s³ y)`. -/
def twistChange (s : F) (hs : s ≠ 0) : VariableChange F :=
  ⟨Units.mk0 s⁻¹ (inv_ne_zero hs), 0, 0, 0⟩

/-- **`curveF (s² L)` is isomorphic to `curveF L`** (`PROVED`; tex 2645–2647): it is the change of
variables of `curveF L` by `u = s⁻¹`. -/
theorem curveF_sq_mul_eq_smul (s : F) (hs : s ≠ 0) (L : F) :
    curveF (s ^ 2 * L) = twistChange s hs • curveF L := by
  ext <;> simp [twistChange, curveF, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> ring

/-- `curveF L` is an elliptic curve when `2, 3, L ≠ 0`. -/
theorem curveF_isElliptic (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {L : F} (hL : L ≠ 0) :
    (curveF L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (curveF_Δ_ne_zero h2 h3 hL)⟩

/-- **The reductions have the same number of points** (`PROVED`; tex 2645–2647, 10488–10490):
`#E_{s²L}(F) = #E_L(F)`. -/
theorem natCard_curveF_sq_mul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {L : F} (hL : L ≠ 0)
    {s : F} (hs : s ≠ 0) :
    Nat.card (curveF (s ^ 2 * L)).toAffine.Point = Nat.card (curveF L).toAffine.Point := by
  have := curveF_isElliptic h2 h3 hL
  rw [curveF_sq_mul_eq_smul s hs L]
  exact ZInQ.Literature.natCard_point_variableChange _ _

/-- **The form used for the twist**: if `K = s²` is a nonzero square in `F`, then
`#E_{K·L}(F) = #E_L(F)` (`PROVED`; tex 2645–2647: `E^{(k)}` reduces to `curveF (k ℓ mod p)`). -/
theorem natCard_curveF_mul_of_isSquare (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {L : F} (hL : L ≠ 0)
    {K : F} (hK : IsSquare K) (hK0 : K ≠ 0) :
    Nat.card (curveF (K * L)).toAffine.Point = Nat.card (curveF L).toAffine.Point := by
  obtain ⟨s, rfl⟩ := hK
  have hs : s ≠ 0 := by rintro rfl; simp at hK0
  rw [← natCard_curveF_sq_mul h2 h3 hL hs, pow_two]

end ZInQ.Manuscript.RC.KSplit
