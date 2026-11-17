import ZInQKernel.Contrib.OneProof.SelmerCorank

/-!
# The curves `E_ℓ`: full two-torsion, and Selmer classes as Kummer classes

For the manuscript's curves `E_ℓ : y² = x(x - ℓ)(x + 3ℓ)` (`ZInQ.Manuscript.curve`):

* `isElliptic_curve`, `fullTwoTorsion_curve`: for `ℓ ≠ 0`, `E_ℓ` is elliptic and `#E_ℓ(ℚ)[2] = 4`;
* `kummerSelmerMap_surjective_of_rank_one`: for an elliptic curve with full rational two-torsion,
  `#Sel₂ = 8` and `rank E(ℚ) = 1` (with Mordell–Weil), every class of `Sel₂(E/ℚ)` is the Kummer class
  of a rational point — the step of the manuscript's proof of Theorem 5.2 at lines 1107–1110 ("the
  Kummer class is then represented by actual rational points");
* `kummerSelmerMap_surjective_of_restrictedConverse`: the same for `E_ℓ` in the domain of
  Theorem 5.3, from Theorem 5.3 over the genuine Selmer condition (`RestrictedConverseGenuine`),
  Lemma 5.4 (`selmerCorankOne_of_card_selmerAt_one`) and the printed inputs Cassels–Tate and the rank
  half of Lemma 5.5 (Kolyvagin, with modularity), as stated hypotheses; Mordell–Weil is proved
  (`mordellWeilQ`, Tau Ceti), giving `kummerSelmerMap_surjective_of_restrictedConverse'`.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology ZInQ.Cofinite WeierstrassCurve.Affine

/-! ### `E_ℓ` is elliptic with full rational two-torsion -/

theorem isElliptic_curve {ℓ : ℚ} (hℓ : ℓ ≠ 0) : (ZInQ.Manuscript.curve ℓ).IsElliptic :=
  ⟨by rw [ZInQ.Manuscript.curve_Δ]; exact isUnit_iff_ne_zero.mpr (by positivity)⟩

section TwoTorsion

variable {ℓ : ℚ}

theorem curve_equation_iff (x y : ℚ) :
    (ZInQ.Manuscript.curve ℓ).toAffine.Equation x y ↔ y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ZInQ.Manuscript.curve, zero_mul, add_zero]
  constructor <;> intro h <;> linear_combination h

theorem curve_evalEval_polynomialY (x y : ℚ) :
    (ZInQ.Manuscript.curve ℓ).toAffine.polynomialY.evalEval x y = 2 * y := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  simp [ZInQ.Manuscript.curve]

variable (hℓ : ℓ ≠ 0)
include hℓ

theorem curve_nonsingular_of_root {x : ℚ} (hx : x * (x - ℓ) * (x + 3 * ℓ) = 0) :
    (ZInQ.Manuscript.curve ℓ).toAffine.Nonsingular x 0 := by
  have := isElliptic_curve hℓ
  exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((curve_equation_iff x 0).mpr (by
    rw [hx]; ring))

/-- The point `(x, 0)` for a root `x` of `x(x - ℓ)(x + 3ℓ)`, as an element of `E_ℓ(ℚ)[2]`. -/
def twoTorsionPt {x : ℚ} (hx : x * (x - ℓ) * (x + 3 * ℓ) = 0) :
    tors (ZInQ.Manuscript.curve ℓ).toAffine.Point 2 :=
  ⟨Point.some x 0 (curve_nonsingular_of_root hℓ hx), mem_tors.mpr (by
    rw [two_nsmul, Point.some_add_self_eq_zero_iff, curve_evalEval_polynomialY, mul_zero])⟩

theorem fullTwoTorsion_curve : FullTwoTorsion (ZInQ.Manuscript.curve ℓ) := by
  classical
  have h0 : (0 : ℚ) * (0 - ℓ) * (0 + 3 * ℓ) = 0 := by ring
  have h1 : ℓ * (ℓ - ℓ) * (ℓ + 3 * ℓ) = 0 := by ring
  have h2 : (-3 * ℓ) * (-3 * ℓ - ℓ) * (-3 * ℓ + 3 * ℓ) = 0 := by ring
  let f : Fin 4 → tors (ZInQ.Manuscript.curve ℓ).toAffine.Point 2 :=
    ![0, twoTorsionPt hℓ h0, twoTorsionPt hℓ h1, twoTorsionPt hℓ h2]
  have hne1 : (0 : ℚ) ≠ ℓ := fun h => hℓ h.symm
  have hne2 : (0 : ℚ) ≠ -3 * ℓ := fun h => hℓ (by linarith)
  have hne3 : ℓ ≠ -3 * ℓ := fun h => hℓ (by linarith)
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [f, twoTorsionPt, Subtype.ext_iff, Point.some.injEq]
    · intro S
      obtain ⟨S, hS⟩ := S
      have hS2 : S + S = 0 := by rw [← two_nsmul]; exact mem_tors.mp hS
      rcases S with _ | ⟨x, y, h⟩
      · exact ⟨0, rfl⟩
      · have hy : y = 0 := by
          have := (Point.some_add_self_eq_zero_iff h).mp hS2
          rw [curve_evalEval_polynomialY] at this
          linarith
        subst hy
        have hx : x * (x - ℓ) * (x + 3 * ℓ) = 0 := by
          have := (curve_equation_iff x 0).mp h.1
          linarith
        rcases mul_eq_zero.mp hx with hx' | hx'
        · rcases mul_eq_zero.mp hx' with hx'' | hx''
          · subst hx''
            exact ⟨1, rfl⟩
          · obtain rfl : x = ℓ := by linarith
            exact ⟨2, rfl⟩
        · obtain rfl : x = -3 * ℓ := by linarith
          exact ⟨3, rfl⟩
  rw [FullTwoTorsion, ← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end TwoTorsion

/-! ### Rank one: `Sel₂` is the Kummer image -/

/-- `rank_ℤ (ℤ^r × T) = r` for a finite `T`. -/
theorem rank_pi_int_prod (r : ℕ) (T : Type) [AddCommGroup T] [Finite T] :
    Module.rank ℤ ((Fin r → ℤ) × T) = r := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ (Fin r → ℤ) T)
  rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, rank_top, rank_fin_fun] at h
  have hker : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin r → ℤ) T)) = 0 := by
    rw [Module.rank_eq_zero_iff_isTorsion]
    intro x
    refine ⟨⟨(Nat.card T : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast Nat.card_pos.ne')⟩,
      ?_⟩
    have hx1 : (x : (Fin r → ℤ) × T).1 = 0 := LinearMap.mem_ker.mp x.2
    apply Subtype.ext
    change (Nat.card T : ℤ) • (x : (Fin r → ℤ) × T) = 0
    refine Prod.ext ?_ ?_
    · simp [hx1]
    · simp only [Prod.smul_snd, Prod.snd_zero, natCast_zsmul, card_nsmul_eq_zero']
  rw [hker, add_zero] at h
  exact h.symm

theorem rank_eq_of_addEquiv {A T : Type} [AddCommGroup A] [AddCommGroup T] [Finite T] {r : ℕ}
    (e : A ≃+ (Fin r → ℤ) × T) : Module.rank ℤ A = r := by
  rw [e.toIntLinearEquiv.rank_eq, rank_pi_int_prod]

/-- **Rank one makes every class of `Sel₂` a Kummer class** (the manuscript, lines 1107–1110): for
an elliptic curve `E/ℚ` with full rational two-torsion, `#Sel₂ = 8` and `rank E(ℚ) = 1`,
`#(E(ℚ)/2E(ℚ)) = 2 · 4 = 8 = #Sel₂`, so the injective Kummer map `E(ℚ)/2E(ℚ) → Sel₂` is onto. -/
theorem kummerSelmerMap_surjective_of_rank_one (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hMW : MordellWeilQ E) (h2 : FullTwoTorsion E) (hSel : Nat.card (selmerAt E 1) = 8)
    (hrank : Module.rank ℤ E.toAffine.Point = 1) :
    Function.Surjective (E.kummerSelmerMap emb (isUnit_two_pow 1)) := by
  classical
  have : AddGroup.FG E.toAffine.Point := hMW
  obtain ⟨r, T, _, hT, ⟨eMW⟩⟩ := exists_addEquiv_pi_int_prod_finite E.toAffine.Point
  have hr : r = 1 := by
    have := rank_eq_of_addEquiv eMW
    rw [hrank] at this
    exact_mod_cast this.symm
  have hT2 : Nat.card (tors T 2) = 4 := by
    rw [← h2, card_tors_congr eMW, card_tors_prod, card_tors_int_pi r 2 two_ne_zero, one_mul]
  have hQ : Nat.card (E.toAffine.Point ⧸
      (nsmulAddMonoidHom (α := E.toAffine.Point) (2 ^ 1)).range) = 8 := by
    rw [card_quotient_nsmul_range_of_addEquiv eMW (by norm_num), hr, pow_one, pow_one, hT2]
  have hS1 : Finite (E.selmerGroup emb (2 ^ 1)) :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card (selmerAt E 1) ≠ 0
      rw [hSel]; norm_num)
  refine ((E.kummerSelmerMap_injective emb (isUnit_two_pow 1)).bijective_of_nat_card_le ?_).2
  change Nat.card (selmerAt E 1) ≤ _
  rw [hSel, hQ]

/-- **The rank half of Lemma 5.5** (`lem:forward-rank`, lines 1086–1105): for an elliptic curve `E/ℚ`
with `ord_{s=1} L(E, s) = 1`, `rank E(ℚ) = 1` (modularity, Breuil–Conrad–Diamond–Taylor Theorem A, and
Kolyvagin's Theorem 1, as the manuscript cites them). A printed input. -/
def KolyvaginRankOne (E : WeierstrassCurve ℚ) : Prop :=
  ZInQ.Manuscript.AnalyticRankOne E → Module.rank ℤ E.toAffine.Point = 1

/-- **The manuscript's use of Theorem 5.3, lines 1107–1110, over the genuine Selmer groups**: for a
positive squarefree `ℓ ≡ 11 (mod 12)` with `#Sel₂(E_ℓ/ℚ) = 8`, Theorem 5.3
(`RestrictedConverseGenuine`), Lemma 5.4 (proved, `selmerCorankOne_of_card_selmerAt_one`) and the
printed inputs Mordell–Weil, Cassels–Tate and the rank half of Lemma 5.5 make every class of
`Sel₂(E_ℓ/ℚ)` the Kummer class of a rational point. -/
theorem kummerSelmerMap_surjective_of_restrictedConverse {ℓ : ℕ}
    [(ZInQ.Manuscript.curve (ℓ : ℚ)).IsElliptic] (hℓ : 0 < ℓ) (hsf : Squarefree ℓ)
    (hmod : ℓ % 12 = 11) (hRC : RestrictedConverseGenuine)
    (hK : KolyvaginRankOne (ZInQ.Manuscript.curve ℓ)) (hMW : MordellWeilQ (ZInQ.Manuscript.curve ℓ))
    (hCT : CasselsTateSquare (ZInQ.Manuscript.curve ℓ))
    (hSel : Nat.card (selmerAt (ZInQ.Manuscript.curve ℓ) 1) = 8) :
    Function.Surjective ((ZInQ.Manuscript.curve (ℓ : ℚ)).kummerSelmerMap emb (isUnit_two_pow 1)) := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have h2 := fullTwoTorsion_curve hℓ0
  have hcor := selmerCorankOne_of_card_selmerAt_one _ hMW hCT h2 hSel
  have han := hRC ℓ hℓ hsf hmod hcor
  exact kummerSelmerMap_surjective_of_rank_one _ hMW h2 hSel (hK han)

/-- **The manuscript's lines 1107–1110 with Mordell–Weil proved**: as
`kummerSelmerMap_surjective_of_restrictedConverse`, with `MordellWeilQ` discharged by
`mordellWeilQ`. -/
theorem kummerSelmerMap_surjective_of_restrictedConverse' {ℓ : ℕ}
    [(ZInQ.Manuscript.curve (ℓ : ℚ)).IsElliptic] (hℓ : 0 < ℓ) (hsf : Squarefree ℓ)
    (hmod : ℓ % 12 = 11) (hRC : RestrictedConverseGenuine)
    (hK : KolyvaginRankOne (ZInQ.Manuscript.curve ℓ))
    (hCT : CasselsTateSquare (ZInQ.Manuscript.curve ℓ))
    (hSel : Nat.card (selmerAt (ZInQ.Manuscript.curve ℓ) 1) = 8) :
    Function.Surjective ((ZInQ.Manuscript.curve (ℓ : ℚ)).kummerSelmerMap emb (isUnit_two_pow 1)) :=
  kummerSelmerMap_surjective_of_restrictedConverse hℓ hsf hmod hRC hK (mordellWeilQ _) hCT hSel

end ZInQ.Manuscript.SelmerTwoPower
