import ZInQKernel.Contrib.PoleRC.SelMTauCetiLocal
import ZInQKernel.Contrib.OneProof.SelmerTwoPower
import ZInQKernel.RouteK.Rank.Image
import ZInQKernel.RouteK.Slots.Basic

/-!
# The explicit `2`-Selmer system `SelM ℓ` is the genuine `Sel₂(E_ℓ/ℚ)`

Lane R7 of fork issue #83. `SelM ℓ` (`Defs.lean`) is the set of pairs `(a, b)` of squarefree
integers that satisfy the x-form local condition `LocM` over `ℝ` and every `ℚ_p`;
`selmerAt (curve ℓ) 1` (`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean`) is the genuine
`Sel₂(E_ℓ/ℚ)`: Tau Ceti's kernel of `H¹(G_ℚ, E_ℓ[2]) → ∏_v H¹(G_{ℚ_v}, E_ℓ(ℚ_vˢ))` over every place.

* `selMEquiv`: **`SelM ℓ ≃ Sel₂(E_ℓ/ℚ)`** for every positive integer `ℓ` (Silverman X.1.4):
  `(a, b) ↦` the class whose characters at `T_A = (−3ℓ, 0)` and `T_B = (ℓ, 0)` (the manuscript's
  Kummer coordinates `x + 3ℓ`, `x − ℓ`, `diophantine_zq.tex` line 1058) are the Kummer classes of
  `a` and `b`.
* `card_selmerAt_curve`: `Nat.card Sel₂(E_ℓ/ℚ) = (SelM ℓ).ncard`.

The proof assembles `SelMTauCetiLocal.lean`: `H¹(G_ℚ, E_ℓ[2]) ≅ H¹(G_ℚ, μ₂)²` (`eq_of_chi`,
`sec`), Kummer theory `ℚ*/ℚ*² ≅ H¹(G_ℚ, μ₂)` (Tau Ceti's `kummerMap`, `kummerMap_surjective`,
`kummerMap_eq_iff`), the Selmer condition as local Kummer images
(`WeierstrassCurve.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap`) and the local
condition in the x-form (`torsionRes_mem_range_kummerMap_iff`); squarefree representatives come
from `ZInQ.RouteK.Rank.exists_squarefree_sqc` and are unique by
`ZInQ.RouteK.int_squarefree_eq_of_mul_sq`.
-/

noncomputable section

namespace ZInQ.Manuscript.PoleRC.SelMTauCeti

open TauCeti TauCeti.ContCohomology WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower

theorem curve_isCurveE (ℓ : ℚ) : IsCurveE (curve ℓ) ℓ := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem rat_two_ne_zero : (2 : ℚ) ≠ 0 := two_ne_zero

theorem rat_three_ne_zero : (3 : ℚ) ≠ 0 := by norm_num

/-- The Kummer class `κ(u) ∈ H¹(G_ℚ, μ₂)` of a unit `u ∈ ℚ*`. -/
abbrev kum (u : ℚˣ) : H1 (AbsoluteGaloisGroup ℚ) (KummerCoeff ℚ 2) :=
  (TauCeti.kummerMap ℚ 2 (isUnit_two_nat rat_two_ne_zero) u).toAdd

/-- Two squarefree integers whose quotient is a rational square are equal. -/
theorem squarefree_eq_of_isSquare_div {x x' : ℤ} (hx : Squarefree x) (hx' : Squarefree x')
    (h : IsSquare ((x : ℚ) / x')) : x = x' := by
  obtain ⟨r, hr⟩ := h
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne_zero
  have hx'0 : (x' : ℚ) ≠ 0 := by exact_mod_cast hx'.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    rcases hr with h1 | h1
    · exact hx0 h1
    · exact hx'0 h1
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr0
  have hden : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  refine ZInQ.RouteK.int_squarefree_eq_of_mul_sq hx hx' hden hnum ?_
  have hden' : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have key : (x : ℚ) * (r.den : ℚ) ^ 2 = x' * (r.num : ℚ) ^ 2 := by
    have hr' : (x : ℚ) = x' * (r * r) := by
      rw [div_eq_iff hx'0] at hr; rw [hr]; ring
    rw [hr', ← Rat.mul_den_eq_num r]
    ring
  exact_mod_cast key

/-- Every unit of `ℚ` has the Kummer class of a squarefree integer. -/
theorem exists_squarefree_kum (u : ℚˣ) :
    ∃ x : ℤ, ∃ hx : Squarefree x,
      kum (Units.mk0 (x : ℚ) (by exact_mod_cast hx.ne_zero)) = kum u := by
  obtain ⟨x, hx, hxu⟩ := ZInQ.RouteK.Rank.exists_squarefree_sqc u.ne_zero
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne_zero
  refine ⟨x, hx, ?_⟩
  obtain ⟨w, hw, hxw⟩ := (ZInQ.Descent.sqc_eq_sqc_iff hx0 u.ne_zero).mp hxu
  have hsq : IsSquare (((Units.mk0 (x : ℚ) hx0 : ℚˣ) : ℚ) / (u : ℚ)) :=
    ⟨w, by rw [Units.val_mk0, hxw]; field_simp⟩
  exact congrArg Multiplicative.toAdd ((kummerMap_eq_iff _ _ _).mpr hsq)

section Global

variable {ℓ : ℚ} (hℓ : ℓ ≠ 0) [(curve ℓ).IsElliptic]

/-- **The Selmer condition for a class with characters `κ(a), κ(b)`**: `c ∈ Sel₂(E_ℓ/ℚ)` iff the
x-form local condition `LocM` holds for `(a, b)` at every prime and at the real place. -/
theorem mem_sel_iff (c : H1 (AbsoluteGaloisGroup ℚ) ((curve ℓ).TorsionCoeff 2)) (a b : ℚˣ)
    (ha : explicitCoeff1 _ _ (chiA (curve_isCurveE ℓ) rat_two_ne_zero rat_three_ne_zero hℓ)
      continuous_of_discreteTopology c = kum a)
    (hb : explicitCoeff1 _ _ (chiB (curve_isCurveE ℓ) rat_two_ne_zero rat_three_ne_zero hℓ)
      continuous_of_discreteTopology c = kum b) :
    c ∈ (curve ℓ).selmerGroup embFin 2 ⊓ (curve ℓ).selmerGroup embInf 2 ↔
      (∀ p : Nat.Primes, LocM ℚ_[(p : ℕ)] (algebraMap ℚ ℚ_[(p : ℕ)] ℓ)
          (algebraMap ℚ ℚ_[(p : ℕ)] a) (algebraMap ℚ ℚ_[(p : ℕ)] b)) ∧
        LocM ℝ (algebraMap ℚ ℝ ℓ) (algebraMap ℚ ℝ a) (algebraMap ℚ ℝ b) := by
  classical
  rw [AddSubgroup.mem_inf,
    mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap _ _ (isUnit_two_nat rat_two_ne_zero),
    mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap _ _ (isUnit_two_nat rat_two_ne_zero)]
  refine and_congr (forall_congr' fun p => ?_) ?_
  · exact torsionRes_mem_range_kummerMap_iff (curve_isCurveE ℓ) rat_two_ne_zero
      rat_three_ne_zero hℓ (embFin p) a b c ha hb
  · constructor
    · intro h
      exact (torsionRes_mem_range_kummerMap_iff (curve_isCurveE ℓ) rat_two_ne_zero
        rat_three_ne_zero hℓ (embInf ()) a b c ha hb).mp (h ())
    · intro h u
      exact (torsionRes_mem_range_kummerMap_iff (curve_isCurveE ℓ) rat_two_ne_zero
        rat_three_ne_zero hℓ (embInf u) a b c ha hb).mpr h

end Global

section Equiv

/-- The unit of `ℚ` given by a nonzero integer. -/
abbrev unitOf {x : ℤ} (hx : x ≠ 0) : ℚˣ := Units.mk0 (x : ℚ) (by exact_mod_cast hx)

variable (ℓ : ℕ)

/-- The x-form local conditions of `SelM` in terms of `Nat.Primes`, from the image of a unit. -/
theorem selM_conditions_iff {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ((∀ p : Nat.Primes, LocM ℚ_[(p : ℕ)] (algebraMap ℚ ℚ_[(p : ℕ)] (ℓ : ℚ))
          (algebraMap ℚ ℚ_[(p : ℕ)] (unitOf hx : ℚ)) (algebraMap ℚ ℚ_[(p : ℕ)] (unitOf hy : ℚ))) ∧
        LocM ℝ (algebraMap ℚ ℝ (ℓ : ℚ)) (algebraMap ℚ ℝ (unitOf hx : ℚ))
          (algebraMap ℚ ℝ (unitOf hy : ℚ))) ↔
      LocM ℝ (ℓ : ℝ) (x : ℝ) (y : ℝ) ∧ ∀ (p : ℕ) [Fact p.Prime], LocM ℚ_[p] (ℓ : ℚ_[p]) x y := by
  simp only [Units.val_mk0, map_intCast, map_natCast]
  constructor
  · rintro ⟨hp, hr⟩
    exact ⟨hr, fun p hp' => hp ⟨p, hp'.out⟩⟩
  · rintro ⟨hr, hp⟩
    exact ⟨fun p => hp (p : ℕ), hr⟩

variable (hℓ : (ℓ : ℚ) ≠ 0) [(curve (ℓ : ℚ)).IsElliptic] [Invertible (2 : ℚ)]

/-- The class attached to a pair of `SelM ℓ`: its characters at `T_A`, `T_B` are `κ(a)`, `κ(b)`. -/
def selMClass (ab : SelM ℓ) : H1 (AbsoluteGaloisGroup ℚ) ((curve (ℓ : ℚ)).TorsionCoeff 2) :=
  sec (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero rat_three_ne_zero hℓ
    (kum (unitOf ab.2.1.ne_zero)) (kum (unitOf ab.2.2.1.ne_zero))

theorem chiA_selMClass (ab : SelM ℓ) :
    explicitCoeff1 _ _ (chiA (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero rat_three_ne_zero hℓ)
      continuous_of_discreteTopology (selMClass ℓ hℓ ab) = kum (unitOf ab.2.1.ne_zero) :=
  chiA_sec _ _ _ _ _ _

theorem chiB_selMClass (ab : SelM ℓ) :
    explicitCoeff1 _ _ (chiB (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero rat_three_ne_zero hℓ)
      continuous_of_discreteTopology (selMClass ℓ hℓ ab) = kum (unitOf ab.2.2.1.ne_zero) :=
  chiB_sec _ _ _ _ _ _

theorem selMClass_mem (ab : SelM ℓ) :
    selMClass ℓ hℓ ab ∈
      (curve (ℓ : ℚ)).selmerGroup embFin 2 ⊓ (curve (ℓ : ℚ)).selmerGroup embInf 2 := by
  rw [mem_sel_iff hℓ _ _ _ (chiA_selMClass ℓ hℓ ab) (chiB_selMClass ℓ hℓ ab),
    selM_conditions_iff]
  exact ⟨ab.2.2.2.1, fun p _ => ab.2.2.2.2 p⟩

/-- The map `SelM ℓ → Sel₂(E_ℓ/ℚ)`. -/
def toSel (ab : SelM ℓ) : selmerAt (curve (ℓ : ℚ)) 1 :=
  ⟨selMClass ℓ hℓ ab, selMClass_mem ℓ hℓ ab⟩

theorem toSel_injective : Function.Injective (toSel ℓ hℓ) := by
  rintro ⟨⟨x, y⟩, hxy⟩ ⟨⟨x', y'⟩, hxy'⟩ h
  have h' : selMClass ℓ hℓ ⟨(x, y), hxy⟩ = selMClass ℓ hℓ ⟨(x', y'), hxy'⟩ := congrArg Subtype.val h
  have hA := congrArg (explicitCoeff1 _ _ (chiA (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero
    rat_three_ne_zero hℓ) continuous_of_discreteTopology) h'
  have hB := congrArg (explicitCoeff1 _ _ (chiB (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero
    rat_three_ne_zero hℓ) continuous_of_discreteTopology) h'
  rw [chiA_selMClass, chiA_selMClass] at hA
  rw [chiB_selMClass, chiB_selMClass] at hB
  have sA := (kummerMap_eq_iff _ _ _).mp (Multiplicative.toAdd.injective hA)
  have sB := (kummerMap_eq_iff _ _ _).mp (Multiplicative.toAdd.injective hB)
  simp only [Units.val_mk0] at sA sB
  have ex : x = x' := squarefree_eq_of_isSquare_div hxy.1 hxy'.1 sA
  have ey : y = y' := squarefree_eq_of_isSquare_div hxy.2.1 hxy'.2.1 sB
  subst ex ey
  rfl

theorem toSel_surjective : Function.Surjective (toSel ℓ hℓ) := by
  rintro ⟨c, hc⟩
  set χA := chiA (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero rat_three_ne_zero hℓ
  set χB := chiB (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero rat_three_ne_zero hℓ
  set c' : H1 (AbsoluteGaloisGroup ℚ) ((curve (ℓ : ℚ)).TorsionCoeff 2) := c
  have hc' : c' ∈ (curve (ℓ : ℚ)).selmerGroup embFin 2 ⊓ (curve (ℓ : ℚ)).selmerGroup embInf 2 := hc
  obtain ⟨u, hu⟩ := TauCeti.kummerMap_surjective (isUnit_two_nat rat_two_ne_zero)
    (Multiplicative.ofAdd (explicitCoeff1 _ _ χA continuous_of_discreteTopology c'))
  obtain ⟨v, hv⟩ := TauCeti.kummerMap_surjective (isUnit_two_nat rat_two_ne_zero)
    (Multiplicative.ofAdd (explicitCoeff1 _ _ χB continuous_of_discreteTopology c'))
  obtain ⟨x, hx, hxu⟩ := exists_squarefree_kum u
  obtain ⟨y, hy, hyv⟩ := exists_squarefree_kum v
  have hA : explicitCoeff1 _ _ χA continuous_of_discreteTopology c' = kum (unitOf hx.ne_zero) := by
    rw [hxu, kum, hu, toAdd_ofAdd]
  have hB : explicitCoeff1 _ _ χB continuous_of_discreteTopology c' = kum (unitOf hy.ne_zero) := by
    rw [hyv, kum, hv, toAdd_ofAdd]
  have hmem := (mem_sel_iff hℓ c' _ _ hA hB).mp hc'
  rw [selM_conditions_iff] at hmem
  have hab : ((x, y) : ℤ × ℤ) ∈ SelM ℓ := ⟨hx, hy, hmem.1, fun p _ => hmem.2 p⟩
  refine ⟨⟨(x, y), hab⟩, Subtype.ext ?_⟩
  change selMClass ℓ hℓ ⟨(x, y), hab⟩ = c'
  exact eq_of_chi (curve_isCurveE (ℓ : ℚ)) rat_two_ne_zero rat_three_ne_zero hℓ
    ((chiA_selMClass ℓ hℓ _).trans hA.symm) ((chiB_selMClass ℓ hℓ _).trans hB.symm)

end Equiv

/-- **`SelM ℓ ≃ Sel₂(E_ℓ/ℚ)`** for every positive integer `ℓ` (Silverman, AEC, Proposition X.1.4,
in the manuscript's Kummer coordinates `(x + 3ℓ, x − ℓ)`). -/
def selMEquiv (ℓ : ℕ) (hℓ : ℓ ≠ 0) : SelM ℓ ≃ selmerAt (curve (ℓ : ℚ)) 1 :=
  haveI : (curve (ℓ : ℚ)).IsElliptic :=
    (curve_isCurveE (ℓ : ℚ)).isElliptic rat_two_ne_zero rat_three_ne_zero (by exact_mod_cast hℓ)
  letI : Invertible (2 : ℚ) := invertibleOfNonzero rat_two_ne_zero
  Equiv.ofBijective (toSel ℓ (by exact_mod_cast hℓ))
    ⟨toSel_injective ℓ _, toSel_surjective ℓ _⟩

/-- **`#Sel₂(E_ℓ/ℚ) = #SelM ℓ`** for every positive integer `ℓ`. -/
theorem card_selmerAt_curve (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    Nat.card (selmerAt (curve (ℓ : ℚ)) 1) = (SelM ℓ).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (selMEquiv ℓ hℓ)).symm

end ZInQ.Manuscript.PoleRC.SelMTauCeti
