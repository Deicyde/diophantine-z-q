import ZInQKernel.RouteK.Rank.Image
import ZInQKernel.RouteK.Rank.Counting
import ZInQKernel.RouteK.Rank.Torsion2

/-!
# RK9: positive rank and `#Sel₂ = 8` give `δ(C_d(ℚ)) = Sel₂(C_d)`

`docs/research/pc-audit.md` RK9. Let `d ≠ 0` and assume `C_d(ℚ)` is finitely generated
(Mordell–Weil; the hypothesis `hfg`). The complete 2-descent map `δ_d` (`deltaHom`) has kernel
`2C_d(ℚ)` (`delta_eq_one_iff`), so `C_d(ℚ)/2C_d(ℚ) ≅ δ_d(C_d(ℚ))`, and its image, written by
squarefree representatives (`selRep`), lies in `Sel2 d` (`selRep_mem_sel2`). Since
`#C_d(ℚ)[2] = 4` (`card_ker_two_nsmul_eq_four`), a point of infinite order gives
`#(C_d(ℚ)/2C_d(ℚ)) ≥ 8` (`eight_le_card_quotient_two`). So if `#Sel2 d = 8`, the image is all of
`Sel2 d`, and every Selmer class has a rational point on its covering (`loc_selRep`).
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent ZInQ.RouteK.Selmer

variable {d : ℕ}

/-- The kernel of `δ_d` over `ℚ` is `2 C_d(ℚ)`. -/
theorem deltaHom_ker_eq (hd : d ≠ 0) :
    (deltaHom rat_two_ne_zero (rat_d_ne_zero hd)).ker =
      (nsmulAddMonoidHom 2 : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point →+ _).range := by
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  rw [← delta_eq_one_iff hd P]
  constructor
  · intro h; exact congrArg Additive.toMul h
  · intro h; exact congrArg Additive.ofMul h

/-- The pair of squarefree representatives of a class in `Additive ((ℚ*/ℚ*²)²)`. -/
noncomputable def repPair (c : Additive (SqClass ℚ × SqClass ℚ)) : ℤ × ℤ :=
  (sqfRep (Additive.toMul c).1, sqfRep (Additive.toMul c).2)

theorem repPair_injective : Function.Injective repPair := fun c c' h => by
  simp only [repPair, Prod.mk.injEq] at h
  apply Additive.toMul.injective
  exact Prod.ext (sqfRep_injective h.1) (sqfRep_injective h.2)

/-- `#(C_d(ℚ)/2C_d(ℚ))` is the number of pairs `selRep P`. -/
theorem card_quotient_two_eq_ncard_range_selRep (hd : d ≠ 0) :
    Nat.card ((shortCurve (-(d : ℚ) ^ 2)).toAffine.Point ⧸
        (nsmulAddMonoidHom 2 : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point →+ _).range) =
      (Set.range (selRep (d := d))).ncard := by
  set δ := deltaHom rat_two_ne_zero (rat_d_ne_zero hd)
  rw [← deltaHom_ker_eq hd, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ).toEquiv]
  have hsel : Set.range (selRep (d := d)) = repPair '' Set.range δ := by
    rw [← Set.range_comp]; rfl
  rw [hsel, Set.ncard_image_of_injective _ repPair_injective, ← Nat.card_coe_set_eq,
    ← AddMonoidHom.coe_range, SetLike.coe_sort_coe]

/-- **RK9.** If `C_d(ℚ)` is finitely generated, has a point of infinite order, and `#Sel2 d = 8`,
then every Selmer class `(a, b) ∈ Sel2 d` has a rational point on its covering. -/
theorem loc_of_mem_sel2_of_infinite_order (hd : d ≠ 0)
    (hfg : AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point)
    (hinf : ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P)
    (h8 : (Sel2 d).ncard = 8) : ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2 := by
  set S := Set.range (selRep (d := d))
  have hS : S ⊆ Sel2 d := by rintro _ ⟨P, rfl⟩; exact selRep_mem_sel2 hd P
  have hfin : (Sel2 d).Finite := Set.finite_of_ncard_ne_zero (by rw [h8]; norm_num)
  have hSfin : S.Finite := hfin.subset hS
  have hSpos : S.ncard ≠ 0 := (Set.ncard_pos hSfin).mpr ⟨_, 0, rfl⟩ |>.ne'
  have hcard := card_quotient_two_eq_ncard_range_selRep hd
  have : Finite ((shortCurve (-(d : ℚ) ^ 2)).toAffine.Point ⧸
      (nsmulAddMonoidHom 2 : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point →+ _).range) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hSpos)
  have h8le := eight_le_card_quotient_two
    (card_ker_two_nsmul_eq_four rat_two_ne_zero (rat_d_ne_zero hd)) hinf
  rw [hcard] at h8le
  have hSeq : S = Sel2 d := Set.eq_of_subset_of_ncard_le hS (by rw [h8]; exact h8le) hfin
  intro ab hab
  rw [← hSeq] at hab
  obtain ⟨P, rfl⟩ := hab
  exact loc_selRep hd P

end ZInQ.RouteK.Rank
