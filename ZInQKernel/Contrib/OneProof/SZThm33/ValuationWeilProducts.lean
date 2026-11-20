import ZInQKernel.Contrib.OneProof.SZThm33.ValuationWeilEvaluation

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar ReductSplit SmoothGroup HDec.WeilPairing PicDict.DirectPairing
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : AbVar K) (M : GroupModelO A O)

attribute [local instance] ZInQ.FaltingsRestate.isCommMonObj_groupModelO

/-- Products of valuation torsion points restrict to sums in the additive
generic torsion group. -/
theorem valuationTorsionPoint_of_prod {I : Type} [Fintype I] {n : ℕ}
    (x : (Over.mk (base hw) ⟶ M.G)) (hx : x ^ n = 1) (z : I → (Over.mk (base hw) ⟶ M.G)) (hz : ∀ i, z i ^ n = 1)
    (h : x = ∏ i, z i) :
    valuationTorsionPoint hw A M x hx = ∑ i, valuationTorsionPoint hw A M (z i) (hz i) := by
  let f := ((genPtHom hw A M).comp (restrictPoint gen)).toAdditive
  apply Subtype.ext
  change ((valuationTorsionPoint hw A M x hx : tors A n) : P A) =
    (tors A n).subtype (∑ i, valuationTorsionPoint hw A M (z i) (hz i))
  rw [map_sum]
  change f (Additive.ofMul x) = ∑ i, f (Additive.ofMul (z i))
  rw [← map_sum, ← ofMul_prod, h]

/-- A product in the translating coordinate pairs trivially when each
factor pairs trivially. -/
theorem valuationWeilValue_eq_one_of_prod {I : Type} [Fintype I] {n : ℕ}
    (hn : 0 < n) (hchar : (n : K) ≠ 0) (L : A.X.left.Pic)
    (x y : (Over.mk (base hw) ⟶ M.G)) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (z : I → (Over.mk (base hw) ⟶ M.G)) (hz : ∀ i, z i ^ n = 1) (h : x = ∏ i, z i)
    (hval : ∀ i, value A L hn hchar (valuationTorsionPoint hw A M (z i) (hz i))
      (valuationTorsionPoint hw A M y hy) = 1) :
    value A L hn hchar (valuationTorsionPoint hw A M x hx)
      (valuationTorsionPoint hw A M y hy) = 1 := by
  let f := finitePairing A L hn hchar
  let y' := valuationTorsionPoint hw A M y hy
  have hz0 (i : I) : f (valuationTorsionPoint hw A M (z i) (hz i)) y' = 0 := by
    apply Mu.val_injective
    exact hval i
  have h0 : f (valuationTorsionPoint hw A M x hx) y' = 0 := by
    rw [valuationTorsionPoint_of_prod hw A M x hx z hz h, map_sum, AddMonoidHom.finsetSum_apply]
    simp only [hz0, Finset.sum_const_zero]
  exact congrArg Mu.val h0

end SZRaynaud.Ambient

namespace PicDict.DirectPairing

variable {K : Type} [Field K] (A : AbVar K) (L : A.X.left.Pic) {n : ℕ}

/-- Vanishing of the finite Weil value is symmetric by alternation. -/
theorem value_eq_one_of_swap (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y : tors A n)
    (h : value A L hn hchar y x = 1) : value A L hn hchar x y = 1 := by
  let f := finitePairing A L hn hchar
  have h0 : f y x = 0 := Mu.val_injective h
  have hdiag := finitePairing_self A L hn hchar (x + y)
  change f (x + y) (x + y) = 0 at hdiag
  have hs : f x y = 0 := by
    simpa only [map_add, AddMonoidHom.add_apply, h0,
      show f x x = 0 from finitePairing_self A L hn hchar x,
      show f y y = 0 from finitePairing_self A L hn hchar y, zero_add, add_zero] using hdiag
  exact congrArg Mu.val hs

end PicDict.DirectPairing
