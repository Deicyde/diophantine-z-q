import ZInQKernel.Contrib.OneProof.SZThm33.ValuationSliceClass
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.WeilModelBridge

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules HDec.WeilPairing T09Pic ReductSplit SmoothGroup PkgI3 PkgI3.AbVar
open PicDict PicDict.Transport PicDict.DirectPairing ZInQ.ToricOrthogonality
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : AbVar K) (M : GroupModelO A O)

/-- The generic restriction of a torsion section over the valuation ring. -/
def valuationTorsionPoint {n : ℕ} (x : Over.mk (base hw) ⟶ (M.G)) (hx : x ^ n = 1) : tors A n :=
  ⟨Additive.ofMul (genPtHom hw A M (restrictPoint gen x)), AddSubgroup.torsionBy.nsmul_iff.mpr <| by
    apply Additive.toMul.injective
    change (genPtHom hw A M (restrictPoint gen x)) ^ n = 1
    rw [← map_pow, ← map_pow, hx, map_one, map_one]⟩

private theorem valuationGenericMap_unit :
    (pts (1 : A.Pt (AlgebraicClosure K))).left ≫ valuationGenericMap hw A M =
      gen ≫ η[(valuationModel hw A M)].left := by
  have h := valuationGenericMap_point hw A M (1 : Over.mk (base hw) ⟶ (M.G))
  rw [map_one, map_one, map_one, ← MonObj.one_eq_one] at h
  exact h

private theorem eval_constK_at_unit (u : AlgebraicClosure K) :
    ((pts (1 : A.Pt (AlgebraicClosure K))).left).appTop (constK A u) =
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv u := by
  let s := (pts (1 : A.Pt (AlgebraicClosure K))).left
  let f := (bcX A).hom
  have hsf : s ≫ f = 𝟙 (Spec (CommRingCat.of (AlgebraicClosure K))) :=
    Over.w (pts (1 : A.Pt (AlgebraicClosure K)))
  change s.appTop (f.appTop ((Scheme.ΓSpecIso _).inv u)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hsf, Scheme.Hom.id_appTop]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Evaluation of a relative Weil function at the identity over the generic
field is the actual finite-level Weil pairing of the lifted torsion points. -/
theorem valuationWeilEvaluation_at_generic
    {n : ℕ} (hn : 0 < n) (hchar : (n : K) ≠ 0)
    (x y : Over.mk (base hw) ⟶ (M.G)) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (L : (M.G).left.Modules) [SheafOfModules.IsInvertible L]
    (D : ((M.G) ⊗ (M.G)).left.Modules) [SheafOfModules.IsInvertible D]
    (hD : Scheme.Pic.mk D = productDeltaClass (M.G) (Scheme.Pic.mk L))
    (a : (valuationModel hw A M).left ⟶ ((M.G) ⊗ (M.G)).left)
    (hfst : a ≫ (fst (M.G) (M.G)).left = (Limits.pullback.fst M.G.hom (base hw)))
    (hsnd : a ≫ (snd (M.G) (M.G)).left = (valuationModel hw A M).hom ≫ (valuationSectionEquiv hw A M y).left ≫ (Limits.pullback.fst M.G.hom (base hw)))
    (h : (translateBy (valuationModel hw A M) (valuationSectionEquiv hw A M x)).left ≫
      (multiplyBy (valuationModel hw A M) n).left = (multiplyBy (valuationModel hw A M) n).left)
    (ψ : unit (valuationModel hw A M).left ≅ (pullback (multiplyBy (valuationModel hw A M) n).left).obj ((pullback a).obj D)) :
    letI : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
      unfold Relative.genericModelLine
      infer_instance
    ((gen (w := w)) ≫ η[(valuationModel hw A M)].left).appTop
        (wf (translateBy (valuationModel hw A M) (valuationSectionEquiv hw A M x)).left (multiplyBy (valuationModel hw A M) n).left
          h ((pullback a).obj D) ψ) =
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv
        (value A (Scheme.Pic.mk (Relative.genericModelLine M L)) hn hchar
          (valuationTorsionPoint hw A M x hx) (valuationTorsionPoint hw A M y hy)) := by
  let s := (pts (1 : A.Pt (AlgebraicClosure K))).left
  let g := valuationGenericMap hw A M
  let t := (translateBy (valuationModel hw A M) (valuationSectionEquiv hw A M x)).left
  let m := (multiplyBy (valuationModel hw A M) n).left
  let F := (pullback a).obj D
  let x' := valuationTorsionPoint hw A M x hx
  let y' := valuationTorsionPoint hw A M y hy
  have : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
    unfold Relative.genericModelLine
    infer_instance
  let Lη := Scheme.Pic.mk (Relative.genericModelLine M L)
  let ψ' := restrictTriv g (mlN A n) m (valuationGenericMap_multiply hw A M n).symm F ψ
  have hP : Scheme.Pic.mk ((pullback g).obj F) = torsionClass A Lη y' := valuationGenericSlice_pic hw A M y L D hD a hfst hsnd
  have hW := wf_restrict (trl (Additive.toMul (x' : P A))) (mlN A n) g t m
    (valuationGenericMap_translate hw A M x) (valuationGenericMap_multiply hw A M n).symm
    h (transl_left_comp_mulN_left x') F ψ
  have hC := wf_eq_const_value_of_pic_mk A Lη hn hchar x' y' ((pullback g).obj F) hP ψ'
  change (gen ≫ η[(valuationModel hw A M)].left).appTop (wf t m h F ψ) =
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv (value A Lη hn hchar x' y')
  rw [← valuationGenericMap_unit hw A M, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact (congrArg (fun u => s.appTop u) (hW.symm.trans hC)).trans (eval_constK_at_unit A _)

end SZRaynaud.Ambient
