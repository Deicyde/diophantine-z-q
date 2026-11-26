import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RouteBReduction
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RegularityCriterion
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Valuation

/-! Adapters from the closed-point, valuation and regularity results to the statements
K10, K11 (at arc points) and K12 used by the inverse map `Ψ`.

* K10: closed points are arc points or algebraic cusps, and the algebraic cusp of the
  orbit of `σ(∞)` is the analytic limit of `P(στ)` as `Im τ → ∞`.
* K12: the local sections representing `(A / B) · dj` near the closed points agree on
  overlaps (they agree on a nonempty open carrying representatives, and the curve is
  integral), so they glue to a global differential, which represents `(A / B) · dj` on
  every open. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane Topology Opposite
open scoped Manifold MatrixGroups

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

variable (N : ℕ) [NeZero N]

/-! ### K10 -/

/-- **K10**, proved. -/
theorem k10_holds : K10 N := by
  intro x hx
  rcases closedPoint_eq_arcPoint_or_cusp N x hx with h | ⟨c, hc⟩
  · exact Or.inl h
  · right
    obtain ⟨σ, rfl⟩ := orbitOfSL_surjective N c
    exact ⟨σ, cuspPoint N (orbitOfSL N σ), hc, algebraicCusp_limit N σ⟩

/-! ### K12 -/

/-- Sections of a sheaf of modules over an empty open agree. -/
theorem relativeDifferentials_eq_of_empty {W : (curveC N).left.Opens}
    (hW : ¬ (W : Set (curveC N).left).Nonempty)
    (u v : Γ((curveC N).hom.relativeDifferentials, W)) : u = v := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(curveC N).hom.relativeDifferentials.presheaf,
      (curveC N).hom.relativeDifferentials.isSheaf⟩ (fun i : Empty => (⊥ : (curveC N).left.Opens))
    W (fun i => i.elim) (fun x hx => (hW ⟨x, hx⟩).elim) u v (fun i => i.elim)

/-- If `θ` represents `(A / B) · dj` on `W`, then on every nonempty open `V ≤ W` carrying
representatives `s`, `b`, `c` with `b` a unit, `b · θ = s · dc` there (the definition), and
restrictions of representatives are representatives. -/
theorem representsDiffOn_res {W V : (curveC N).left.Opens} (hVW : V ≤ W)
    {θ : Γ((curveC N).hom.relativeDifferentials, W)} {A B : FieldC N}
    (hθ : RepresentsDiffOn N W θ A B) : RepresentsDiffOn N V (resD hVW θ) A B := by
  intro W' hW' s b c hs hb hc hbu
  have := hθ W' (hW'.trans hVW) s b c hs hb hc hbu
  change b • resD hW' (resD hVW θ) = _
  rw [resD_resD]
  exact this

/-- **K12**, proved. -/
theorem k12_holds : K12 N := by
  intro A B hreg
  have := curveC_isIntegral N
  have : LocallyOfFiniteType (curveC N).hom := by
    have := SmoothOfRelativeDimension.smooth 1 (curveC N).hom
    infer_instance
  let _ : JacobsonSpace (curveC N).left := LocallyOfFiniteType.jacobsonSpace (curveC N).hom
  by_cases hG : ∃ (G : (curveC N).left.Opens) (_ : (G : Set (curveC N).left).Nonempty)
      (s b c : Γ((curveC N).left, G)), RepOn N G A s ∧ RepOn N G B b ∧ RepOn N G (jC N) c ∧
        IsUnit b
  · obtain ⟨G, hGne, sG, bG, cG, hsG, hbG, hcG, hbu⟩ := hG
    -- on every nonempty open `V ≤ G`, two representing sections agree
    have hagree : ∀ (V : (curveC N).left.Opens) (hVG : V ≤ G),
        ∀ (W₁ W₂ : (curveC N).left.Opens) (h₁ : V ≤ W₁) (h₂ : V ≤ W₂)
          (θ₁ : Γ((curveC N).hom.relativeDifferentials, W₁))
          (θ₂ : Γ((curveC N).hom.relativeDifferentials, W₂)),
          RepresentsDiffOn N W₁ θ₁ A B → RepresentsDiffOn N W₂ θ₂ A B →
            resD h₁ θ₁ = resD h₂ θ₂ := by
      intro V hVG W₁ W₂ h₁ h₂ θ₁ θ₂ hθ₁ hθ₂
      have hu : IsUnit (resO hVG bG) := hbu.map _
      have e₁ := hθ₁ V h₁ (resO hVG sG) (resO hVG bG) (resO hVG cG)
        (hsG.res N hVG) (hbG.res N hVG) (hcG.res N hVG) hu
      have e₂ := hθ₂ V h₂ (resO hVG sG) (resO hVG bG) (resO hVG cG)
        (hsG.res N hVG) (hbG.res N hVG) (hcG.res N hVG) hu
      exact (hu.smul_left_cancel).mp (e₁.trans e₂.symm)
    let ι := closedPoints (curveC N).left
    choose U hxU θ hθ using fun x : ι => hreg x.1 x.2
    have hcov : (⊤ : (curveC N).left.Opens) ≤ iSup U := by
      intro y _
      obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty y).closure
        isClosed_closure.isLocallyClosed
      obtain ⟨_, hyU, rfl⟩ := mem_closure_iff.mp hx (U ⟨x, hxc⟩) (U ⟨x, hxc⟩).isOpen
        (hxU ⟨x, hxc⟩)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxc⟩, hyU⟩
    have hcompat : TopCat.Presheaf.IsCompatible (curveC N).hom.relativeDifferentials.presheaf
        U θ := by
      intro i j
      have hne : ((U i ⊓ U j ⊓ G : (curveC N).left.Opens) : Set (curveC N).left).Nonempty :=
        inter_nonempty (inter_nonempty ⟨_, hxU i⟩ ⟨_, hxU j⟩) hGne
      have hle : U i ⊓ U j ⊓ G ≤ U i ⊓ U j := inf_le_left
      apply eq_of_resD_eq hle hne
      change resD hle (resD inf_le_left (θ i)) = resD hle (resD inf_le_right (θ j))
      rw [resD_resD, resD_resD]
      exact hagree _ inf_le_right _ _ _ _ _ _ (hθ i) (hθ j)
    obtain ⟨S, hS, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨(curveC N).hom.relativeDifferentials.presheaf,
      (curveC N).hom.relativeDifferentials.isSheaf⟩ U ⊤ (fun i => homOfLE le_top) hcov θ hcompat
    refine ⟨S, fun W' hW' s b c hs hb hc hbu' => ?_⟩
    by_cases hne : (W' : Set (curveC N).left).Nonempty
    · obtain ⟨x, -, hxc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := (curveC N).left))
        isOpen_univ.isLocallyClosed
      let i : ι := ⟨x, hxc⟩
      have hVne : ((W' ⊓ U i : (curveC N).left.Opens) : Set (curveC N).left).Nonempty :=
        inter_nonempty hne ⟨_, hxU i⟩
      have h₁ : W' ⊓ U i ≤ W' := inf_le_left
      have h₂ : W' ⊓ U i ≤ U i := inf_le_right
      apply eq_of_resD_eq h₁ hVne
      have hSi : resD h₂ (θ i) = resD (h₁.trans hW') S := by
        rw [← hS i]
        change resD h₂ (resD le_top S) = _
        rw [resD_resD]
      have key := hθ i (W' ⊓ U i) h₂ (resO h₁ s) (resO h₁ b) (resO h₁ c) (hs.res N h₁)
        (hb.res N h₁) (hc.res N h₁) (hbu'.map _)
      change resD h₁ (b • resD hW' S) = resD h₁ (s • (curveC N).hom.sectionsD W' c)
      have hd : resD h₁ ((curveC N).hom.sectionsD W' c) =
          (curveC N).hom.sectionsD (W' ⊓ U i) (resO h₁ c) :=
        ((curveC N).hom.sectionsD_map h₁ c).symm
      rw [resD_smul, resD_smul, resD_resD, hd, ← hSi]
      exact key
    · exact relativeDifferentials_eq_of_empty N hne _ _
  · refine ⟨0, fun W' hW' s b c hs hb hc hbu => ?_⟩
    by_cases hne : (W' : Set (curveC N).left).Nonempty
    · exact (hG ⟨W', hne, s, b, c, hs, hb, hc, hbu⟩).elim
    · exact relativeDifferentials_eq_of_empty N hne _ _

end ZInQ.Manuscript.RC.CuspFormDifferentials
