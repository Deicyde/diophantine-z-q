import ZInQKernel.Contrib.SpreadOut.Spread

/-!
# group-law, II.a: spread-out's `exists_grp_stage`, keeping track of a property of the stages

The proof is spread-out's (`ZInQKernel/Contrib/SpreadOut/Spread.lean`, `exists_grp_stage`) verbatim; only the
property `Q`, stable under `Stage.next`, is carried along. Mathlib only.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLaw

open ZInQ.Contrib.SpreadOut

/-! ## §1 `exists_grp_stage` keeping track of an invariant of the stages -/

section StageQ

variable {I : Type} [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- spread-out's `exists_grp_stage` (verbatim proof), with a property of stages stable under `Stage.next`
carried along. -/
theorem exists_grp_stage_Q {N : Over c.pt} [GrpObj N] (Q : Stage D c N → Prop)
    (hQ : ∀ (s : Stage D c N) {k' : I} (b : k' ⟶ s.k), Q s → Q (s.next b))
    (s : Stage D c N) (hs : Q s) :
    ∃ (t : Stage D c N), Q t ∧ ∃ (_ : GrpObj t.M),
      letI : GrpObj ((Over.pullback (c.π.app t.k)).obj t.M) := Functor.grpObjObj
      IsMonHom t.e.hom := by
  obtain ⟨k₁, b₁, m₁, hm₁⟩ := exists_mul hc s
  obtain ⟨k₂, b₂, u₂, hu₂⟩ := exists_one hc (s.next b₁)
  have hm₂ := compatM_transport (Over.pullback (D.map b₂)) (Over.pullback (c.π.app k₂))
    (Over.pullback (c.π.app (s.next b₁).k)) (stθ D c b₂) (s.next b₁).e hm₁
  obtain ⟨k₃, b₃, i₃, hi₃⟩ := exists_inv hc ((s.next b₁).next b₂)
  have hm₃ := compatM_transport (Over.pullback (D.map b₃)) (Over.pullback (c.π.app k₃))
    (Over.pullback (c.π.app ((s.next b₁).next b₂).k)) (stθ D c b₃) ((s.next b₁).next b₂).e hm₂
  have hu₃ := compatU_transport (Over.pullback (D.map b₃)) (Over.pullback (c.π.app k₃))
    (Over.pullback (c.π.app ((s.next b₁).next b₂).k)) (stθ D c b₃) ((s.next b₁).next b₂).e hu₂
  obtain ⟨k₄, b₄, hF⟩ := ev_fAx D c hc (((s.next b₁).next b₂).next b₃).e hm₃ hu₃ hi₃
  letI : GrpObj ((Over.pullback (D.map b₄)).obj (((s.next b₁).next b₂).next b₃).M) :=
    ((grpAx_map_iff (Over.pullback (D.map b₄)) _ _ _).2 hF).grpObj
  refine ⟨(((s.next b₁).next b₂).next b₃).next b₄, hQ _ _ (hQ _ _ (hQ _ _ (hQ _ _ hs))), ?_⟩
  exact ⟨this, isMonHom_descend
    (Over.pullback (D.map b₄)) (Over.pullback (c.π.app k₄))
    (Over.pullback (c.π.app (((s.next b₁).next b₂).next b₃).k)) (stθ D c b₄)
    (((s.next b₁).next b₂).next b₃).e hm₃ hu₃ hi₃ hF⟩

end StageQ

end ZInQ.Contrib.GroupLaw
