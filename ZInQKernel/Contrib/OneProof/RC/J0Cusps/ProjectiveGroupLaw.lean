import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupIdentities
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveChartGluing

/-! The scheme group law on the fixed Weierstrass model over ℚ.
On the spot (c), tex 1785–1787. -/

noncomputable section

open scoped Classical

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.J0Cusps

open PreparedParam

theorem exists_projectiveMultiplication (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ m : projectiveTarget E ⊗ projectiveTarget E ⟶ projectiveTarget E,
      ∀ (F : Type) [Field F] [Algebra ℚ F] (p q : AbVar.ptObj (K := ℚ) F ⟶ projectiveTarget E),
        projectiveValue (lift p q ≫ m).left = projectiveValue p.left + projectiveValue q.left := by
  let X := projectiveTarget E
  let T := X ⊗ X
  haveI : IsReduced T.left := projectiveTarget_square_reduced E
  let f (i : Fin 2) : T.left ⟶ X.left := ![(fst X X).left, (snd X X).left] i
  obtain ⟨m, hm⟩ := projectiveMorphism_of_formulas E T.left T.hom f
    (I := Bool)
    (by intro R _ _ b v; exact additionCoordinates E b (v 0) (v 1))
    (by intro F _ _ p; exact p 0 + p 1)
    (by intro R S _ _ _ _ g b v; exact additionCoordinates_map E g b (v 0) (v 1))
    (by intro F _ _ v hv; exact additionCoordinates_fields E (hv 0) (hv 1))
  refine ⟨Over.homMk m (schemeMapsToRat_unique _ _), ?_⟩
  intro F _ _ p q
  have hp : (lift p q).left ≫ (fst X X).left = p.left :=
    congrArg (fun u => u.left) (lift_fst p q)
  have hq : (lift p q).left ≫ (snd X X).left = q.left :=
    congrArg (fun u => u.left) (lift_snd p q)
  change projectiveValue ((lift p q).left ≫ m) = _
  calc
    _ = projectiveValue ((lift p q).left ≫ (fst X X).left) +
        projectiveValue ((lift p q).left ≫ (snd X X).left) := hm F (lift p q).left
    _ = _ := congrArg₂ (· + ·)
      (congrArg (projectiveValue (E := E) (F := F)) hp)
      (congrArg (projectiveValue (E := E) (F := F)) hq)

theorem exists_projectiveInversion (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ n : projectiveTarget E ⟶ projectiveTarget E,
      ∀ (F : Type) [Field F] [Algebra ℚ F] (p : AbVar.ptObj (K := ℚ) F ⟶ projectiveTarget E),
        projectiveValue (p ≫ n).left = -projectiveValue p.left := by
  let X := projectiveTarget E
  haveI : IsReduced X.left := isReduced_proj E
  obtain ⟨n, hn⟩ := projectiveMorphism_of_formulas E X.left X.hom (fun (_ : Fin 1) => 𝟙 _)
    (I := Unit)
    (by intro R _ _ _ v; exact (E.baseChange R).toProjective.neg (v 0))
    (by intro F _ _ p; exact -p 0)
    (by
      intro R S _ _ _ _ g _ v
      have eq : (E.baseChange R).toProjective.map g = (E.baseChange S).toProjective := by
        change (E.map (algebraMap ℚ R)).map g = E.map (algebraMap ℚ S)
        rw [E.map_map, show g.comp (algebraMap ℚ R) = algebraMap ℚ S from Subsingleton.elim _ _]
      rw [← eq, Projective.map_neg])
    (by
      intro F _ _ v h
      have hv := (E.baseChange F).toProjective.nonsingular_neg (h 0)
      exact ⟨⟨(), projectiveNonsingular_ne_zero hv⟩,
        fun _ _ => ⟨hv.1, Projective.Point.toAffine_neg (h 0)⟩⟩)
  refine ⟨Over.homMk n (schemeMapsToRat_unique _ _), ?_⟩
  intro F _ _ p
  have hp : p.left ≫ 𝟙 X.left = p.left := Category.comp_id _
  change projectiveValue (p.left ≫ n) = _
  calc
    _ = -projectiveValue (p.left ≫ 𝟙 X.left) := hn F p.left
    _ = _ := congrArg (fun t => -projectiveValue (E := E) (F := F) t) hp

/-- The chord-and-tangent law is a group object on the fixed projective
Weierstrass model over ℚ. Its complex points add by coordinate evaluation. -/
theorem projectiveGroup_exists (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ g : GrpObj (projectiveTarget E), letI := g
      ∀ p q : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E,
        projectiveValue (p * q).left = projectiveValue p.left + projectiveValue q.left := by
  obtain ⟨m, hm⟩ := exists_projectiveMultiplication E
  obtain ⟨n, hn⟩ := exists_projectiveInversion E
  refine ⟨projectiveGroupOfOperations E m n hm hn, ?_⟩
  intro p q
  exact hm ℂ p q


end ZInQ.Manuscript.RC.J0Cusps
