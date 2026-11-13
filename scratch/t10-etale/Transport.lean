import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

open CategoryTheory Limits AlgebraicGeometry Opposite Scheme

universe u

namespace T10Transport

set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- `π_X : X.ProEt ⥤ Scheme`, `(U → X) ↦ U`. -/
abbrev piX (X : Scheme.{u}) : X.ProEt ⥤ Scheme.{u} := Scheme.ProEt.forget X ⋙ Over.forget X

/-- **Lemma A.** A sieve on `U` in the small pro-étale site of `X` covers iff its image in
`Scheme` is a pro-étale covering sieve of `U.left`. -/
lemma mem_topology_iff {U : X.ProEt} (S : Sieve U) :
    S ∈ Scheme.ProEt.topology X U ↔ S.functorPushforward (piX X) ∈ proetaleTopology U.left := by
  have h2 : Scheme.ProEt.topology X =
      (Scheme.ProEt.forget X).restrictedTopology (proetaleTopology.over X) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology (P := @WeaklyEtale) (S := X)
      _ proetalePrecoverage_le_precoverage_weaklyEtale
  rw [h2, Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
    Sieve.functorPushforward_comp]
  rfl


/-- `WeaklyEtale` holds for isomorphisms. -/
lemma weaklyEtale_hom (e : X ≅ Y) : (@WeaklyEtale : MorphismProperty Scheme.{u}) e.hom :=
  (inferInstance : WeaklyEtale e.hom)

/-- The functor `X.ProEt ⥤ Y.ProEt`, `(U → X) ↦ (U → X → Y)`, for a scheme isomorphism `e`. -/
noncomputable def proEtMap (e : X ≅ Y) : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (weaklyEtale_hom e)

/-- The equivalence of small pro-étale sites induced by a scheme isomorphism. -/
noncomputable def proEtEquiv (e : X ≅ Y) : X.ProEt ≌ Y.ProEt :=
  CategoryTheory.Equivalence.mk (proEtMap e) (proEtMap e.symm)
    ((MorphismProperty.Over.mapId ⊤ X).symm ≪≫
      MorphismProperty.Over.mapComp ⊤ (weaklyEtale_hom e) (weaklyEtale_hom e.symm) (𝟙 X) (by simp))
    ((MorphismProperty.Over.mapComp ⊤ (weaklyEtale_hom e.symm) (weaklyEtale_hom e) (𝟙 Y)
      (by simp)).symm ≪≫ MorphismProperty.Over.mapId ⊤ Y)

instance (e : X ≅ Y) : (proEtEquiv e).inverse.IsDenseSubsite (Scheme.ProEt.topology Y)
    (Scheme.ProEt.topology X) where
  functorPushforward_mem_iff {U S} := by
    rw [mem_topology_iff, mem_topology_iff, ← Sieve.functorPushforward_comp]
    rfl

/-- The equivalence of categories of abelian sheaves on the pro-étale sites. -/
noncomputable def sheafEquiv (e : X ≅ Y) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u+1} ≌ Sheaf (Scheme.ProEt.topology Y) Ab.{u+1} :=
  (proEtEquiv e).sheafCongr _ _ _

instance (e : X ≅ Y) : (sheafEquiv e).functor.Additive where
  map_add := by intros; apply Sheaf.hom_ext; rfl


variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient sheaf of `EllAdicCohomology` (after the universe lift). -/
noncomputable abbrev Fs (X : Scheme.{u}) : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u+1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)

/-- The sheaf equivalence carries the `ℓ`-adic coefficient sheaf of `X` to that of `Y`
(componentwise the identity of `ULift C(U, ℤ_ℓ)`). -/
noncomputable def ellIso (e : X ≅ Y) : (sheafEquiv e).functor.obj (Fs ℓ X) ≅ Fs ℓ Y :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- `X → X`, the terminal object of `X.ProEt`. -/
noncomputable def terminalProEt (X : Scheme.{u}) : X.ProEt :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)

noncomputable def isTerminalProEt (X : Scheme.{u}) : IsTerminal (terminalProEt X) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

/-- The sheaf equivalence carries constant sheaves to constant sheaves (uniqueness of left
adjoints of the global-sections functor). -/
noncomputable def constIso (e : X ≅ Y) (A : Ab.{u+1}) :
    (sheafEquiv e).functor.obj ((constantSheaf (Scheme.ProEt.topology X) Ab.{u+1}).obj A) ≅
      (constantSheaf (Scheme.ProEt.topology Y) Ab.{u+1}).obj A :=
  let hT' : IsTerminal ((proEtEquiv e).functor.obj (terminalProEt X)) :=
    (isTerminalProEt X).isTerminalObj _
  let adj1 := (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u+1} (isTerminalProEt X)).comp
    (sheafEquiv e).toAdjunction
  let adj2 := constantSheafAdj (Scheme.ProEt.topology Y) Ab.{u+1} hT'
  let iso : (sheafEquiv e).inverse ⋙ (sheafSections _ _).obj (op (terminalProEt X)) ≅
      (sheafSections _ _).obj (op ((proEtEquiv e).functor.obj (terminalProEt X))) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
      simp only [Iso.refl_hom]; rfl)
  (Adjunction.leftAdjointUniq (adj1.ofNatIsoRight iso) adj2).app A

/-- **Transport of `ℓ`-adic cohomology along a scheme isomorphism** `e : X ≅ Y`
(`e_* = (e⁻¹)^*`). -/
noncomputable def transport (e : X ≅ Y) (n : ℕ) :
    X.EllAdicCohomology ℓ n →+ Y.EllAdicCohomology ℓ n :=
  ((Abelian.Ext.mk₀ (constIso e _).inv).precomp _ (zero_add n)).comp
    (((Abelian.Ext.mk₀ (ellIso ℓ e).hom).postcomp _ (add_zero n)).comp
      ((sheafEquiv e).functor.mapExtAddHom _ _ n))

end T10Transport
