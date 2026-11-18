import HenselDivision.TorsionKernelV005
import ToricBaseChange.EtaleKernelPointsV002
import ToricBaseChange.ActualKernelDVRV002

/-!
# The `m`-torsion kernel of a homomorphism with generic isomorphism is trivial

`S'` an irreducible scheme with generic point `η`, `j : E → S'` an open immersion onto `{η}` (for a
discrete valuation ring `O'`, `Spec L → Spec O'`), `u : G → N'` a homomorphism of group schemes over
`S'` whose base change along `j` is an isomorphism.

* `generic_kernel_trivial`: a point of `G` over `η` sent by `u` to the unit section lies on the unit
  section (the generic fibre is the open subscheme over `η`, where `u` is an isomorphism).
* `torsionMap`: the actual map `G[m] → N'[m]` of the torsion pullbacks induced by `u`;
  `torsionUnit`: their unit sections.
* `torsion_point_trivial`: if `[m]` is étale on `G` and on `N'` and `G` is separated, every `T`-point
  `w` of `G` with `w^m = 1` and `w ≫ u = 1` is trivial. Proof: `w` is a `T`-point of the étale
  separated `G[m]` killed by `torsionMap`, whose kernel is trivial over `η`; the vanishing of étale
  kernels with trivial generic fibre (`kernel_morphism_trivial`) gives `w = 1`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

variable {S' E : Scheme.{0}}

theorem toUnit_left (T : Over S') : (toUnit T).left = T.hom := by
  have h := Over.w (toUnit T)
  simpa using h

theorem eta_eq_one (G : Over S') [GrpObj G] : η[G] = (1 : 𝟙_ (Over S') ⟶ G) := by
  rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S'))) (𝟙 _), Category.id_comp]

/-- The unit of the base change, on points over `η`. -/
theorem fst_unit_apply [IrreducibleSpace S'] (j : E ⟶ S') (hj : ∀ a, j a = genericPoint S')
    (G : Over S') [GrpObj G] (a : (𝟙_ (Over E)).left) :
    pullback.fst G.hom j (η[(Over.pullback j).obj G].left a) = η[G].left (genericPoint S') := by
  have h1 : η[(Over.pullback j).obj G].left ≫ pullback.fst G.hom j =
      (Functor.LaxMonoidal.ε (Over.pullback j)).left ≫ pullback.fst (𝟙_ (Over S')).hom j ≫
        η[G].left := by
    change (Functor.LaxMonoidal.ε (Over.pullback j) ≫ (Over.pullback j).map η[G]).left ≫
      pullback.fst G.hom j = _
    rw [Over.comp_left, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  congr 1
  set q := (Functor.LaxMonoidal.ε (Over.pullback j)).left a
  have hc := pullback.condition (f := (𝟙_ (Over S')).hom) (g := j)
  have h2 : (pullback.fst (𝟙_ (Over S')).hom j ≫ (𝟙_ (Over S')).hom) q =
      (pullback.snd (𝟙_ (Over S')).hom j ≫ j) q := by rw [hc]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hj] at h2
  exact h2

/-- **The generic kernel is trivial.** -/
theorem generic_kernel_trivial [IrreducibleSpace S'] (j : E ⟶ S') [IsOpenImmersion j]
    (hj : ∀ a, j a = genericPoint S') [Nonempty E]
    (G N' : Over S') [GrpObj G] [GrpObj N'] (u : G ⟶ N') [IsMonHom u]
    [IsIso ((Over.pullback j).map u)] (g : G.left) (hg : G.hom g = genericPoint S')
    (hu : u.left g ∈ Set.range η[N'].left) : g ∈ Set.range η[G].left := by
  obtain ⟨a0⟩ := ‹Nonempty E›
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := j) g a0
    (hg.trans (hj a0).symm)
  obtain ⟨s, hs⟩ := hu
  have hs' : s = genericPoint S' := by
    have h1 : N'.hom (η[N'].left s) = s := by
      rw [← Scheme.Hom.comp_apply, HenselDivision.eta_comp_hom]; rfl
    have h2 : N'.hom (u.left g) = G.hom g := by
      rw [← Scheme.Hom.comp_apply, Over.w u]
    rw [← h1, hs, h2, hg]
  subst hs'
  let uL := (Over.pullback j).map u
  have key1 : uL.left ≫ pullback.fst N'.hom j = pullback.fst G.hom j ≫ u.left := by
    simp [uL]
  have hfst : pullback.fst N'.hom j (uL.left z) =
      pullback.fst N'.hom j (η[(Over.pullback j).obj N'].left (pullback.snd G.hom j z)) := by
    rw [fst_unit_apply j hj N', ← Scheme.Hom.comp_apply, key1, Scheme.Hom.comp_apply, hz1, hs]
  have hinj' : Function.Injective (pullback.fst N'.hom j) :=
    (pullback.fst N'.hom j).isOpenEmbedding.injective
  have h3 : uL.left z = η[(Over.pullback j).obj N'].left (pullback.snd G.hom j z) := hinj' hfst
  have h4 : uL.left (η[(Over.pullback j).obj G].left (pullback.snd G.hom j z)) =
      η[(Over.pullback j).obj N'].left (pullback.snd G.hom j z) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  haveI : IsIso uL.left := (inferInstance : IsIso ((Over.forget E).map uL))
  have hinjL : Function.Injective uL.left := by
    intro x y hxy
    have hx : (uL.left ≫ inv uL.left) x = x := by rw [IsIso.hom_inv_id]; rfl
    have hy : (uL.left ≫ inv uL.left) y = y := by rw [IsIso.hom_inv_id]; rfl
    rw [← hx, ← hy, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hxy]
  have h5 : z = η[(Over.pullback j).obj G].left (pullback.snd G.hom j z) := hinjL (h3.trans h4.symm)
  refine ⟨genericPoint S', ?_⟩
  rw [← hz1, h5]
  exact (fst_unit_apply j hj G _).symm

section Torsion

variable (G N' : Over S') [GrpObj G] [GrpObj N'] (u : G ⟶ N') [IsMonHom u] (m : ℕ)

theorem powHom_comp_hom : HenselDivision.powHom G m ≫ u = u ≫ HenselDivision.powHom N' m := by
  rw [HenselDivision.comp_powHom, HenselDivision.powHom, MonObj.pow_comp, Category.id_comp]

/-- **The map of `m`-torsion schemes induced by `u`.** -/
def torsionMap : HenselDivision.torsionKer G m ⟶ HenselDivision.torsionKer N' m :=
  pullback.map _ _ _ _ u (𝟙 _) u (powHom_comp_hom G N' u m)
    (by rw [Category.id_comp, IsMonHom.one_hom])

theorem torsionMap_ι :
    torsionMap G N' u m ≫ HenselDivision.torsionKerι N' m = HenselDivision.torsionKerι G m ≫ u :=
  pullback.lift_fst _ _ _

/-- The unit section of `G[m]`. -/
def torsionUnit : 𝟙_ (Over S') ⟶ HenselDivision.torsionKer G m :=
  pullback.lift η[G] (𝟙 _) (by
    rw [HenselDivision.comp_powHom, eta_eq_one, one_pow, Category.id_comp])

theorem torsionUnit_ι : torsionUnit G m ≫ HenselDivision.torsionKerι G m = η[G] :=
  pullback.lift_fst _ _ _

theorem torsionUnit_left_hom :
    (torsionUnit G m).left ≫ (HenselDivision.torsionKer G m).hom = 𝟙 S' := by
  rw [Over.w]; rfl

theorem isSeparated_torsionKer [IsSeparated G.hom] : IsSeparated (HenselDivision.torsionKer G m).hom := by
  haveI := HenselDivision.isClosedImmersion_torsionKerι G m
  rw [← Over.w (HenselDivision.torsionKerι G m)]
  infer_instance

/-- **Trivial generic kernel on the torsion schemes.** -/
theorem torsion_generic_trivial [IrreducibleSpace S'] (j : E ⟶ S') [IsOpenImmersion j]
    (hj : ∀ a, j a = genericPoint S') [Nonempty E] [IsSeparated G.hom]
    [IsIso ((Over.pullback j).map u)] (x : (HenselDivision.torsionKer G m).left)
    (hx : (HenselDivision.torsionKer G m).hom x = genericPoint S')
    (hv : (torsionMap G N' u m).left x ∈ Set.range (torsionUnit N' m).left) :
    x ∈ Set.range (torsionUnit G m).left := by
  have hg : G.hom ((HenselDivision.torsionKerι G m).left x) = genericPoint S' := by
    rw [← hx, ← Scheme.Hom.comp_apply, Over.w]
  have hug : u.left ((HenselDivision.torsionKerι G m).left x) ∈ Set.range η[N'].left := by
    obtain ⟨s, hs⟩ := hv
    refine ⟨s, ?_⟩
    rw [← torsionUnit_ι N' m, Over.comp_left, Scheme.Hom.comp_apply, hs, ← Scheme.Hom.comp_apply,
      ← Over.comp_left, torsionMap_ι, Over.comp_left, Scheme.Hom.comp_apply]
  obtain ⟨s, hs⟩ := generic_kernel_trivial j hj G N' u _ hg hug
  refine ⟨s, ?_⟩
  haveI := HenselDivision.isClosedImmersion_torsionKerι G m
  apply (HenselDivision.torsionKerι G m).left.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, torsionUnit_ι, hs]

/-- **A torsion point killed by `u` is trivial**, from étaleness of `[m]` on `G` and `N'`. -/
theorem torsion_point_trivial [IrreducibleSpace S'] (j : E ⟶ S') [IsOpenImmersion j]
    (hj : ∀ a, j a = genericPoint S') [Nonempty E] [IsSeparated G.hom]
    [IsIso ((Over.pullback j).map u)]
    (hG : Etale (HenselDivision.powHom G m).left) (hN : Etale (HenselDivision.powHom N' m).left)
    {T : Over S'} (w : T ⟶ G) (hw : w ^ m = 1) (hwu : w ≫ u = 1) : w = 1 := by
  haveI : Etale (HenselDivision.torsionKer G m).hom := HenselDivision.etale_torsionKer_hom G m hG
  haveI : Etale (HenselDivision.torsionKer N' m).hom := HenselDivision.etale_torsionKer_hom N' m hN
  haveI := isSeparated_torsionKer G m
  let yP := (HenselDivision.torsionKerHomEquiv G m T).symm ⟨w, hw⟩
  have hyP : yP ≫ HenselDivision.torsionKerι G m = w :=
    congrArg Subtype.val ((HenselDivision.torsionKerHomEquiv G m T).apply_symm_apply ⟨w, hw⟩)
  have hyv : yP ≫ torsionMap G N' u m = toUnit T ≫ torsionUnit N' m := by
    haveI := HenselDivision.torsionKerι_mono N' m
    apply (cancel_mono (HenselDivision.torsionKerι N' m)).mp
    rw [Category.assoc, torsionMap_ι, ← Category.assoc, hyP, hwu, Category.assoc, torsionUnit_ι,
      CategoryTheory.Hom.one_def]
  have hleft : yP.left ≫ (torsionMap G N' u m).left =
      (yP.left ≫ (HenselDivision.torsionKer G m).hom) ≫ (torsionUnit N' m).left := by
    rw [← Over.comp_left, hyv, Over.comp_left, Over.w yP, toUnit_left]
  have hres := ToricBaseChange.Vanishing.kernel_morphism_trivial
    (HenselDivision.torsionKer G m).hom (HenselDivision.torsionKer N' m).hom
    (torsionUnit G m).left (torsionUnit_left_hom G m) (torsionUnit N' m).left
    (torsionUnit_left_hom N' m) (torsionMap G N' u m).left
    (fun x hx hv => torsion_generic_trivial G N' u m j hj x hx hv) yP.left hleft
  have hyP1 : yP = toUnit T ≫ torsionUnit G m := by
    apply Over.OverMorphism.ext
    rw [hres, Over.comp_left, Over.w yP, toUnit_left]
  rw [← hyP, hyP1, Category.assoc, torsionUnit_ι, CategoryTheory.Hom.one_def]

end Torsion

end ToricBaseChange.ActualKernel
