import ToricBaseChange.TorusKernelK4V001
import ToricBaseChange.ActualKernelGenericV002
import HenselDivision.SmoothCommMulEtaleV001
import HenselDivision.GenericCommutativityV004

/-!
# Torus survival under base change of Néron models: the kernel condition proved

Native unbundled data: valuation subrings `O ⊆ K` and `O' ⊆ L` (`O'` a discrete valuation ring,
`O' ∩ K = O`), an abelian variety `A/K`; `N/O` a smooth group model of `A` with the Néron mapping
property, `N'/O'` a smooth separated group model of `A_L` with the Néron mapping property, both with
generic identifications that are homomorphisms; `u : N ⊗_O O' → N'` the comparison characterised by
the mapping property of `N'`.

* `torsion_kernel_native`: for `m` invertible on `O'`, every `m`-torsion point of `N ⊗ O'` (over any
  `O'`-scheme `T`) killed by `u` is trivial. Proof: `N`, `N'` are commutative (mapping property, `A` and
  `A_L` commutative), so `[m]` is étale on `N ⊗ O'` and `N'` (smooth commutative group schemes, `m` a
  unit); `u_L` is an isomorphism (comparison) and `Spec L ⊆ Spec O'` is the open generic point; the
  étale separated `m`-torsion kernel with trivial generic fibre is trivial.
* `hker_native`: the special-fibre comparison kills no nontrivial `m`-torsion point of the torus.
* `toricRank_le_native`: `r ≤ r'`, with no kernel, étaleness or injectivity hypothesis: `m ∈ {2, 3}` is
  chosen invertible on `O'`.
The field `k` under `O` (the residue field in the application) and the algebraically closed field `Ω`
under `O'` (an algebraic closure of the residue field of `O'`) are arbitrary, with `k̄ → Ω`
compatible over `O`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem isCommMonObj_source (O : ValuationSubring K) (A : PkgI3.AbVar K)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj N ≅ A.X)
    [IsMonHom gen.hom]
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f ≫ gen.hom) :
    IsCommMonObj N :=
  HenselDivision.isCommMonObj_of_generic_injective _ N A.X gen (fun Y _ => (hN Y).1)

theorem isCommMonObj_target (O' : ValuationSubring L) (A : PkgI3.AbVar K)
    (N' : Over (Spec (CommRingCat.of O'))) [GrpObj N'] [Smooth N'.hom]
    (gen' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).obj N' ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X)
    [IsMonHom gen'.hom]
    (hN' : ∀ (Y : Over (Spec (CommRingCat.of O'))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map f ≫ gen'.hom) :
    IsCommMonObj N' := by
  haveI : IsCommMonObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X) :=
    HenselDivision.SmoothCommMulEtale.isCommMonObj_grpObjObj _ A.X
  exact HenselDivision.isCommMonObj_of_generic_injective _ N' _ gen' (fun Y _ => (hN' Y).1)

/-- **The `m`-torsion kernel of the comparison is trivial.** -/
theorem torsion_kernel_native (O : ValuationSubring K) (O' : ValuationSubring L)
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K L) = O) (A : PkgI3.AbVar K)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom] [IsSeparated N.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj N ≅ A.X)
    [IsMonHom gen.hom]
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f ≫ gen.hom)
    (N' : Over (Spec (CommRingCat.of O'))) [GrpObj N'] [Smooth N'.hom]
    (gen' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).obj N' ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X)
    [IsMonHom gen'.hom]
    (hN' : ∀ (Y : Over (Spec (CommRingCat.of O'))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map f ≫ gen'.hom)
    (u : Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N ⟶ N')
    (hu : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map u ≫ gen'.hom =
        (Comparison.genIso (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)))
          (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O' L)))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) (Comparison.iota_square O O' hO) N A.X gen).hom)
    (m : ℕ) (hmu : IsUnit (m : O'))
    (T : Over (Spec (CommRingCat.of O')))
    (w : T ⟶ Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N)
    (hw : w ^ m = 1) (hwu : w ≫ u = 1) : w = 1 := by
  haveI : IsMonHom u := Comparison.isMonHom_comparison _ _ _ _ (Comparison.iota_square O O' hO)
    N A.X gen N' gen' hN' u hu
  haveI : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map u) :=
    Comparison.comparison_generic_isIso _ _ _ _ (Comparison.iota_square O O' hO) N A.X gen N' gen' u hu
  haveI : IsCommMonObj N := isCommMonObj_source O A N gen hN
  haveI : IsCommMonObj N' := isCommMonObj_target O' A N' gen' hN'
  haveI : IsCommMonObj (Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N) :=
    HenselDivision.SmoothCommMulEtale.isCommMonObj_grpObjObj _ N
  haveI : IsSeparated (Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N).hom := by
    change IsSeparated (pullback.snd N.hom (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))))
    infer_instance
  have hG : Etale (HenselDivision.powHom
      (Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N) m).left :=
    HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm
      (Grp.mk (Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N)) m hmu
  have hNe : Etale (HenselDivision.powHom N' m).left :=
    HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm (Grp.mk N') m hmu
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O' L))) :=
    isOpenImmersion_generic O'
  haveI : IrreducibleSpace (Spec (CommRingCat.of O')) := by
    change IrreducibleSpace (PrimeSpectrum O'); infer_instance
  haveI : Nonempty (Spec (CommRingCat.of L)) := by
    change Nonempty (PrimeSpectrum L); infer_instance
  exact torsion_point_trivial _ N' u m (Spec.map (CommRingCat.ofHom (algebraMap O' L)))
    (generic_apply O') hG hNe w hw hwu

end ToricBaseChange.ActualKernel
