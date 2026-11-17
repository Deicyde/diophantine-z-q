/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/I1BaseChange.lean (sha256 6229ec967745a9cb7602ce34884260717332ad12c6fef6cc69cfafaa4045682e).
Body changes relative to the base: ONLY P2 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 1, component I1a: base change of the native Euler characteristic along k ⊆ k̄.
2026-11-17, v2. New file. SOURCE-ONLY, UNCOMPILED. Universe u, any field k (no characteristic,
perfectness or dimension restriction).

v2 change, Over instances only (v1 c93facbd is kept in `step1-i1/history/`):
* `Msbar` is typed on `H̄.X.left` with `H̄ = PkgI2.baseChange Hs k̄`. It is defeq to the literal
  `Limits.pullback Hs.X.hom g`.
* Every Euler characteristic now carries an EXPLICIT Over instance: `⟨H̄.X.hom⟩` over `k̄`
  (= `pullback.snd Hs.X.hom g` definitionally) and `⟨Hs.X.hom⟩` over `k`.
* v1 relied on `canonicallyOverPullback` firing on `Limits.pullback Hs.X.hom g`. That instance
  only matches the syntactic `pullback (X ↘ S) f` form.

Proof: the published W07 `Scheme.Modules.eulerChar_pullback` (Cohomology/FieldExtension.lean, fork
2880 sha256 c89aa5fd…). Its hypotheses are DERIVED:
* qc/qs from properness;
* quasi-coherence from invertibility (W07 `SheafOfModules.IsInvertible.isQuasicoherent`).
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- `H̄ = PkgI2.baseChange Hs k̄` is an abelian variety. Each defining property of
`PkgI2.IsAbelianVariety` is stable under the literal base change `pullback.snd`. -/
instance isAbelianVariety_baseChange {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k))))
    [PkgI2.IsAbelianVariety Hs] (K' : Type u) [Field K'] [Algebra k K'] :
    PkgI2.IsAbelianVariety (PkgI2.baseChange Hs K') := by
  haveI : IsProper Hs.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : Smooth Hs.X.hom := PkgI2.IsAbelianVariety.smooth
  haveI : GeometricallyIntegral Hs.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  refine ⟨?_, ?_, ?_⟩
  · change IsProper (pullback.snd Hs.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K'))))
    infer_instance
  · change Smooth (pullback.snd Hs.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K'))))
    infer_instance
  · change GeometricallyIntegral (pullback.snd Hs.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K'))))
    infer_instance

/-- The literal `k̄`-pullback of the SAME line `Ms` (agreed I1 form), on `H̄.X.left`. -/
abbrev Msbar {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k))))
    (Ms : Hs.X.left.Modules) : (PkgI2.baseChange Hs (AlgebraicClosure k)).X.left.Modules :=
  (Scheme.Modules.pullback (pullback.fst Hs.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))).obj Ms

/-- I1a: `χ_{k̄}(M̄) = χ_k(Ms)`, with explicit Over instances. -/
theorem eulerChar_Msbar {k : Type u} [Field k]
    (Hs : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety Hs]
    (Ms : Hs.X.left.Modules) [Ms.IsInvertible] :
    (letI : (PkgI2.baseChange Hs (AlgebraicClosure k)).X.left.Over
        (Spec (CommRingCat.of (AlgebraicClosure k))) :=
      ⟨(PkgI2.baseChange Hs (AlgebraicClosure k)).X.hom⟩
     (Msbar Hs Ms).eulerChar (AlgebraicClosure k)) =
    (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
     Ms.eulerChar k) := by
  letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
  haveI : IsProper Hs.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : QuasiCompact (Hs.X.left ↘ Spec (CommRingCat.of k)) :=
    show QuasiCompact Hs.X.hom from inferInstance
  haveI : QuasiSeparated (Hs.X.left ↘ Spec (CommRingCat.of k)) :=
    show QuasiSeparated Hs.X.hom from inferInstance
  haveI : Ms.IsQuasicoherent := SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u} ‹Ms.IsInvertible›
  -- W07 states this over the canonical instance on `pullback (X ↘ Spec k) g`, whose structure map
  -- is `pullback.snd Hs.X.hom g`, i.e. `H̄.X.hom` by definition.
  exact Scheme.Modules.eulerChar_pullback (AlgebraicClosure k) Ms

end ZInQ.Contrib.CloudR2NOS.Step1
