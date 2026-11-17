/-
NEW EDITION 2: Lane2 world004 explicit projection flatness, 2026-11-17.
Probe base SHA3a84900e83f2a16ce4b5538f1f6662877443b086061dab74ebb6699e15be11ff.
Edition 1 and its h5w4p1 failure log remain unchanged.
The only proof change explicitly derives Flat q from the original field
spectrum and Flat p from the SAME literal base-change projection. No new
hypothesis, carrier, module, ideal, namespace, public statement or option.
Parent probes this new Source; no lane compiler/parser/AST/helper run.
-/
/-
NEW EDITION: Lane2 world004 divisor repair, 2026-11-17.
Parent/H5 lead requested Source-only repairs and Parent-run probes.
Base NativeDivisorKernel.lean:
1a9fd7cbc05c65dab36dd7b4bebc6da89b66bfd0c41adbfb47b6ad83011d574e.
The base file and its failed world004 proof history remain unchanged.
Changes are proof-local only: pin p, Msbar, theta-bar and Dbar to the
SAME Hbar.X.left; derive native invertibility of the literal pulled Ms;
ascribe the Cartier representation before removing its unit factor; pass
I1 explicitly in the final application. Public statements, namespace,
original group/field/points/maps/modules/ideals and universe u are unchanged.
UNCOMPILED new Source. No lane compile, parser/AST/helper or Native run.
-/
/-
H5 original-input Step 2 / GM8: native divisor-stabilizer inclusion.
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.

NEW Source-only proof, UNCOMPILED. Native remains HELD.
This is the literal H(D) subset K(M) edge, not the contracted-curve theorem,
basepoint freeness, ampleness, construction of a finite projective map, I0,
I1, I2, or either original NOS equivalence.

The given native module, section and Cartier zero ideal are kept. All
pullbacks/tensors/duals below are actual Scheme.Modules operations. We do
not install a Source/W07 alias, a square/cube Fact, a model or a finite-kernel
assumption. The terminal-point right translation is exactly C3's agreed I1.

Sources read before authoring: frozen Task-A provider record d1346f11 and
independent H71 L1 review 86d27970; Parent plan c3e58087. Existing zero-locus
and divisor-line primitives are reused by their literal names; they are not
reproved or claimed newly admitted by this Source. H71 cube 3b509d68 remains
an independent pending/uncompiled dependency and is not needed here.

References: Mumford, Abelian Varieties, section 6, Application 1.
W07 native zero-locus primitives retain their c4254cce Apache-2.0 headers,
LICENSE and NOTICE unchanged. No proof text from a held FLT module is copied.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeDivisorKernel

/-- The exact terminal-point right translation used in the agreed I1.
The group object, not an independently chosen law, supplies multiplication. -/
def rightTranslationOver {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) : G.X ⟶ G.X :=
  lift (𝟙 G.X) (toUnit G.X ≫ x) ≫ μ[G.X]

/-- The underlying map is literally the agreed right-translation scheme map. -/
def rightTranslation {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) : G.X.left ⟶ G.X.left :=
  (rightTranslationOver G x).left

/-- Scheme-theoretic divisor preservation; this is not just support equality. -/
def divisorStabilizer {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) (D : G.X.left.IdealSheafData) :
    Set (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :=
  {x | D.comap (rightTranslation G x) = D}

/-- The native line-isomorphism kernel of the same group/module. -/
def moduleStabilizer {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) (M : G.X.left.Modules) :
    Set (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :=
  {x | Nonempty ((Scheme.Modules.pullback (rightTranslation G x)).obj M ≅ M)}

/-- Any actual self-map preserving the given Cartier zero ideal preserves the
same divisor line. There is no abelian, field, characteristic or dimension
restriction in this elementary native edge. -/
theorem nonempty_pullback_iso_of_preserves_zero_divisor
    {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (θ : Scheme.Modules.unit X ⟶ M) (D : X.IdealSheafData)
    (hD : D.IsInvertible) (hZero : D = θ.zeroLocus)
    (hMD : Nonempty (M ≅ D.toModulesᵛ))
    (t : X ⟶ X) (ht : D.comap t = D) :
    Nonempty ((Scheme.Modules.pullback t).obj M ≅ M) := by
  let φ := (Scheme.Modules.pullback t).map θ
  have hφ : φ.zeroLocus = D := by
    change ((Scheme.Modules.pullback t).map θ).zeroLocus = D
    rw [← Scheme.Modules.Hom.comap_zeroLocus, ← hZero, ht]
  have hregular : φ.zeroLocus.IsInvertible := by
    rw [hφ]
    exact hD
  letI : D.toModules.IsInvertible := hD.isInvertible_toModules
  obtain ⟨eφ⟩ := Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj φ hregular
  have hp : Nonempty ((Scheme.Modules.pullback t).obj M ≅
      D.toModulesᵛ ⊗ (Scheme.Modules.pullback t).obj (Scheme.Modules.unit X)) := by
    simpa only [hφ] using (show Nonempty (_ ≅ _) from ⟨eφ⟩)
  obtain ⟨ep⟩ := hp
  obtain ⟨eMD⟩ := hMD
  exact ⟨ep ≪≫ whiskerLeftIso D.toModulesᵛ (Scheme.Modules.pullbackObjUnitIso t) ≪≫
    ρ_ D.toModulesᵛ ≪≫ eMD.symm⟩

/-- H(D) is contained in the literal native K(M) of the same right action. -/
theorem divisorStabilizer_subset_moduleStabilizer
    {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (M : G.X.left.Modules) [M.IsInvertible]
    (θ : Scheme.Modules.unit G.X.left ⟶ M) (D : G.X.left.IdealSheafData)
    (hD : D.IsInvertible) (hZero : D = θ.zeroLocus)
    (hMD : Nonempty (M ≅ D.toModulesᵛ)) :
    divisorStabilizer G D ⊆ moduleStabilizer G M := by
  intro x hx
  exact nonempty_pullback_iso_of_preserves_zero_divisor M θ D hD hZero hMD
    (rightTranslation G x) hx

/-- The agreed I1 point-finiteness output gives point-finiteness of H(D).
I1 is an earlier producer OUTPUT; this lemma does not supply that output. -/
theorem divisorStabilizer_finite_of_moduleStabilizer_finite
    {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (M : G.X.left.Modules) [M.IsInvertible]
    (θ : Scheme.Modules.unit G.X.left ⟶ M) (D : G.X.left.IdealSheafData)
    (hD : D.IsInvertible) (hZero : D = θ.zeroLocus)
    (hMD : Nonempty (M ≅ D.toModulesᵛ))
    (hI1 : (moduleStabilizer G M).Finite) :
    (divisorStabilizer G D).Finite :=
  hI1.subset (divisorStabilizer_subset_moduleStabilizer G M θ D hD hZero hMD)

/-- The given section is not zero precisely in the load-bearing way needed
for D to be a proper zero scheme. Effectivity is not inferred from Euler. -/
theorem zero_divisor_ne_bot_of_section_ne_zero
    {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (θ : Scheme.Modules.unit X ⟶ M) (hθ : θ ≠ 0)
    (D : X.IdealSheafData) (hZero : D = θ.zeroLocus) : D ≠ ⊥ := by
  intro h
  apply hθ
  apply (Scheme.Modules.Hom.zeroLocus_eq_bot_iff θ).mp
  rw [← hZero, h]

/-- The actual unit-source pullback of the given section, with no chosen
new point or line. The source-unit isomorphism is a genuine native map. -/
def pulledSectionHom {X Y : Scheme.{u}} (p : Y ⟶ X)
    (M : X.Modules) (θ : Scheme.Modules.unit X ⟶ M) :
    Scheme.Modules.unit Y ⟶ (Scheme.Modules.pullback p).obj M :=
  (Scheme.Modules.pullbackObjUnitIso p).inv ≫ (Scheme.Modules.pullback p).map θ

/-- The zero ideal of the literal pulled section is the literal comap of
D. This keeps the scheme-theoretic Cartier data, not only its support. -/
theorem pulledSectionHom_zeroLocus {X Y : Scheme.{u}} (p : Y ⟶ X)
    (M : X.Modules) [M.IsInvertible] (θ : Scheme.Modules.unit X ⟶ M) :
    (pulledSectionHom p M θ).zeroLocus = θ.zeroLocus.comap p := by
  have e : Arrow.mk ((Scheme.Modules.pullback p).map θ) ≅
      Arrow.mk (pulledSectionHom p M θ) :=
    Arrow.isoMk (Scheme.Modules.pullbackObjUnitIso p)
      (Iso.refl ((Scheme.Modules.pullback p).obj M)) (by
        simp [pulledSectionHom])
  exact (Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _ e).symm.trans
    (Scheme.Modules.Hom.comap_zeroLocus p θ).symm

/-- Apply the inclusion to EXACTLY the geometric pullbacks of the special
field's group, line, section and ideal. This is the consumer-fixed I1 spelling.
The finiteness premise is C3's future I1 OUTPUT, not a new NOS premise. -/
theorem geometric_divisorStabilizer_finite_of_I1
    {k : Type u} [Field k]
    (Hs : Grp (Over (Spec (CommRingCat.of k))))
    (Ms : Hs.X.left.Modules) [Ms.IsInvertible]
    (θ : Scheme.Modules.unit Hs.X.left ⟶ Ms)
    (D : Hs.X.left.IdealSheafData) (hD : D.IsInvertible)
    (hZero : D = θ.zeroLocus) :
    let q := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    let Hbar := PkgI2.baseChange Hs (AlgebraicClosure k)
    let Msbar := (Scheme.Modules.pullback (pullback.fst Hs.X.hom q)).obj Ms
    let Dbar := D.comap (pullback.fst Hs.X.hom q)
    {x : 𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶ Hbar.X |
      Nonempty ((Scheme.Modules.pullback
        (lift (𝟙 Hbar.X) (toUnit Hbar.X ≫ x) ≫ μ[Hbar.X]).left).obj Msbar ≅ Msbar)}.Finite →
      (divisorStabilizer Hbar Dbar).Finite := by
  dsimp only
  let q := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let Hbar := PkgI2.baseChange Hs (AlgebraicClosure k)
  let p : Hbar.X.left ⟶ Hs.X.left := pullback.fst Hs.X.hom q
  haveI : Flat q := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    infer_instance
  haveI : Flat p := by
    change Flat (pullback.fst Hs.X.hom q)
    infer_instance
  let Msbar : Hbar.X.left.Modules := (Scheme.Modules.pullback p).obj Ms
  letI : Msbar.IsInvertible := by
    dsimp only [Msbar]
    infer_instance
  let θbar : Scheme.Modules.unit Hbar.X.left ⟶ Msbar := pulledSectionHom p Ms θ
  let Dbar : Hbar.X.left.IdealSheafData := D.comap p
  intro hI1
  have hDbar : Dbar.IsInvertible := hD.comap_of_flat p
  have hZbar : Dbar = θbar.zeroLocus := by
    dsimp only [Dbar, θbar]
    rw [pulledSectionHom_zeroLocus, ← hZero]
  have hbar : Nonempty (Msbar ≅ Dbar.toModulesᵛ) := by
    have hθbar : θbar.zeroLocus.IsInvertible := by
      rw [← hZbar]
      exact hDbar
    letI : Dbar.toModules.IsInvertible := hDbar.isInvertible_toModules
    have hRep : Nonempty (Msbar ≅ θbar.zeroLocus.toModulesᵛ ⊗
        Scheme.Modules.unit Hbar.X.left) :=
      Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj θbar hθbar
    obtain ⟨e⟩ := hRep
    rw [← hZbar] at e
    exact ⟨e ≪≫ ρ_ Dbar.toModulesᵛ⟩
  exact divisorStabilizer_finite_of_moduleStabilizer_finite
    Hbar Msbar θbar Dbar hDbar hZbar hbar hI1

end H5OriginalDVR.Lane2.NativeDivisorKernel
