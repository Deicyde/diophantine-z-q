import ZInQKernel.Contrib.OneProof.H.TailC
import ZInQKernel.Contrib.OneProof.Genus.LocalDer

/-! # genus-fold: `dim J₁(N) ≤ N²` for the single proof, with no hypothesis

genus-route (`docs/research/genus-route.md`, `scratch/genus-route/Fold.lean`) proved that the two uses of
`t34 : LeafModCurves.DimJ1Genus` in `HSyn.glueOutputs_of_leaves3` (H/TailD.lean, E2 and the
Javanpeykar step) need only `dim J₁(N) ≤ N²`, and proved that bound with no hypothesis
(`GenusFold.dimJ1Le`, modules `Genus.DimJac`, `Genus.GenusBound`, `Genus.LocalDer`). This module
brings it into namespace `HDec` (copied from `scratch/genus-route/Fold.lean`; `t34Le` is proved
directly from `GenusFold.dimJ1Le`, since `HDec.PkgI3.AbVar` and `HDec.LeafModCurves.IsJ1` are the
kernel's constants by the dedupe, and `toAbVarK4`/`isJacobianK_of5` are declared only after TailD):

* `HSyn.DimJ1Le5`: the statement, as Fold.lean;
* `HSyn.t34Le : DimJ1Le5` (proved, no hypothesis);
* `HSyn.dim_J1_le_of5`: drop-in for `LeafModCurves.dim_J1_le t.t34` (TailD, E2);
* `HSyn.G0Split.javanpeykarJ1_of_le`: drop-in for `javanpeykarJ1 hR18 hBelyi t.t34` (TailD, G18). -/

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`DimJ1Le` on the OneProof names** (`PkgI3.AbVar`, `LeafModCurves.IsJ1` of `HDec`): the conclusion
of `LeafModCurves.dim_J1_le`, the only use of `t34`. -/
def DimJ1Le5 : Prop :=
  ∀ (N : ℕ) (J : PkgI3.AbVar ℚ), 0 < N → LeafModCurves.IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2

/-- **The replacement for `t34`, with no hypothesis (proved)**: `dim J₁(N) ≤ N²`, from
`GenusFold.dimJ1Le` (dimjac-glue's `dimJacobianEqGenus` and genus-route's elementary genus bound). -/
theorem t34Le : DimJ1Le5 := GenusFold.dimJ1Le

/-- `t34` implies `DimJ1Le5` (so the replacement is weaker than the old field). -/
theorem dimJ1Le5_of_t34 (h : LeafModCurves.DimJ1Genus) : DimJ1Le5 :=
  fun N J hN hJ => LeafModCurves.dim_J1_le h N hN J hJ

/-- **Drop-in for `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1`** (TailD, E2). -/
theorem dim_J1_le_of5 (h : DimJ1Le5) (N : ℕ) (hN : 0 < N) (J : PkgI3.AbVar ℚ)
    (hJ : LeafModCurves.IsJ1 N J) : ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2 :=
  h N J hN hJ

/-- The type of `dim_J1_le_of5 h` is the type of `LeafModCurves.dim_J1_le t34` (checked by `example`). -/
example (h : DimJ1Le5) (t34 : LeafModCurves.DimJ1Genus) (N : ℕ) (hN : 0 < N) (J : PkgI3.AbVar ℚ)
    (hJ : LeafModCurves.IsJ1 N J) :
    (∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2) ∧ (∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2) :=
  ⟨dim_J1_le_of5 h N hN J hJ, LeafModCurves.dim_J1_le t34 N hN J hJ⟩

namespace G0Split

/-- **Drop-in for `javanpeykarJ1 hR18 hBelyi t.t34`** (TailD, G18): `javanpeykarJ1` (LPrefix) with `t34`
replaced by `DimJ1Le5`; the proof is `javanpeykarJ1`'s with `LeafModCurves.dim_J1_le hT34 N hN J hJ`
replaced by `h N J hN hJ` (genus-route, `Fold.lean`). -/
theorem javanpeykarJ1_of_le (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel)
    (h : DimJ1Le5) : JavanpeykarJ1 := by
  intro N hN J hJ g hg hg1 x hx
  obtain ⟨X, _, _, P₀, aj, hJac, t, ht, d, hd, hd0, hdN⟩ := hB N hN J hJ
  have h' := hR18 ℚ X P₀ J aj hJac g hg hg1 t ht d hd hd0
  rw [hx] at h'
  have hxb : x ≤ ZInQ.LeafPush2.javanpeykarBound g d := EReal.coe_le_coe_iff.mp h'
  obtain ⟨g', hg', hgN⟩ := h N J hN hJ
  have hgg : g = g' := by
    have : (g : WithBot ℕ∞) = (g' : WithBot ℕ∞) := hg.symm.trans hg'
    exact_mod_cast this
  subst hgg
  have hgR : (g : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  have hdR : (d : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hdN
  calc x ≤ ZInQ.LeafPush2.javanpeykarBound g d := hxb
    _ = 13 * 10 ^ 6 * (g : ℝ) * (d : ℝ) ^ 5 := rfl
    _ ≤ 13 * 10 ^ 6 * ((N : ℝ) ^ 2) * ((N : ℝ) ^ 2) ^ 5 := by gcongr
    _ = 13000000 * (N : ℝ) ^ 12 := by ring

/-- `javanpeykarJ1_of_le` agrees with the original on `t34`. -/
example (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel) (t34 : LeafModCurves.DimJ1Genus) :
    javanpeykarJ1_of_le hR18 hB (dimJ1Le5_of_t34 t34) = javanpeykarJ1 hR18 hB t34 := rfl

end G0Split

end HSyn

end HDec
