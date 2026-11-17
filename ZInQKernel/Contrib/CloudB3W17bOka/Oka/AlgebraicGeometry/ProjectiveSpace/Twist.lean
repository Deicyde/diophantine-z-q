/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.ProjectiveSpace.Basic
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.Modules.CocycleTwist

/-!
# Twisting sheaves on projective space

For a sheaf of modules `F` on `ℙ(n; R)` and `m : ℤ`, the **twist** `F(m) = F ⊗ O(m)` is the twist
of `F` (`Scheme.Modules.twist`) by the `m`-th power of the standard cocycle `gᵢⱼ = Xⱼ / Xᵢ` on
the standard cover `Uᵢ = D₊(Xᵢ)`: its sections over `V` are the families `sᵢ ∈ Γ(F, V ∩ Uᵢ)` with
`sᵢ = (Xⱼ / Xᵢ)ᵐ • sⱼ` on `V ∩ Uᵢ ∩ Uⱼ`. On the chart `Uᵢ`, a section `s` of `O(m)` corresponds
to `Xᵢᵐ · sᵢ` (see `Oka/AlgebraicGeometry/ProjectiveSpace/TwistSections.lean`).

## Main definitions and results

- `ProjectiveSpace.xDiv i j`: the section `Xⱼ / Xᵢ` of `𝒪` over `Uᵢ`; `xDiv_mul_xDiv`.
- `ProjectiveSpace.cocycle n R`: the standard cocycle `(Xⱼ / Xᵢ)`, the transition functions of
  `O(1)`.
- `ProjectiveSpace.twist F m`, `ProjectiveSpace.twistFunctor n R m`, and
  `ProjectiveSpace.twistingSheaf n R m = O(m)`.
- `ProjectiveSpace.twistRestrictIso`: `F(m)|_{Uᵢ} ≅ F|_{Uᵢ}` (natural in `F`:
  `ProjectiveSpace.twistFunctorRestrictIso`).
- `ProjectiveSpace.twistZeroIso`: `F(0) ≅ F`; `ProjectiveSpace.twistTwistIso`:
  `(F(m))(k) ≅ F(m + k)`.
- `ProjectiveSpace.twistEquivalence`: `F ↦ F(m)` is an autoequivalence (inverse `F ↦ F(-m)`), so
  it preserves all limits and colimits and is additive, in particular exact.
- `ProjectiveSpace.mulX F m l : F(m) ⟶ F(m + 1)`: multiplication by the variable `Xₗ` (by
  `Xₗ / Xᵢ` on `Uᵢ`); `mono_mulX_twistingSheaf`: it is a monomorphism `O(m) ⟶ O(m + 1)`.
-/

open CategoryTheory Limits MvPolynomial HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace

universe u

namespace AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R]



/-- The section `Xⱼ / Xᵢ` of the structure sheaf over the chart `U i`. -/
noncomputable def xDiv (i j : Fin (n + 1)) : Γ((AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)), U n R i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) R) (X i) (awayXDiv R i j)

lemma xDiv_self (i : Fin (n + 1)) : xDiv (R := R) i i = 1 := by
  rw [xDiv, awayXDiv_self, map_one]
  rfl

lemma xDiv_res (i j : Fin (n + 1)) {m : ℕ} {g x : MvPolynomial (Fin (n + 1)) R} (hg : g ∈ (homogeneousSubmodule (Fin (n + 1)) R) m)
    (hx : x = X i * g) :
    TopCat.Presheaf.restrictOpen (xDiv i j) (Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) x)
      (Proj.basicOpen_mono _ _ _ ⟨g, hx⟩) =
      Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) R) x (awayMap (homogeneousSubmodule (Fin (n + 1)) R) hg hx (awayXDiv R i j)) := by
  have := congr($(Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (n + 1)) R) hg hx) (awayXDiv R i j))
  exact this.symm

/-- `(Xⱼ / Xᵢ) (Xₗ / Xⱼ) = Xₗ / Xᵢ` on `Uᵢ ∩ Uⱼ`. -/
lemma xDiv_mul_xDiv (i j l : Fin (n + 1)) (W : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Opens) (hW : W ≤ U n R i ⊓ U n R j) :
    ((TopCat.Presheaf.restrictOpen (xDiv i j) (W) (by order))) * ((TopCat.Presheaf.restrictOpen (xDiv j l) (W) (by order))) = ((TopCat.Presheaf.restrictOpen (xDiv i l) (W) (by order))) := by
  suffices ((TopCat.Presheaf.restrictOpen (xDiv i j) ((U n R i ⊓ U n R j)) (by order))) * ((TopCat.Presheaf.restrictOpen (xDiv j l) ((U n R i ⊓ U n R j)) (by order))) =
      ((TopCat.Presheaf.restrictOpen (xDiv i l) ((U n R i ⊓ U n R j)) (by order))) by
    have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W hW) this
    simpa only [ores_mul, ores_res] using this
  have hT : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) (X i * X j) = U n R i ⊓ U n R j := Proj.basicOpen_mul _ _ _
  refine ores_injective_of_le hT.le hT.ge ?_
  have h1 := cloudB3W17bOka_X_mem_homogeneousSubmodule_one (R := R) j
  have h2 := cloudB3W17bOka_X_mem_homogeneousSubmodule_one (R := R) i
  simp only [ores_mul, ores_res]
  rw [xDiv_res i j h1 rfl, xDiv_res j l h2 (mul_comm _ _), xDiv_res i l h1 rfl, ← map_mul]
  congr 1
  apply val_injective
  simp only [awayXDiv, awayMap_mk, val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]; ring⟩

variable (n R) in
/-- The **standard cocycle** `gᵢⱼ = Xⱼ / Xᵢ` on `Uᵢ ∩ Uⱼ`, the transition functions of `O(1)`. -/
noncomputable def cocycle : Cocycle (U n R) where
  g i j := (TopCat.Presheaf.restrictOpen (xDiv i j) ((U n R i ⊓ U n R j)) (by order))
  self i := by rw [xDiv_self, ores_one]
  mul i j k := by
    simp only [ores_res]
    exact xDiv_mul_xDiv i j k _ (by order)

lemma cocycle_g (i j : Fin (n + 1)) :
    (cocycle n R).g i j = (TopCat.Presheaf.restrictOpen (xDiv i j) ((U n R i ⊓ U n R j)) (by order)) :=
  rfl

/-- The twist `F(m) = F ⊗ O(m)` of a sheaf of modules on `ℙ(n; R)`: sections over `V` are the
families `sᵢ ∈ Γ(F, V ∩ Uᵢ)` with `sᵢ = (Xⱼ / Xᵢ)ᵐ • sⱼ` on `V ∩ Uᵢ ∩ Uⱼ`. -/
noncomputable abbrev twist (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) (m : ℤ) : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules :=
  Scheme.Modules.twist F (cocycle n R ^ m)

variable (n R) in
/-- The functor `F ↦ F(m)`. -/
noncomputable abbrev twistFunctor (m : ℤ) : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules ⥤ (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules :=
  Scheme.Modules.twistFunctor (cocycle n R ^ m)

@[simp]
lemma twistFunctor_obj (m : ℤ) (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) : (twistFunctor n R m).obj F = twist F m :=
  rfl

variable (n R) in
/-- The **twisting sheaf** `O(m)` on `ℙ(n; R)`. -/
noncomputable abbrev twistingSheaf (m : ℤ) : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules :=
  twist (SheafOfModules.unit _) m

instance (m : ℤ) : (twistFunctor n R m).Additive :=
  inferInstanceAs (Scheme.Modules.twistFunctor _).Additive

/-- `F(m)` is trivial on the chart `Uᵢ`: `F(m)|_{Uᵢ} ≅ F|_{Uᵢ}`. -/
noncomputable def twistRestrictIso (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) (m : ℤ) (i : Fin (n + 1)) :
    (twist F m).restrict (U n R i).ι ≅ F.restrict (U n R i).ι :=
  Scheme.Modules.twistRestrictIso F _ i

variable (n R) in
/-- The trivialisation `F(m)|_{Uᵢ} ≅ F|_{Uᵢ}`, natural in `F`. -/
noncomputable def twistFunctorRestrictIso (m : ℤ) (i : Fin (n + 1)) :
    twistFunctor n R m ⋙ restrictFunctor (U n R i).ι ≅ restrictFunctor (U n R i).ι :=
  Scheme.Modules.twistFunctorRestrictIso _ i

/-- `F(0) ≅ F`. -/
noncomputable def twistZeroIso (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) : twist F 0 ≅ F :=
  (twistFunctorCongr (zpow_zero (cocycle n R))).app F ≪≫ twistOneIso F (iSup_U n R)

/-- `(F(m))(k) ≅ F(m + k)`. -/
noncomputable def twistTwistIso (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) (m k : ℤ) :
    twist (twist F m) k ≅ twist F (m + k) :=
  Scheme.Modules.twistTwistIso F _ _ ≪≫
    (twistFunctorCongr (zpow_add (cocycle n R) m k).symm).app F

variable (n R) in
/-- `F ↦ F(m)` is an autoequivalence of the category of sheaves of modules on `ℙ(n; R)`, with
inverse `F ↦ F(-m)`. -/
noncomputable def twistEquivalence (m : ℤ) : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules ≌ (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules :=
  Scheme.Modules.twistEquivalence (cocycle n R ^ m) (iSup_U n R)

@[simp]
lemma twistEquivalence_functor (m : ℤ) : (twistEquivalence n R m).functor = twistFunctor n R m :=
  rfl

instance (m : ℤ) : (twistFunctor n R m).IsEquivalence :=
  (twistEquivalence n R m).isEquivalence_functor

/-- **Twisting is exact**: it preserves all limits. -/
instance (m : ℤ) : PreservesLimits (twistFunctor n R m) := inferInstance

/-- **Twisting is exact**: it preserves all colimits. -/
instance (m : ℤ) : PreservesColimits (twistFunctor n R m) := inferInstance

section MulX

/-- `Xₗ / Xᵢ = (Xⱼ / Xᵢ) (Xₗ / Xⱼ)` on `Uᵢ ∩ Uⱼ`: the `xDiv · l` form a global section of `O(1)`. -/
lemma xDiv_compat (l i j : Fin (n + 1)) :
    ((TopCat.Presheaf.restrictOpen (xDiv i l) ((U n R i ⊓ U n R j)) (by order))) =
      (cocycle n R).g i j * ((TopCat.Presheaf.restrictOpen (xDiv j l) ((U n R i ⊓ U n R j)) (by order))) :=
  (xDiv_mul_xDiv i j l _ le_rfl).symm

/-- **Multiplication by the variable `Xₗ`**, `F(m) ⟶ F(m + 1)`: on the chart `Uᵢ` it is
multiplication by `Xₗ / Xᵢ`. -/
noncomputable def mulX (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) (m : ℤ) (l : Fin (n + 1)) :
    twist F m ⟶ twist F (m + 1) :=
  twistMulSection F _ (cocycle n R) (fun i ↦ xDiv i l) (xDiv_compat l) ≫
    ((twistFunctorCongr (zpow_add_one (cocycle n R) m).symm).app F).hom

@[simp]
lemma twistComp_mulX_app (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) (m : ℤ) (l : Fin (n + 1)) (V : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Opens)
    (s : Γ(twist F m, V)) (i : Fin (n + 1)) :
    twistComp ((mulX F m l).app V s) i = ((TopCat.Presheaf.restrictOpen (xDiv i l) ((V ⊓ U n R i)) (by order))) • twistComp s i :=
  rfl

lemma mulX_app_injective (F : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Modules) (m : ℤ) (l : Fin (n + 1)) (V : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Opens)
    (hF : ∀ i (x y : Γ(F, V ⊓ U n R i)),
      ((TopCat.Presheaf.restrictOpen (xDiv i l) ((V ⊓ U n R i)) (by order))) • x = ((TopCat.Presheaf.restrictOpen (xDiv i l) ((V ⊓ U n R i)) (by order))) • y → x = y) :
    Function.Injective ((mulX F m l).app V) := fun s t h ↦
  twist_ext fun i ↦ hF i _ _ (by
    rw [← twistComp_mulX_app, ← twistComp_mulX_app, h])

lemma xDiv_mem_nonZeroDivisors (i l : Fin (n + 1)) :
    xDiv (R := R) i l ∈ nonZeroDivisors Γ((AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)), U n R i) := by
  let e := (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin (n + 1)) R) (X i) (cloudB3W17bOka_X_mem_homogeneousSubmodule_one i)
    Nat.one_pos).commRingCatIsoToRingEquiv
  have h : awayXDiv R i l ∈ nonZeroDivisors (Away (homogeneousSubmodule (Fin (n + 1)) R) (X i)) := by
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i l
    · rw [awayXDiv_self]
      exact one_mem _
    · rw [← toAwayX_X, ← awayXEquiv_apply, ← MulEquivClass.map_nonZeroDivisors (awayXEquiv R i)]
      exact Submonoid.mem_map_of_mem _ (isRegular_iff_mem_nonZeroDivisors.mp isRegular_X)
  have := Submonoid.mem_map_of_mem e h
  rw [MulEquivClass.map_nonZeroDivisors] at this
  exact this

lemma mulX_twistingSheaf_app_injective (m : ℤ) (l : Fin (n + 1)) (V : (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).Opens) :
    Function.Injective ((mulX (SheafOfModules.unit _) m l).app V) :=
  mulX_app_injective _ m l V fun i _ _ hxy ↦
    (mul_cancel_left_mem_nonZeroDivisors ((isAffineOpen_U i).restrictOpen_mem_nonZeroDivisors
      (xDiv_mem_nonZeroDivisors i l) (inf_le_right : V ⊓ U n R i ≤ U n R i))).mp hxy

/-- **Multiplication by `Xₗ` is injective on twisting sheaves**: `O(m) ⟶ O(m + 1)` is a
monomorphism. -/
instance mono_mulX_twistingSheaf (m : ℤ) (l : Fin (n + 1)) :
    Mono (mulX (SheafOfModules.unit (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (R)).ringCatSheaf) m l) :=
  mono_of_injective _ (mulX_twistingSheaf_app_injective m l)

end MulX

end AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace
