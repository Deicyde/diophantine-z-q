/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section plan GM11 (Step 3), the sub-results that are PROVED here from held
W07/Mathlib bodies plus the explicitly named sub-gaps of `Step3Gaps.lean`.
SOURCE ONLY, UNCOMPILED. Native HELD. No kernel/ABI/admission grade is claimed.

* `exists_subsingleton_H_tensorPow_of_presentation` (Serre vanishing on a field from a FINITE
  presentation), from (G1) + held W07 `exists_subsingleton_H_tensor_pullback_twist_of_isFinite`
  (Cohomology/SerreVanishing.lean, sha256 cd712da0…5691) + W07 `nonempty_tensorObj_twist_iso`.
* `surjective_pullbackSection_of_subsingleton_H_one` (sections lift from the closed fibre over a
  DVR), from (G3) + held W07 long exact sequence (Cohomology/LongExact.lean, 02150bc8…), W07
  `hasFiniteH_of_isProper` (Cohomology/Proper.lean, 2af41186…), W07 affine pushforward comparison,
  and Mathlib Nakayama.
* `eq_top_of_closedFibre`, `framesNear_of_closedFibre`: over a local base, an open containing the
  closed fibre of a universally closed map is everything (closed image + specialization).
* `isFinite_toProj_of_quasiFiniteAt_closedFibre`: quasi-finite over the closed point ⇒ finite
  (Mathlib quasi-finite locus, `IsProper.of_comp`, `IsFinite.of_isProper_of_locallyQuasiFinite`).
No relative ampleness, vanishing, presentation, model or Fact is assumed; powers are native W07.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Gaps
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.NativePower
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.SerreVanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.LongExact
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Affine.Pushforward
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Tensor
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-! ### Native power bookkeeping -/

/-- Native W07 powers of isomorphic modules are isomorphic (actual tensor of the given iso). -/
noncomputable def tensorPowIsoOfIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    (n : ℕ) → L.tensorPow n ≅ L'.tensorPow n
  | 0 => Iso.refl (𝟙_ X.Modules)
  | n + 1 => e ⊗ᵢ tensorPowIsoOfIso e n

/-- `𝒪(1)^{⊗(n+1)} ≅ 𝒪(n+1)` for the W07 twist on `Proj R[T_c]`, `c : ULift (Fin (N+1))`,
from W07 `nonempty_tensorObj_twist_iso`. -/
theorem nonempty_twistOne_tensorPow_succ (R : Type u) [CommRing R] (N : ℕ) :
    ∀ n : ℕ, Nonempty
      ((Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R) 1).tensorPow
          (n + 1) ≅
        Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R)
          ((n + 1 : ℕ) : ℤ))
  | 0 => ⟨(ρ_ _) ≪≫ eqToIso (congrArg
      (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R))
      (by norm_num))⟩
  | n + 1 => by
      obtain ⟨e⟩ := nonempty_twistOne_tensorPow_succ R N n
      obtain ⟨t⟩ := Proj.nonempty_tensorObj_twist_iso
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R)
        (Proj.exists_mem_basicOpen_homogeneousSubmodule.{u, u} (ULift.{u} (Fin (N + 1))) R)
        1 ((n + 1 : ℕ) : ℤ)
      exact ⟨(Iso.refl _ ⊗ᵢ e) ≪≫ t ≪≫ eqToIso (congrArg
        (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R))
        (by push_cast; ring))⟩

/-! ### (S1) Serre vanishing from a finite presentation over a field -/

/-- **(S1)** If `L` has a presentation with FINITE map over a field, all positive-degree native
cohomology of all sufficiently large native powers of `L` vanishes. Uses (G1) only to identify
`L` with the pullback of `𝒪(1)`; the vanishing itself is the held W07 theorem. -/
theorem exists_subsingleton_H_tensorPow_of_presentation (hG1 : PresentationTwistIso.{u})
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    {L : X.Modules} {N : ℕ} (𝔓 : Pres L f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ, 0 < q → Subsingleton ((L.tensorPow n).H q) := by
  obtain ⟨φ, hφ, ⟨e⟩⟩ := hG1 𝔓
  haveI : IsFinite φ := hφ hfin
  obtain ⟨bound, hvan⟩ := Scheme.Modules.exists_subsingleton_H_tensor_pullback_twist_of_isFinite
    (ULift.{u} (Fin (N + 1))) k φ (𝟙_ X.Modules)
  refine ⟨bound.toNat + 1, fun n hn q hq => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb : bound ≤ ((m + 1 : ℕ) : ℤ) := by
    have := Int.self_le_toNat bound
    omega
  haveI := hvan ((m + 1 : ℕ) : ℤ) hb q hq
  obtain ⟨t⟩ := nonempty_twistOne_tensorPow_succ k N m
  let iso : L.tensorPow (m + 1) ≅ 𝟙_ X.Modules ⊗ (Scheme.Modules.pullback φ).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)
        ((m + 1 : ℕ) : ℤ)) :=
    tensorPowIsoOfIso e (m + 1) ≪≫ (pullbackTensorPowIso φ _ (m + 1)).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso t ≪≫ (λ_ _).symm
  exact (Scheme.Modules.H.mapLinearEquiv iso q).toEquiv.subsingleton

/-! ### (S2) Lifting sections from the closed fibre over a DVR -/

/-- Cohomology vanishing passes to the pushforward along an affine morphism (held W07 affine
pushforward comparison, used exactly as in W07 SerreVanishing). -/
theorem subsingleton_H_pushforward_of_isAffineHom {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsAffineHom i] (G : Y.Modules) [G.IsQuasicoherent] (q : ℕ) [Subsingleton (G.H q)] :
    Subsingleton (((Scheme.Modules.pushforward i).obj G).H q) := by
  obtain ⟨comparison⟩ := Scheme.Modules.nonempty_functorH_iso_pushforwardAb_of_isAffineHom i q
  let e : G.H q ≃+ ((Scheme.Modules.pushforward i).obj G).H q :=
    (comparison.app ⟨(SheafOfModules.toSheaf Y.ringCatSheaf).obj G,
      Scheme.Modules.cechAcyclicOnAffines_of_isQuasicoherent G⟩).addCommGroupIsoToAddEquiv
  exact e.symm.injective.subsingleton

/-- The closed-fibre inclusion over a local base is a closed immersion, hence affine. -/
theorem isClosedImmersion_fiberι_closedPoint {C : Type u} [CommRing C] [IsLocalRing C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of C)) :
    IsClosedImmersion (f.fiberι (IsLocalRing.closedPoint C)) := by
  haveI : IsClosedImmersion
      ((Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C)) :=
    isClosed_singleton_iff_isClosedImmersion.1 (IsLocalRing.isClosed_singleton_closedPoint C)
  show IsClosedImmersion (pullback.fst f
    ((Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C)))
  infer_instance

/-- **(S2)** Over a DVR, for `X` proper and flat and `F` invertible: if `H¹` of the literal
closed-fibre restriction vanishes, every closed-fibre global section is the literal pullback of
a global section of `F`. Proof: (G3) gives `0 → F --ϖ--> F → i_* i^*F → 0`; `H¹(i_* i^*F) = 0`
(affine pushforward), so `ϖ` is onto on `H¹(F)`, which is finite over `C` (W07 proper finiteness),
hence `H¹(F) = 0` by Nakayama; then `H⁰(F) → H⁰(i_* i^*F)` is onto by the long exact sequence,
and `H⁰` is global sections compatibly with the literal unit map. -/
theorem surjective_pullbackSection_of_subsingleton_H_one (hG3 : UniformizerSequence.{u})
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of C)) [IsProper f] [Flat f]
    (F : X.Modules) [F.IsInvertible]
    (h1 : Subsingleton
      (((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint C))).obj F).H 1)) :
    Function.Surjective
      (pullbackSection (M := F) (f.fiberι (IsLocalRing.closedPoint C))) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  obtain ⟨w, hS⟩ := hG3 f F ϖ hϖ
  let i := f.fiberι (IsLocalRing.closedPoint C)
  let a : Γ(X, ⊤) := f.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ϖ)
  let S : ShortComplex X.Modules := ShortComplex.mk _ _ w
  haveI : IsClosedImmersion i := isClosedImmersion_fiberι_closedPoint f
  haveI := h1
  -- (1) `H¹(i_* i^* F) = 0`.
  have h3 : Subsingleton (S.X₃.H 1) :=
    subsingleton_H_pushforward_of_isAffineHom i ((Scheme.Modules.pullback i).obj F) 1
  -- (2) multiplication by `a` is onto on `H¹(F)`.
  have hsurj : ∀ z : F.H 1, ∃ z' : F.H 1, a • z' = z := by
    intro z
    have hz : z ∈ (Scheme.Modules.H.map S.g 1).ker :=
      (AddMonoidHom.mem_ker).2 (@Subsingleton.elim _ h3 _ _)
    rw [Scheme.Modules.H.ker_map_g_eq_range_map_f hS 1] at hz
    obtain ⟨z', hz'⟩ := (AddMonoidHom.mem_range).1 hz
    exact ⟨z', (Scheme.Modules.smul_H_eq_map F 1 a z').trans hz'⟩
  -- (3) Nakayama over the local ring `C`: `H¹(F) = 0`.
  letI : Module C (F.H 1) := Scheme.Modules.moduleHOfSpec f F 1
  haveI : Module.Finite C (F.H 1) := Scheme.Modules.hasFiniteH_of_isProper f F 1
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal C :=
    (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hle : (⊤ : Submodule C (F.H 1)) ≤ IsLocalRing.maximalIdeal C • ⊤ := by
    intro z _
    obtain ⟨z', hz'⟩ := hsurj z
    have hsmul : (ϖ • z' : F.H 1) = z := hz'
    rw [← hsmul]
    exact Submodule.smul_mem_smul hϖm Submodule.mem_top
  have hbot : (⊤ : Submodule C (F.H 1)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal C) ⊤
      Module.Finite.fg_top hle (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hF1 : Subsingleton (F.H 1) := ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule C (F.H 1)) := hbot ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule C (F.H 1)) := hbot ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]⟩
  -- (4) `H⁰(F) → H⁰(i_* i^* F)` is onto.
  have h0 : Function.Surjective (Scheme.Modules.H.map S.g 0) := by
    intro x
    have hx : x ∈ (Scheme.Modules.H.δ hS 0).ker :=
      (AddMonoidHom.mem_ker).2 (@Subsingleton.elim _ hF1 _ _)
    rw [Scheme.Modules.H.ker_δ_eq_range_map_g hS 0] at hx
    exact (AddMonoidHom.mem_range).1 hx
  -- (5) translate `H⁰` to global sections along the literal unit map.
  intro τ
  obtain ⟨y, hy⟩ := h0 ((Scheme.Modules.H.zeroLinearEquiv S.X₃).symm (show Γ(S.X₃, ⊤) from τ))
  refine ⟨Scheme.Modules.H.zeroLinearEquiv F y, ?_⟩
  have hnat : (S.g.app ⊤) (Scheme.Modules.H.zeroLinearEquiv F y) =
      Scheme.Modules.H.zeroLinearEquiv S.X₃ (Scheme.Modules.H.map S.g 0 y) :=
    Sheaf.H.equiv₀_naturality (hT := CategoryTheory.Limits.isTerminalTop)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g) y
  change (S.g.app ⊤) (Scheme.Modules.H.zeroLinearEquiv F y) = τ
  rw [hnat, hy]
  exact (Scheme.Modules.H.zeroLinearEquiv S.X₃).apply_symm_apply _

/-! ### (S3) Closed-fibre conditions spread over a local base -/

/-- Over a local base, an open subset containing the whole closed fibre of a universally closed
morphism is everything: its complement has closed image, every point of the base specializes to
the closed point, and the closed point has no preimage outside the open. -/
theorem eq_top_of_closedFibre {C : Type u} [CommRing C] [IsLocalRing C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of C)) [UniversallyClosed f] (G : X.Opens)
    (hG : ∀ x : X, f.base x = IsLocalRing.closedPoint C → x ∈ G) : G = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  by_contra hx
  have hZ : IsClosed (f.base '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hspec : (f.base x : PrimeSpectrum C) ⤳ IsLocalRing.closedPoint C :=
    IsLocalRing.specializes_closedPoint _
  obtain ⟨y, hy, hfy⟩ : IsLocalRing.closedPoint C ∈ f.base '' (G : Set X)ᶜ :=
    hspec.mem_closed hZ ⟨x, hx, rfl⟩
  exact hy (hG y hfy)

/-- **(S3)** If at every point of the closed fibre some member of a family of global sections
generates near that point, then this holds at every point. -/
theorem framesNear_of_closedFibre {C : Type u} [CommRing C] [IsLocalRing C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of C)) [UniversallyClosed f] (M : X.Modules) {ι : Type*}
    (σ : ι → Γ(M, ⊤))
    (h : ∀ x : X, f.base x = IsLocalRing.closedPoint C → ∃ j, FramesNear M (σ j) x) :
    ∀ x : X, ∃ j, FramesNear M (σ j) x := by
  let G : X.Opens := ⨆ p : (Σ j : ι, {U : X.Opens // ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) =>
        g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ j) : Γ(M, V))}), p.2.1
  have hG : ∀ x : X, x ∈ G ↔ ∃ j, FramesNear M (σ j) x := by
    intro x
    simp only [G, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨⟨j, U, hU⟩, hx⟩
      exact ⟨j, U, hx, hU⟩
    · rintro ⟨j, U, hx, hU⟩
      exact ⟨⟨j, U, hU⟩, hx⟩
  have htop : G = ⊤ := eq_top_of_closedFibre f G fun x hx => (hG x).2 (h x hx)
  intro x
  exact (hG x).1 (by rw [htop]; trivial)

/-! ### (S4) Finiteness from quasi-finiteness over the closed point -/

/-- **(S4)** For `X` proper over a local ring, the map of a presentation that is quasi-finite at
every point over the closed point is finite. -/
theorem isFinite_toProj_of_quasiFiniteAt_closedFibre {C : Type u} [CommRing C] [IsLocalRing C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of C)) [IsProper f] {M : X.Modules} {N : ℕ}
    (𝔔 : Pres M f N)
    (h : ∀ x : X, f.base x = IsLocalRing.closedPoint C → 𝔔.toProj.QuasiFiniteAt x) :
    IsFinite 𝔔.toProj := by
  haveI : IsProper (𝔔.toProj ≫ ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π C N) := by
    rw [𝔔.toProj_π]
    infer_instance
  haveI : LocallyOfFiniteType 𝔔.toProj := locallyOfFiniteType_of_comp 𝔔.toProj
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π C N)
  haveI : IsProper 𝔔.toProj :=
    IsProper.of_comp (f := 𝔔.toProj)
      (g := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π C N)
  have htop : 𝔔.toProj.quasiFiniteLocus = ⊤ :=
    eq_top_of_closedFibre f _ fun x hx => Scheme.Hom.mem_quasiFiniteLocus.2 (h x hx)
  haveI : LocallyQuasiFinite 𝔔.toProj := 𝔔.toProj.quasiFiniteLocus_eq_top_iff.1 htop
  exact IsFinite.of_isProper_of_locallyQuasiFinite 𝔔.toProj

end ZInQ.Contrib.CloudR2NOS.ClosedSection
