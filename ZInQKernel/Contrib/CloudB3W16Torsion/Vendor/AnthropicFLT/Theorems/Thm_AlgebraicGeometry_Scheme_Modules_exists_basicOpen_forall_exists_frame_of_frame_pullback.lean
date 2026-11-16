/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤))
    (K : Type u) [Field K] [Algebra R K] (𝔭 : PrimeSpectrum R) (h𝔭 : RingHom.ker (algebraMap R K) = 𝔭.asIdeal)
    (hgen : ∀ z : ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∃ (i : ι) (U' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens), z ∈ U' ∧
        ∀ V' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens, V' ≤ U' →
          Function.Bijective fun g : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))), V') =>
            g • (((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M).presheaf.map
                  (homOfLE (le_top : V' ≤ ⊤)).op
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app M).app ⊤) (m i)) :
              Γ((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, V'))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.solution
