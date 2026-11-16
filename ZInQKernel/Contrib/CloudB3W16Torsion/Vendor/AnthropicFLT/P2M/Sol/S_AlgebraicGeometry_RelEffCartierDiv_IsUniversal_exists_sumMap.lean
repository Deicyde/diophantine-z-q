/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap.AlgebraicGeometry

namespace AlgebraicGeometry
export AlgebraicGeometry (Surjective Scheme.Hom.finrank_comp_left_of_isIso SmoothOfRelativeDimension Scheme.Hom IsFinite Scheme Smooth Flat IsSeparated LocallyOfFinitePresentation fibrePowOver fibrePowOver.proj fibrePowOver.toBase fibrePowOver.proj_comp prodKerGraph fibrePowOver.tautIdeal RelEffCartierDiv mapOnProdOver RelEffCartierDiv.I RelEffCartierDiv.IsUniversal RelEffCartierDiv.exists_split RelEffCartierDiv.exists_I_eq_prodKerGraph prodKerGraph_comap_mapOnProdOver)
open AlgebraicGeometry

theorem prodKerGraph_congr {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : Fin r → (T ⟶ 𝒞)} (h : a = a') (ha : ∀ i, a i ≫ f = g) (ha' : ∀ i, a' i ≫ f = g) :
    prodKerGraph f a ha = prodKerGraph f a' ha' := by
  subst h; rfl

namespace RelEffCartierDiv
export AlgebraicGeometry.RelEffCartierDiv (pullbackAlong pullbackAlong_comp I IsUniversal exists_split exists_I_eq_prodKerGraph)
namespace IsUniversal
export AlgebraicGeometry.RelEffCartierDiv.IsUniversal (lift lift_comp pullsBackOver_lift hom_ext)
open AlgebraicGeometry.RelEffCartierDiv.IsUniversal
open AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}

set_option backward.isDefEq.respectTransparency false in

private theorem _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_sumMap_aux (hU : Duniv.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      ∀ x : Y, σ.finrank x = r.factorial := by

  obtain ⟨Dt, hDt⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := f)
    (fibrePowOver.proj f r) (fibrePowOver.proj_comp f r)
  set σ : fibrePowOver f r ⟶ Y := hU.lift Dt with hσdef
  have hσ : σ ≫ y = fibrePowOver.toBase f r := hU.lift_comp Dt
  have hσI : Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r :=
    (hU.pullsBackOver_lift Dt).trans hDt
  clear_value σ

  obtain ⟨P, gP, p, hp, b, hb, hfin, hflat, hlfp, hsurj, hrank, hI, huniv⟩ :=
    RelEffCartierDiv.exists_split Duniv
  subst hp

  obtain ⟨u, ⟨hup, hub⟩, -⟩ := huniv (fibrePowOver.toBase f r) σ hσ (fibrePowOver.proj f r)
    (fibrePowOver.proj_comp f r) hσI

  let t : P ⟶ fibrePowOver f r := WidePullback.lift (p ≫ y) b hb
  have ht_proj : ∀ i, t ≫ fibrePowOver.proj f r i = b i := fun i => WidePullback.lift_π _ _ _ _ _
  have ht_base : t ≫ fibrePowOver.toBase f r = p ≫ y := WidePullback.lift_base _ _ _ _

  have hut : u ≫ t = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro i
      rw [Category.assoc, Category.id_comp]
      exact (ht_proj i).symm ▸ hub i
    · rw [Category.assoc, ht_base, Category.id_comp, ← Category.assoc, hup, hσ]

  have hty : (t ≫ σ) ≫ y = p ≫ y := by rw [Category.assoc, hσ, ht_base]
  have hcomp := congrArg RelEffCartierDiv.I (Duniv.pullbackAlong_comp σ hσ t ht_base)
  have htσ : p = t ≫ σ := by
    refine hU.hom_ext hty.symm ?_
    change (Duniv.pullbackAlong p rfl).I = (Duniv.pullbackAlong (t ≫ σ) hty).I
    rw [hI, ← hcomp]
    change prodKerGraph f b hb =
      ((Duniv.I.comap (mapOnProdOver f σ hσ)).comap (mapOnProdOver f t ht_base))
    rw [hσI, fibrePowOver.tautIdeal, prodKerGraph_comap_mapOnProdOver]
    exact prodKerGraph_congr f (funext fun i => (ht_proj i).symm) _ _

  have htu : t ≫ u = 𝟙 P := by
    obtain ⟨w, -, hwuniq⟩ := huniv (p ≫ y) p rfl b hb hI
    have h1 : t ≫ u = w :=
      hwuniq _ ⟨by rw [Category.assoc, hup, ← htσ], fun i => by rw [Category.assoc, hub, ht_proj]⟩
    have h2 : 𝟙 P = w := hwuniq _ ⟨Category.id_comp _, fun i => Category.id_comp _⟩
    exact h1.trans h2.symm
  have : IsIso u := ⟨⟨t, hut, htu⟩⟩
  subst hup
  exact ⟨u ≫ p, hσ, hσI, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by rw [Scheme.Hom.finrank_comp_left_of_isIso]; exact hrank x⟩
export AlgebraicGeometry.RelEffCartierDiv.IsUniversal (exists_sumMap_aux)
end RelEffCartierDiv.IsUniversal

end AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}
    (hU : Duniv.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      ∀ x : Y, σ.finrank x = r.factorial :=
  hU.exists_sumMap_aux
