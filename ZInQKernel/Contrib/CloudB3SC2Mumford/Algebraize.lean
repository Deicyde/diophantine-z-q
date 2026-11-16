import ZInQKernel.Contrib.CloudB3SC2Mumford.Interfaces
import ZInQKernel.Contrib.CloudB3SC2Mumford.Pipeline.Uniqueness
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete

/-!
# Algebraization of morphisms between proper schemes

The graph construction reduces morphism algebraization (EGA III₁ 5.4.1) to finite-cover
algebraization over the proper product. Formal closed-immersion and isomorphism detection
then identify the algebraized graph with the source. No projectivity, flatness, smoothness,
or group structure is required. The finite-cover and detection theorems are the proved,
revision-pinned Fermat-development modules named in the imports; their original notices
and compatibility modifications are retained in the vendor directory.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ZInQ.Contrib.CloudB3SC2Mumford

private abbrev baseTransition {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))

private theorem transition_isPullback {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    IsPullback (adicThickeningTransition f I n) (adicThickeningToBase f I n)
      (adicThickeningToBase f I (n + 1)) (baseTransition I n) := by
  refine IsPullback.of_right ?_ (adicThickeningTransition_toBase f I n)
    (IsPullback.of_hasPullback f (adicThickeningBase I (n + 1)))
  simpa only [adicThickeningTransition_ι, baseTransition, adicThickeningBase_succ_comp]
    using IsPullback.of_hasPullback f (adicThickeningBase I n)

section Graph

variable {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))

private abbrev productToBase : pullback f g ⟶ Spec (CommRingCat.of R) :=
  pullback.fst f g ≫ f

private def graphToProduct (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    adicThickening f I n ⟶ pullback f g :=
  pullback.lift (adicThickeningι f I n) (φ ≫ adicThickeningι g I n) (by
    calc
      adicThickeningι f I n ≫ f =
          adicThickeningToBase f I n ≫ adicThickeningBase I n := adicThickeningι_comp f I n
      _ = φ ≫ adicThickeningToBase g I n ≫ adicThickeningBase I n := by
        rw [← Category.assoc, hφ]
      _ = (φ ≫ adicThickeningι g I n) ≫ g := by
        rw [Category.assoc, adicThickeningι_comp])

private def formalGraph (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    adicThickening f I n ⟶ adicThickening (productToBase f g) I n :=
  pullback.lift (graphToProduct I f g n φ hφ) (adicThickeningToBase f I n) (by
    simp only [productToBase, graphToProduct, ← Category.assoc, pullback.lift_fst]
    exact adicThickeningι_comp f I n)

private theorem formalGraph_ι (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    formalGraph I f g n φ hφ ≫ adicThickeningι (productToBase f g) I n =
      graphToProduct I f g n φ hφ :=
  pullback.lift_fst _ _ _

private theorem formalGraph_toBase (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    formalGraph I f g n φ hφ ≫ adicThickeningToBase (productToBase f g) I n =
      adicThickeningToBase f I n :=
  pullback.lift_snd _ _ _

private theorem formalGraph_ι_fst (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    formalGraph I f g n φ hφ ≫ adicThickeningι (productToBase f g) I n ≫
      pullback.fst f g = adicThickeningι f I n := by
  rw [← Category.assoc, formalGraph_ι]
  exact pullback.lift_fst _ _ _

private theorem formalGraph_ι_snd (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    formalGraph I f g n φ hφ ≫ adicThickeningι (productToBase f g) I n ≫
      pullback.snd f g = φ ≫ adicThickeningι g I n := by
  rw [← Category.assoc, formalGraph_ι]
  exact pullback.lift_snd _ _ _

private def formalProjection (n : ℕ) :
    adicThickening (productToBase f g) I n ⟶ adicThickening f I n :=
  pullback.lift (adicThickeningι (productToBase f g) I n ≫ pullback.fst f g)
    (adicThickeningToBase (productToBase f g) I n) (by
      rw [Category.assoc]
      exact adicThickeningι_comp (productToBase f g) I n)

private theorem formalGraph_projection (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    formalGraph I f g n φ hφ ≫ formalProjection I f g n = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [formalProjection, Category.assoc, pullback.lift_fst, Category.id_comp]
    exact formalGraph_ι_fst I f g n φ hφ
  · simp only [formalProjection, Category.assoc, pullback.lift_snd, Category.id_comp]
    exact formalGraph_toBase I f g n φ hφ

private theorem formalGraph_isClosedImmersion [IsProper f] [IsProper g] (n : ℕ)
    (φ : adicThickening f I n ⟶ adicThickening g I n)
    (hφ : φ ≫ adicThickeningToBase g I n = adicThickeningToBase f I n) :
    IsClosedImmersion (formalGraph I f g n φ hφ) := by
  haveI : IsSeparated (formalProjection I f g n ≫ adicThickeningToBase f I n) := by
    simp only [formalProjection, adicThickeningToBase, pullback.lift_snd]
    infer_instance
  haveI : IsSeparated (formalProjection I f g n) :=
    IsSeparated.of_comp _ (adicThickeningToBase f I n)
  haveI : IsClosedImmersion (formalGraph I f g n φ hφ ≫ formalProjection I f g n) := by
    rw [formalGraph_projection]
    infer_instance
  exact IsClosedImmersion.of_comp _ (formalProjection I f g n)

private theorem formalGraph_transition
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) =
      φ n ≫ adicThickeningTransition g I n) (n : ℕ) :
    adicThickeningTransition f I n ≫ formalGraph I f g (n + 1) (φ (n + 1)) (hφ (n + 1)) =
      formalGraph I f g n (φ n) (hφ n) ≫
        adicThickeningTransition (productToBase f g) I n := by
  apply (cancel_mono (adicThickeningι (productToBase f g) I (n + 1))).mp
  simp only [Category.assoc, adicThickeningTransition_ι, formalGraph_ι]
  apply pullback.hom_ext
  · simp only [graphToProduct, Category.assoc, pullback.lift_fst,
      adicThickeningTransition_ι]
  · simp only [graphToProduct, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, hφt n, Category.assoc, adicThickeningTransition_ι]

private theorem formalGraph_transition_isPullback
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) =
      φ n ≫ adicThickeningTransition g I n) (n : ℕ) :
    IsPullback (adicThickeningTransition f I n) (formalGraph I f g n (φ n) (hφ n))
      (formalGraph I f g (n + 1) (φ (n + 1)) (hφ (n + 1)))
      (adicThickeningTransition (productToBase f g) I n) := by
  refine (IsPullback.of_right ?_ (formalGraph_transition I f g φ hφ hφt n).symm
    (transition_isPullback I (productToBase f g) n).flip).flip
  simpa only [formalGraph_toBase] using (transition_isPullback I f n).flip

end Graph

/-- Compatible morphisms on all adic thickenings of proper schemes algebraize uniquely. -/
theorem properAlgebraization : ProperAlgebraization.{u} := by
  intro R _ _ I _ X Y f g hf hg φ hφ hφt
  letI : IsProper f := hf
  letI : IsProper g := hg
  let p : pullback f g ⟶ Spec (CommRingCat.of R) := productToBase f g
  haveI : IsProper p := by dsimp [p, productToBase]; infer_instance
  let γ := fun n : ℕ => formalGraph I f g n (φ n) (hφ n)
  haveI : ∀ n : ℕ, IsClosedImmersion (γ n) := fun n =>
    formalGraph_isClosedImmersion I f g n (φ n) (hφ n)
  haveI : ∀ n : ℕ, IsFinite (γ n) := fun n => inferInstance
  obtain ⟨Γ, G, hG, e, he, _⟩ :=
    AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
      R I (pullback f g) p (fun n => adicThickeningBase I n)
      (fun n => by rw [Ideal.Quotient.algebraMap_eq])
      (fun n => baseTransition I n) (fun n => adicThickeningBase_succ_comp I n)
      (fun n => adicThickeningTransition p I n)
      (fun n => adicThickeningTransition_ι p I n)
      (fun n => adicThickeningTransition_toBase p I n)
      (fun n => adicThickening f I n) γ (fun n => adicThickeningTransition f I n)
      (fun n => formalGraph_transition_isPullback I f g φ hφ hφt n)
  letI : IsFinite G := hG
  haveI : IsClosedImmersion G :=
    AlgebraicGeometry.isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
      R I p G (fun n => adicThickeningBase I n)
      (fun n => by rw [Ideal.Quotient.algebraMap_eq]) (fun n => by
        rw [← he n]
        infer_instance)
  let h : Γ ⟶ X := G ≫ pullback.fst f g
  haveI : IsProper h := by dsimp [h]; infer_instance
  have hc (n : ℕ) :
      pullback.fst G (adicThickeningι p I n) ≫ h = (e n).hom ≫ adicThickeningι f I n := by
    calc
      pullback.fst G (adicThickeningι p I n) ≫ h =
          (pullback.fst G (adicThickeningι p I n) ≫ G) ≫ pullback.fst f g := by
        simp only [h, Category.assoc]
      _ = (pullback.snd G (adicThickeningι p I n) ≫ adicThickeningι p I n) ≫
          pullback.fst f g := by rw [pullback.condition]
      _ = (e n).hom ≫ γ n ≫ adicThickeningι p I n ≫ pullback.fst f g := by
        rw [← he n]
        simp only [Category.assoc]
      _ = (e n).hom ≫ adicThickeningι f I n := by
        exact congrArg ((e n).hom ≫ ·) (formalGraph_ι_fst I f g n (φ n) (hφ n))
  have hp (n : ℕ) :
      IsPullback (pullback.fst G (adicThickeningι p I n)) ((e n).hom) h
        (adicThickeningι f I n) := by
    have hout := (IsPullback.of_hasPullback G (adicThickeningι p I n)).paste_vert
      (IsPullback.of_hasPullback p (adicThickeningBase I n))
    have hb : pullback.snd G (adicThickeningι p I n) ≫ adicThickeningToBase p I n =
        (e n).hom ≫ adicThickeningToBase f I n := by
      rw [← he n, Category.assoc]
      exact congrArg ((e n).hom ≫ ·) (formalGraph_toBase I f g n (φ n) (hφ n))
    have hs : G ≫ p = h ≫ f := by simp only [h, p, productToBase, Category.assoc]
    rw [hb, hs] at hout
    exact IsPullback.of_bot hout (hc n)
      (IsPullback.of_hasPullback f (adicThickeningBase I n))
  haveI : IsIso h :=
    AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
      R I f h (fun n => adicThickeningBase I n)
      (fun n => by rw [Ideal.Quotient.algebraMap_eq]) (fun n => by
        let a := (hp n).isoPullback
        haveI : IsIso (a.hom ≫ pullback.snd h (adicThickeningι f I n)) := by
          rw [(hp n).isoPullback_hom_snd]
          infer_instance
        exact IsIso.of_isIso_comp_left a.hom _)
  let ψ : X ⟶ Y := inv h ≫ G ≫ pullback.snd f g
  have hψ : ψ ≫ g = f := by
    calc
      ψ ≫ g = inv h ≫ (G ≫ pullback.fst f g) ≫ f := by
        simp only [ψ, Category.assoc, ← pullback.condition]
      _ = f := by change inv h ≫ h ≫ f = f; simp
  have hψn (n : ℕ) : adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by
    have hl : adicThickeningι f I n ≫ inv h =
        (e n).inv ≫ pullback.fst G (adicThickeningι p I n) := by
      apply (cancel_mono h).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [hc n, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    calc
      adicThickeningι f I n ≫ ψ =
          (adicThickeningι f I n ≫ inv h) ≫ G ≫ pullback.snd f g := by
        simp only [ψ, Category.assoc]
      _ = (e n).inv ≫ pullback.fst G (adicThickeningι p I n) ≫ G ≫ pullback.snd f g := by
        rw [hl, Category.assoc]
      _ = (e n).inv ≫ (pullback.fst G (adicThickeningι p I n) ≫ G) ≫
          pullback.snd f g := by simp only [Category.assoc]
      _ = (e n).inv ≫ (pullback.snd G (adicThickeningι p I n) ≫
          adicThickeningι p I n) ≫ pullback.snd f g := by rw [pullback.condition]
      _ = γ n ≫ adicThickeningι p I n ≫ pullback.snd f g := by
        rw [← he n]
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = φ n ≫ adicThickeningι g I n := formalGraph_ι_snd I f g n (φ n) (hφ n)
  refine ⟨ψ, ⟨hψ, hψn⟩, ?_⟩
  intro ψ' hψ'
  exact eq_of_forall_adicThickening_comp_eq_of_isProper I f g hψ'.1 hψ
    (fun n => (hψ'.2 n).trans (hψn n).symm)

end ZInQ.Contrib.CloudB3SC2Mumford
