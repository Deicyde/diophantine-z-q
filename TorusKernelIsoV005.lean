import TorusPresentationV001
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The scheme-theoretic kernel of `π` is the split torus

`K = U ×_{π, B, η} Spec k` is the scheme-theoretic kernel of `π : U → B` (the fibre over the
identity section of `B`). From the natural presentation `e` (naturality, injectivity, kernel
condition) this file proves that the universal point `τ : 𝔾_m^r → U` factors through `K` and
that the factorization `τ' : 𝔾_m^r → K` is an isomorphism of schemes:

* `τ` is a monomorphism of schemes (cancellation on affine pieces, from injectivity of `e`);
* every affine piece `Spec A → K` is an `A`-point of `U` with trivial image in `B`, hence of the
  form `e_A t = Spec(t^♯) ≫ τ`; these local inverses glue along the affine open cover of `K`.

Consequently the local ring of `K` at the image of the identity of `𝔾_m^r` has Krull dimension
`r`.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open TorusDimension

namespace SemiAbelianKernel

variable {k : Type} [Field k] {r : ℕ} {U B : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj B]
  {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)}

/-- The identity section `Spec k → B`. -/
abbrev unitSec (B : Over (Spec (CommRingCat.of k))) [GrpObj B] :
    Spec (CommRingCat.of k) ⟶ B.left :=
  (η[B] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B).left

/-- **The scheme-theoretic kernel** `U ×_B Spec k` of `π`. -/
abbrev kernel (π : U ⟶ B) : Scheme := pullback π.left (unitSec B)

theorem unitSec_comp : unitSec B ≫ B.hom = 𝟙 _ :=
  Over.w (η[B] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B)

instance unitSec_mono : Mono (unitSec B) := mono_of_mono_fac unitSec_comp

theorem kernel_snd_eq (π : U ⟶ B) :
    pullback.snd π.left (unitSec B) = pullback.fst π.left (unitSec B) ≫ U.hom := by
  have h := congrArg (· ≫ B.hom) (pullback.condition (f := π.left) (g := unitSec B))
  simp only [Category.assoc, Over.w π, unitSec_comp, Category.comp_id] at h
  exact h.symm

variable (k r) in
/-- The structure map `Spec k[X^{±1}] → Spec k`. -/
def strT : Spec (CommRingCat.of (TorusRing k r)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (TorusRing k r)))

variable (r U e) in
/-- `τ` as a morphism of schemes `Spec k[X^{±1}] → U`. -/
def tauL : Spec (CommRingCat.of (TorusRing k r)) ⟶ U.left := (univPoint r U e).left

theorem tauL_w : tauL r U e ≫ U.hom = strT k r := Over.w (univPoint r U e)

/-- **Cancellation from the spectrum of a ring.** -/
theorem cancel_from_spec (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (A : CommRingCat) (a b : Spec A ⟶ Spec (CommRingCat.of (TorusRing k r)))
    (h : a ≫ tauL r U e = b ≫ tauL r U e) : a = b := by
  letI : Algebra k A := (Spec.preimage (a ≫ strT k r)).hom.toAlgebra
  have hs : (algPt k A).hom = a ≫ strT k r := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (a ≫ strT k r)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h1 : (a ≫ tauL r U e) ≫ U.hom = (b ≫ tauL r U e) ≫ U.hom := congrArg (· ≫ U.hom) h
  have hsb : b ≫ strT k r = a ≫ strT k r :=
    calc b ≫ strT k r = b ≫ (tauL r U e ≫ U.hom) := by rw [tauL_w]
      _ = (b ≫ tauL r U e) ≫ U.hom := (Category.assoc _ _ _).symm
      _ = (a ≫ tauL r U e) ≫ U.hom := h1.symm
      _ = a ≫ (tauL r U e ≫ U.hom) := Category.assoc _ _ _
      _ = a ≫ strT k r := by rw [tauL_w]
  let a' : algPt k A ⟶ algPt k (TorusRing k r) := Over.homMk a hs.symm
  let b' : algPt k A ⟶ algPt k (TorusRing k r) := Over.homMk b (hsb.trans hs.symm)
  have hab : a' ≫ univPoint r U e = b' ≫ univPoint r U e := by
    apply Over.OverMorphism.ext
    exact h
  exact congrArg (fun p => p.left) (univPoint_cancel hnat he a' b' hab)

/-- **Cancellation from an affine scheme.** -/
theorem cancel_from_affine (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (W : Scheme) [IsAffine W] (a b : W ⟶ Spec (CommRingCat.of (TorusRing k r)))
    (h : a ≫ tauL r U e = b ≫ tauL r U e) : a = b := by
  rw [← cancel_epi W.isoSpec.inv]
  exact cancel_from_spec hnat he _ _ _ ((Category.assoc _ _ _).trans
    ((congrArg (fun x => W.isoSpec.inv ≫ x) h).trans (Category.assoc _ _ _).symm))

/-- **`τ` is a monomorphism of schemes.** -/
theorem tauL_mono (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R)) :
    Mono (tauL r U e) :=
  ⟨fun {Z} a b h => Z.affineCover.hom_ext a b fun j =>
    cancel_from_affine hnat he (Z.affineCover.X j) _ _ ((Category.assoc _ _ _).trans
      ((congrArg (fun x => Z.affineCover.f j ≫ x) h).trans (Category.assoc _ _ _).symm))⟩

/-- `τ` lands in the kernel. -/
theorem tauL_comp_eq (π : U ⟶ B) [IsMonHom π]
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    tauL r U e ≫ π.left = strT k r ≫ unitSec B := by
  have h : univPoint r U e ≫ π = 1 := (hker _ _).2 ⟨coordUnit r, rfl⟩
  have h' := congrArg (fun p => p.left) h
  rw [Hom.one_def] at h'
  exact h'

/-- **The factorization `τ' : 𝔾_m^r → K`.** -/
def kernelLift (π : U ⟶ B) [IsMonHom π]
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    Spec (CommRingCat.of (TorusRing k r)) ⟶ kernel π :=
  pullback.lift (tauL r U e) (strT k r) (tauL_comp_eq π hker)

theorem kernelLift_fst (π : U ⟶ B) [IsMonHom π]
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    kernelLift π hker ≫ pullback.fst π.left (unitSec B) = tauL r U e :=
  pullback.lift_fst _ _ _

theorem kernelLift_mono (π : U ⟶ B) [IsMonHom π] (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) : Mono (kernelLift π hker) := by
  have := tauL_mono hnat he
  exact mono_of_mono_fac (kernelLift_fst π hker)

/-- **Local inverse on the spectrum of a ring mapping to the kernel.** -/
theorem exists_local_inverse_spec (π : U ⟶ B) [IsMonHom π] (hnat : IsNatural r U e)
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (A : CommRingCat) (v : Spec A ⟶ kernel π) :
    ∃ g : Spec A ⟶ Spec (CommRingCat.of (TorusRing k r)), g ≫ kernelLift π hker = v := by
  letI : Algebra k A :=
    (Spec.preimage ((v ≫ pullback.fst π.left (unitSec B)) ≫ U.hom)).hom.toAlgebra
  have hs : (algPt k A).hom = (v ≫ pullback.fst π.left (unitSec B)) ≫ U.hom := by
    show Spec.map (CommRingCat.ofHom
      (Spec.preimage ((v ≫ pullback.fst π.left (unitSec B)) ≫ U.hom)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let u' : algPt k A ⟶ U := Over.homMk (v ≫ pullback.fst π.left (unitSec B)) hs.symm
  have hu1 : u' ≫ π = 1 := by
    rw [Hom.one_def]
    apply Over.OverMorphism.ext
    show (v ≫ pullback.fst π.left (unitSec B)) ≫ π.left = (algPt k A).hom ≫ unitSec B
    rw [hs]
    show (v ≫ pullback.fst π.left (unitSec B)) ≫ π.left =
      ((v ≫ pullback.fst π.left (unitSec B)) ≫ U.hom) ≫ unitSec B
    rw [Category.assoc, pullback.condition, kernel_snd_eq]
    simp only [Category.assoc]
  obtain ⟨t, ht⟩ := (hker A u').1 hu1
  have hfac := e_eq_comp_univPoint hnat A t
  rw [ht] at hfac
  have hleft : v ≫ pullback.fst π.left (unitSec B) =
      (algPtMap (torusLift k r t)).left ≫ tauL r U e :=
    congrArg (fun p => p.left) hfac
  refine ⟨(algPtMap (torusLift k r t)).left, ?_⟩
  apply (cancel_mono (pullback.fst π.left (unitSec B))).1
  exact (Category.assoc _ _ _).trans ((congrArg (fun x => (algPtMap (torusLift k r t)).left ≫ x)
    (kernelLift_fst π hker)).trans hleft.symm)

/-- **Local inverse on an affine scheme mapping to the kernel.** -/
theorem exists_local_inverse (π : U ⟶ B) [IsMonHom π] (hnat : IsNatural r U e)
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (W : Scheme) [IsAffine W] (v : W ⟶ kernel π) :
    ∃ g : W ⟶ Spec (CommRingCat.of (TorusRing k r)), g ≫ kernelLift π hker = v := by
  obtain ⟨g, hg⟩ := exists_local_inverse_spec π hnat hker _ (W.isoSpec.inv ≫ v)
  exact ⟨W.isoSpec.hom ≫ g, (Category.assoc _ _ _).trans
    ((congrArg (fun x => W.isoSpec.hom ≫ x) hg).trans (Iso.hom_inv_id_assoc _ _))⟩

/-- **The kernel is the torus**: `τ' : 𝔾_m^r → K` is an isomorphism of schemes. -/
theorem kernelLift_isIso (π : U ⟶ B) [IsMonHom π] (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) : IsIso (kernelLift π hker) := by
  have hmono := kernelLift_mono π hnat he hker
  let 𝒰 := (kernel π).affineCover
  choose g hg using fun j => exists_local_inverse π hnat hker (𝒰.X j) (𝒰.f j)
  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ g x =
      pullback.snd (𝒰.f x) (𝒰.f y) ≫ g y := by
    intro x y
    apply (cancel_mono (kernelLift π hker)).1
    simp only [Category.assoc, hg]
    exact pullback.condition
  let G := 𝒰.glueMorphisms g hcompat
  have h1 : G ≫ kernelLift π hker = 𝟙 _ := 𝒰.hom_ext _ _ fun j => by
    rw [← Category.assoc, 𝒰.ι_glueMorphisms, hg, Category.comp_id]
  have h2 : kernelLift π hker ≫ G = 𝟙 _ := by
    apply (cancel_mono (kernelLift π hker)).1
    rw [Category.assoc, h1, Category.comp_id, Category.id_comp]
  exact ⟨⟨G, h2, h1⟩⟩

variable (k r) in
/-- The identity point of `Spec k[X^{±1}]`, as a point of the scheme. -/
def onePointT : Spec (CommRingCat.of (TorusRing k r)) := onePoint k r

/-- **The local ring of the kernel at the identity of the torus has dimension `r`.** -/
theorem kernel_stalk_dim (π : U ⟶ B) [IsMonHom π] (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    ringKrullDim ((kernel π).presheaf.stalk ((kernelLift π hker) (onePointT k r))) = r := by
  have := kernelLift_isIso π hnat he hker
  rw [ringKrullDim_eq_of_ringEquiv
    (asIso ((kernelLift π hker).stalkMap (onePointT k r))).commRingCatIsoToRingEquiv]
  exact ringKrullDim_stalk_one k r

end SemiAbelianKernel
