import TorusLocalDimensionV006
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The universal point of a natural split-torus presentation

The semi-abelian identity-component data present the kernel of `π : U → B` through a family
`e_R : (R^×)^r →* U(R)` over all `k`-algebras `R`, natural in `k`-algebra maps `f : R → S`:
`e_S (f ∘ t) = U(f) (e_R t)`. Here `U(R)` is `Hom_k(Spec R, U)` with `Spec R` over `Spec k`
through `algebraMap k R` (the point objects `algPt`, `algPtMap` below have the same bodies as the
kernel's). Naturality alone yields, by evaluating at the coordinate units `X_i` of
`k[X_i^{±1}]`, an actual morphism of `k`-schemes `τ : 𝔾_m^r = Spec k[X_i^{±1}] → U` with
`e_R t = Spec(t^♯) ≫ τ` for every `R` and `t`, where `t^♯ : k[X_i^{±1}] → R` sends `X_i ↦ t_i`.
Injectivity of `e_A` for every `k`-algebra `A` then makes `τ` injective on `A`-points.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TorusDimension

namespace SemiAbelianKernel

section Points

variable (k : Type) [Field k]

/-- `Spec R` as a `k`-scheme (same body as the kernel's `algPt`). -/
noncomputable def algPt (R : Type) [CommRing R] [Algebra k R] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

variable {k}

/-- `Spec S → Spec R` over `k` (same body as the kernel's `algPtMap`). -/
noncomputable def algPtMap {R S : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) : algPt k S ⟶ algPt k R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : R →+* S))) (by
    simp only [algPt, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

/-- Every `k`-morphism `Spec A → Spec R` is `Spec` of a `k`-algebra map. -/
theorem exists_algPtMap {R A : Type} [CommRing R] [Algebra k R] [CommRing A] [Algebra k A]
    (p : algPt k A ⟶ algPt k R) : ∃ φ : R →ₐ[k] A, algPtMap φ = p := by
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀, Spec.map φ₀ = p.left := ⟨Spec.preimage p.left, Spec.map_preimage _⟩
  have hw : p.left ≫ (algPt k R).hom = (algPt k A).hom := Over.w p
  have h1 : CommRingCat.ofHom (algebraMap k R) ≫ φ₀ = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ₀]
    exact hw
  refine ⟨{ φ₀.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) h1
    simpa using this
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom φ₀.hom) = p.left
    rw [CommRingCat.ofHom_hom, hφ₀]

end Points

section Torus

variable {k : Type} [Field k] (r : ℕ)

theorem coord_isUnit (i : Fin r) :
    IsUnit (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) (MvPolynomial.X i)) :=
  isUnit_of_dvd_unit
    (map_dvd (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r))
      (Finset.dvd_prod_of_mem (fun j => (MvPolynomial.X j : MvPolynomial (Fin r) k))
        (Finset.mem_univ i)))
    (IsLocalization.Away.algebraMap_isUnit (torusProd k r))

/-- The coordinate units `X_i` of `k[X_i^{±1}]`. -/
def coordUnit (i : Fin r) : (TorusRing k r)ˣ := (coord_isUnit r i).unit

theorem coordUnit_val (i : Fin r) :
    ((coordUnit (k := k) r i : (TorusRing k r)ˣ) : TorusRing k r) =
      algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) (MvPolynomial.X i) :=
  IsUnit.unit_spec _

theorem torusLift_coord {R : Type} [CommRing R] [Algebra k R] (t : Fin r → Rˣ) (i : Fin r) :
    Units.map (torusLift k r t : TorusRing k r →* R) (coordUnit r i) = t i := by
  apply Units.ext
  rw [Units.coe_map, coordUnit_val, MonoidHom.coe_coe]
  exact torusLift_X k r t i

/-- `k`-algebra maps out of `k[X_i^{±1}]` are determined by the images of the `X_i`. -/
theorem torus_algHom_ext {A : Type} [CommRing A] [Algebra k A] (φ ψ : TorusRing k r →ₐ[k] A)
    (h : ∀ i, φ (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) (MvPolynomial.X i)) =
      ψ (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) (MvPolynomial.X i))) : φ = ψ := by
  have h1 : φ.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (TorusRing k r)) =
      ψ.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (TorusRing k r)) :=
    MvPolynomial.algHom_ext fun i => h i
  refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
    (Submonoid.powers (torusProd k r)) (RingHom.ext fun p => ?_))
  exact DFunLike.congr_fun h1 p

end Torus

section Presentation

variable {k : Type} [Field k] (r : ℕ) (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
  (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))

/-- The naturality of the presentation in `k`-algebra maps (the shape of the kernel's field). -/
def IsNatural : Prop :=
  ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
    (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t

/-- **The universal point** `τ = e_{k[X^{±1}]}(X_1, …, X_r) : 𝔾_m^r → U`. -/
def univPoint : algPt k (TorusRing k r) ⟶ U := e (TorusRing k r) (coordUnit r)

variable {r U e}

/-- **Yoneda factorization**: `e_R t = Spec(t^♯) ≫ τ`. -/
theorem e_eq_comp_univPoint (hnat : IsNatural r U e) (R : Type) [CommRing R] [Algebra k R]
    (t : Fin r → Rˣ) : e R t = algPtMap (torusLift k r t) ≫ univPoint r U e := by
  have h := hnat (TorusRing k r) R (torusLift k r t) (coordUnit r)
  rw [show (fun i => Units.map (torusLift k r t : TorusRing k r →* R) (coordUnit r i)) = t from
    funext (torusLift_coord r t)] at h
  exact h

/-- **`τ` is injective on `A`-points** for every `k`-algebra `A`. -/
theorem univPoint_cancel (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    {A : Type} [CommRing A] [Algebra k A] (p q : algPt k A ⟶ algPt k (TorusRing k r))
    (h : p ≫ univPoint r U e = q ≫ univPoint r U e) : p = q := by
  obtain ⟨φ, rfl⟩ := exists_algPtMap p
  obtain ⟨ψ, rfl⟩ := exists_algPtMap q
  have hφ := hnat (TorusRing k r) A φ (coordUnit r)
  have hψ := hnat (TorusRing k r) A ψ (coordUnit r)
  unfold univPoint at h
  rw [← hφ, ← hψ] at h
  have h2 := he A h
  have h3 : φ = ψ := torus_algHom_ext r φ ψ fun i => by
    have := congrArg (fun t => ((t i : Aˣ) : A)) h2
    simpa [coordUnit_val] using this
  rw [h3]

/-- The identity character gives the identity point: `Spec(1^♯) ≫ τ = 1`. -/
theorem onePoint_comp_univPoint (hnat : IsNatural r U e) :
    algPtMap (oneChar k r) ≫ univPoint r U e = 1 := by
  rw [oneChar, ← e_eq_comp_univPoint hnat k (fun _ => 1)]
  exact (e k).map_one

end Presentation

end SemiAbelianKernel
