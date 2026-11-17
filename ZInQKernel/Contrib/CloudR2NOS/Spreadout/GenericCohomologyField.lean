/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): generic-fibre cohomology over the ORIGINAL field

New glue (no vendored source in this file). It continues `GenericCohomologyTransport`, which is
unchanged.

* `hFiber_baseIso`, `hFiber_eq_finrankH_of_iso`, `eulerCharFiber_eq_eulerChar_of_iso`: for a base
  `T` with an isomorphism `i : T ≅ Spec K` (for example lane 5's
  `Effective.exists_dvr_genericOpen_originalField`, whose `i` satisfies
  `i.hom ≫ Spec.map (algebraMap O K) = V.ι`), the W07 fibre cohomology dimensions and Euler
  characteristic over `T` are the native W07 `K`-cohomology with structure map `f ≫ i.hom`.
  The proof is W07's `hFiber_pullback_of_isPullback` on the isomorphism square
  `IsPullback (𝟙) (f ≫ i.hom) f i.inv`, followed by W07's `hFiber_eq_finrankH`.
* `hFiber_transport_originalField` / `eulerCharFiber_transport_originalField`: for lane 5's
  objects, `M.hFiber G.X.hom n (ι t)` equals the `K`-cohomology of the ORIGINAL `L`, in every
  degree, and the same holds for `χ`.
* `genericPoint_mem_preimage`: for the literal stage map
  `p = Spec.map (algebraMap O Bs)` with `O → Bs` injective and `V` the generic open of the DVR
  `Spec O` (complement only the closed point), the LITERAL generic point of `Spec Bs` lies in
  `p⁻¹V`. So `hFiber_genericPoint_originalField` / `eulerCharFiber_genericPoint_originalField`
  need no membership hypothesis.

No cohomology equality, positivity, nonzero `χ`, transition or Čech hypothesis is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberField

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

section BaseIso

variable {X T T' : Scheme.{u}} (f : X ⟶ T) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Fibre cohomology dimensions are unchanged along an isomorphism of the base. -/
theorem hFiber_baseIso (i : T ≅ T') (n : ℕ) (t : T) :
    M.hFiber f n t = M.hFiber (f ≫ i.hom) n (i.hom.base t) := by
  have sq : IsPullback (𝟙 X) (f ≫ i.hom) f i.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := Scheme.Modules.hFiber_pullback_of_isPullback f M i.inv (𝟙 X) (f ≫ i.hom) sq n
    (i.hom.base t)
  let e : (Scheme.Modules.pullback (𝟙 X)).obj M ≅ M := (Scheme.Modules.pullbackId X).app M
  have h' := Scheme.Modules.hFiber_congr e (f ≫ i.hom) n (i.hom.base t)
  have hpt : i.inv.base (i.hom.base t) = t := Scheme.hom_inv_apply i t
  rw [← h', h, hpt]

/-- **Over a base isomorphic to `Spec K`, fibre cohomology is the `K`-cohomology.** -/
theorem hFiber_eq_finrankH_of_iso {K : Type u} [Field K] (i : T ≅ Spec (CommRingCat.of K))
    (n : ℕ) (t : T) :
    M.hFiber f n t =
      (letI : X.Over (Spec (CommRingCat.of K)) := ⟨f ≫ i.hom⟩; M.finrankH K n) := by
  rw [hFiber_baseIso f M i n t]
  exact Scheme.Modules.hFiber_eq_finrankH (f ≫ i.hom) M n (i.hom.base t)

/-- Over a base isomorphic to `Spec K`, the fibre Euler characteristic is the `K`-Euler
characteristic. -/
theorem eulerCharFiber_eq_eulerChar_of_iso {K : Type u} [Field K]
    (i : T ≅ Spec (CommRingCat.of K)) (t : T) :
    M.eulerCharFiber f t =
      (letI : X.Over (Spec (CommRingCat.of K)) := ⟨f ≫ i.hom⟩; M.eulerChar K) := by
  simp only [Scheme.Modules.eulerCharFiber, Scheme.Modules.eulerChar,
    hFiber_eq_finrankH_of_iso f M i]

end BaseIso

section Original

variable {Bs : Type u} [CommRing Bs] {S : Scheme.{u}} (p : Spec (CommRingCat.of Bs) ⟶ S)
  (V : S.Opens) (G : Grp (Over (Spec (CommRingCat.of Bs)))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)

/-- **Generic model cohomology is the ORIGINAL `K`-cohomology of `L`, in every degree.** -/
theorem hFiber_transport_originalField [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] {K : Type u} [Field K]
    (i : V.toScheme ≅ Spec (CommRingCat.of K)) (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L)
    (n : ℕ) (t : (p ⁻¹ᵁ V).toScheme) :
    M.hFiber G.X.hom n ((p ⁻¹ᵁ V).ι.base t) =
      (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom ≫ i.hom⟩; L.finrankH K n) := by
  rw [hFiber_transport p V G A e M L β n t]
  exact hFiber_eq_finrankH_of_iso A.X.hom L i n _

/-- **Generic model Euler characteristic is the ORIGINAL `K`-Euler characteristic of `L`.** -/
theorem eulerCharFiber_transport_originalField [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] {K : Type u} [Field K]
    (i : V.toScheme ≅ Spec (CommRingCat.of K)) (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso p V G A e).q).obj L)
    (t : (p ⁻¹ᵁ V).toScheme) :
    M.eulerCharFiber G.X.hom ((p ⁻¹ᵁ V).ι.base t) =
      (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom ≫ i.hom⟩; L.eulerChar K) := by
  rw [eulerCharFiber_transport p V G A e M L β t]
  exact eulerCharFiber_eq_eulerChar_of_iso A.X.hom L i _

end Original

section GenericPoint

/-- For the literal stage map of an injective `O → Bs` and the generic open `V` of the DVR
`Spec O`, the literal generic point of `Spec Bs` lies in `p⁻¹V`. -/
theorem genericPoint_mem_preimage {O Bs : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Bs] [IsDomain Bs] [Algebra O Bs]
    (hinj : Function.Injective (algebraMap O Bs)) (V : (Spec (CommRingCat.of O)).Opens)
    (hV : ∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O) :
    genericPoint (Spec (CommRingCat.of Bs)) ∈
      Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V := by
  by_contra h
  have h2 := hV ((Spec.map (CommRingCat.ofHom (algebraMap O Bs))).base
    (genericPoint (Spec (CommRingCat.of Bs)))) h
  have h3 := congrArg PrimeSpectrum.asIdeal h2
  rw [Spec.map_apply, genericPoint_eq_bot_of_affine] at h3
  change Ideal.comap (algebraMap O Bs) ⊥ = IsLocalRing.maximalIdeal O at h3
  rw [Ideal.comap_bot_of_injective _ hinj] at h3
  exact IsDiscreteValuationRing.not_a_field O h3.symm

variable {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Bs]
  [IsDomain Bs] [Algebra O Bs] (hinj : Function.Injective (algebraMap O Bs))
  (V : (Spec (CommRingCat.of O)).Opens)
  (hV : ∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O)
  (G : Grp (Over (Spec (CommRingCat.of Bs)))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ∣_ V)).mapGrp.obj A)

include hinj hV

/-- **At the literal generic point of the stage DVR, in every degree, against the ORIGINAL `K`.** -/
theorem hFiber_genericPoint_originalField [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] {K : Type u} [Field K]
    (i : V.toScheme ≅ Spec (CommRingCat.of K)) (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback
        (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso
        (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G A e).q).obj L)
    (n : ℕ) :
    M.hFiber G.X.hom n (genericPoint (Spec (CommRingCat.of Bs))) =
      (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom ≫ i.hom⟩; L.finrankH K n) :=
  hFiber_transport_originalField (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G A e i M L β n
    ⟨_, genericPoint_mem_preimage hinj V hV⟩

/-- Euler characteristic at the literal generic point of the stage DVR, against the ORIGINAL `K`. -/
theorem eulerCharFiber_genericPoint_originalField [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom] {K : Type u} [Field K]
    (i : V.toScheme ≅ Spec (CommRingCat.of K)) (M : G.X.left.Modules) [M.IsQuasicoherent]
    (L : A.X.left.Modules) [L.IsQuasicoherent]
    (β : (Scheme.Modules.pullback
        (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso
        (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G A e).q).obj L) :
    M.eulerCharFiber G.X.hom (genericPoint (Spec (CommRingCat.of Bs))) =
      (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom ≫ i.hom⟩; L.eulerChar K) :=
  eulerCharFiber_transport_originalField (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G A e
    i M L β ⟨_, genericPoint_mem_preimage hinj V hV⟩

end GenericPoint

end ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport
