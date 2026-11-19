import Mathlib

/-!
# Paired functional: integral homotopy inverses and closedness (homological cores)

Proposition `ex:arith-paired-functional` of `diophantine_zq.tex` (tex L3704–3880). Its proof builds
the closed degree-two functional `λ_z = PD(−, j⁻¹ c(z))` (tex L3742–3749, L3845–3860) from an
*integral* homotopy inverse `j⁻¹` of the comparison `j : C_{U^⊥} → τ^* C_U`, obtained by contracting
an acyclic cone of bounded free complexes (tex L3790–3794, L3846–3863). This file proves the
homological-algebra cores of that construction over an arbitrary commutative ring `S` (in the
manuscript `S = 𝒪[G]`, or a localization `Λ_𝔭`), on Mathlib's genuine objects: cochain complexes
`CochainComplex (ModuleCat S) ℤ`, `Homotopy`, `HomotopyEquiv`, `CochainComplex.mappingCone` and the
triangulated homotopy category.

Nodes (each a `def … : Prop` with its proof `…_proof`):

* `ConeContractionInverse` (tex L3853–3858; PROVED): a contraction of the mapping cone of `j`
  yields a chain map `j⁻¹` with `j j⁻¹ ≃ 1` and `j⁻¹ j ≃ 1`.
* `BoundedAcyclicFreeContractible` (tex L3790–3794; PROVED): a bounded acyclic complex of free
  modules is contractible.
* `QuasiIsoFreeHomotopyInverse` (tex L3790–3792; PROVED): a quasi-isomorphism between bounded free
  complexes has an integral homotopy inverse.
* `FiniteSumContractible` (tex L3846–3849; PROVED): a finite direct sum of contractible complexes is
  contractible.
* `IntegralClosedLift` (tex L3850–3863; PROVED): `z^⊥ = j⁻¹ c(z)` is a cocycle, `j(z^⊥) − c(z)` is a
  boundary, and `λ_z = PD(−, z^⊥)` is closed.
* `PairedFunctionalWellDefined` (tex L3755–3758; PROVED): two homotopy inverses of the same `j`
  give functionals differing by a coboundary `y ∘ d`, hence the same functional on `H²`.

`DEPARTURE` (proof route, `BoundedAcyclicFreeContractible`, `QuasiIsoFreeHomotopyInverse`): Elliot
splits the acyclic free cone "from its last nonzero term and proceeding downwards" (tex L3792–3794).
We use Mathlib's theorem that a bounded-above complex of projectives is K-projective
(`CochainComplex.isKProjective_of_projective`), which contains that splitting argument; the
statements are Elliot's (only the upper bound is used, the lower bound is kept as in the text).

`DEPARTURE` (form only, `IntegralClosedLift`, `PairedFunctionalWellDefined`): the retained global
duality, a chain map `C_U ⊗ C_{U^⊥} → S[−3]` in the text, enters as its three components in total
degree three that are used, `PD₁ : C_U^1 × C_{U^⊥}^2 → S`, `PD₂ : C_U^2 × C_{U^⊥}^1 → S`,
`PD₃ : C_U^3 × C_{U^⊥}^0 → S` (`S`-bilinear), with the two Leibniz rules relating them; the Leibniz
signs are arbitrary scalars `ε, ε'` (`±1` in any sign convention). The conjugate transport `c` is a
chain map into `τ^* C_U` and `z` a degree-one cocycle.
-/

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits HomotopyCategory Pretriangulated

universe u

section Cone

variable {S : Type u} [CommRing S]

/-- tex L3853–3858: a contraction of the mapping cone of `φ` makes `φ` a homotopy equivalence
(PROVED: the cone is zero in the triangulated homotopy category, so `φ` becomes an isomorphism
there). -/
theorem homotopyEquiv_of_cone_contractible {K L : CochainComplex (ModuleCat.{u} S) ℤ}
    (φ : K ⟶ L) (h : Homotopy (𝟙 (CochainComplex.mappingCone φ)) 0) :
    ∃ e : HomotopyEquiv K L, e.hom = φ := by
  have hT := mappingCone_triangleh_distinguished φ
  have hZ : IsZero ((CochainComplex.mappingCone.triangleh φ).obj₃) :=
    (isZero_quotient_obj_iff _).2 ⟨h⟩
  have hI : IsIso ((quotient _ _).map φ) :=
    (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ
  have hφ : (MorphismProperty.isomorphisms _).inverseImage
      (HomotopyCategory.quotient (ModuleCat.{u} S) (ComplexShape.up ℤ)) φ := hI
  rw [inverseImage_quotient_isomorphisms] at hφ
  exact hφ

/-- Non-vacuity of the cone hypothesis: the cone of an identity is contractible (tex L3853–3858).
PROVED. -/
theorem cone_id_contractible (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone (𝟙 K))) 0) :=
  ⟨CochainComplex.mappingCone.homotopyToZeroOfId K⟩

end Cone

section Acyclic

variable {S : Type u} [CommRing S]

/-- tex L3790–3794: a bounded-above acyclic complex of projective `S`-modules is contractible.
PROVED (Mathlib: such a complex is K-projective, so its identity, a map to an acyclic complex, is
null-homotopic). -/
theorem contractible_of_acyclic_projective (K : CochainComplex (ModuleCat.{u} S) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ n, Module.Projective S (K.X n)] (hK : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  have : K.IsKProjective := CochainComplex.isKProjective_of_projective K b
  exact CochainComplex.IsKProjective.nonempty_homotopy_zero (𝟙 K) hK

/-- tex L3790–3794: "its bounded acyclic free cone is contractible". PROVED. -/
theorem contractible_of_acyclic_free (K : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [∀ n, Module.Free S (K.X n)] (hK : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) :=
  contractible_of_acyclic_projective K b hK

/-- tex L3790–3792: "A quasi-isomorphism between these bounded free models has an integral
homotopy inverse". PROVED (Mathlib: a quasi-isomorphism between K-projective complexes is a
homotopy equivalence). -/
theorem homotopyEquiv_of_quasiIso_free {K L : CochainComplex (ModuleCat.{u} S) ℤ} (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ n, Module.Free S (K.X n)] [∀ n, Module.Free S (L.X n)] (φ : K ⟶ L) [QuasiIso φ] :
    ∃ e : HomotopyEquiv K L, e.hom = φ := by
  have : K.IsKProjective := CochainComplex.isKProjective_of_projective K b
  have : L.IsKProjective := CochainComplex.isKProjective_of_projective L b
  exact (CochainComplex.IsKProjective.quasiIso_iff φ).1 inferInstance

end Acyclic

section Sum

variable {S : Type u} [CommRing S]

/-- Finite biproducts of cochain complexes of `S`-modules (an abelian category). -/
instance hasFiniteBiproducts_cochainComplex :
    HasFiniteBiproducts (CochainComplex (ModuleCat.{u} S) ℤ) :=
  Abelian.hasFiniteBiproducts

/-- tex L3846–3849: "Their direct sum, of any finite size, is still an integral contraction".
PROVED. -/
theorem contractible_biproduct {ι : Type} [Fintype ι] (K : ι → CochainComplex (ModuleCat.{u} S) ℤ)
    (h : ∀ i, Nonempty (Homotopy (𝟙 (K i)) 0)) :
    Nonempty (Homotopy (𝟙 (⨁ K)) 0) := by
  rw [← isZero_quotient_obj_iff]
  have hz : ∀ i, (quotient _ _).map (𝟙 (K i)) = 0 := fun i => by
    obtain ⟨hi⟩ := h i
    rw [eq_of_homotopy _ _ hi, Functor.map_zero]
  rw [IsZero.iff_id_eq_zero, ← (quotient _ _).map_id, ← biproduct.total, Functor.map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Category.id_comp (biproduct.ι K i), ← Category.assoc, Functor.map_comp,
    Functor.map_comp, hz i]
  simp

end Sum

section Functional

variable {S : Type u} [CommRing S]
variable {CU C' C : CochainComplex (ModuleCat.{u} S) ℤ}

/-- The paired functional `λ(w) = PD(w, ψ(c))` on `C_U^2` (tex L3742–3749, L3845–3849), for a
chain map `ψ : τ^* C_U → C_{U^⊥}` (a homotopy inverse `j⁻¹`) and a degree-one element `c` of
`τ^* C_U`. -/
noncomputable def pairedFunctional (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (ψ : C ⟶ C')
    (cz : C.X 1) : CU.X 2 →ₗ[S] S :=
  pd2.flip ((ψ.f 1).hom cz)

/-- Unfolding `pairedFunctional` (tex L3752–3754). PROVED. -/
theorem pairedFunctional_apply (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (ψ : C ⟶ C')
    (cz : C.X 1) (w : CU.X 2) : pairedFunctional pd2 ψ cz w = pd2 w ((ψ.f 1).hom cz) := rfl

/-- tex L3858–3859: "`d(j⁻¹c(z)) = j⁻¹c(dz) = 0` as a cochain identity". PROVED. -/
theorem zperp_cocycle (ψ : C ⟶ C') {cz : C.X 1} (hz : (C.d 1 2).hom cz = 0) :
    (C'.d 1 2).hom ((ψ.f 1).hom cz) = 0 := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f cz) (ψ.comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, hz, map_zero]

/-- tex L3860–3862: applying the duality to the cocycle `z^⊥` gives a closed element of
`Hom_S(C_U^2, S)`, i.e. `λ ∘ d = 0` on `C_U^1`. PROVED. -/
theorem pairedFunctional_closed (pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S)
    (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (ε : S)
    (hL : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (ψ : C ⟶ C') {cz : C.X 1} (hz : (C.d 1 2).hom cz = 0) (w : CU.X 1) :
    pairedFunctional pd2 ψ cz ((CU.d 1 2).hom w) = 0 := by
  rw [pairedFunctional_apply, hL, zperp_cocycle ψ hz, map_zero, mul_zero]

/-- Homotopic chain maps agree on a degree-one cocycle up to a coboundary (used at tex L3859–3860
and L3755–3758). PROVED. -/
theorem homotopy_apply_cocycle {X Y : CochainComplex (ModuleCat.{u} S) ℤ} {f g : X ⟶ Y}
    (H : Homotopy f g) {x : X.X 1} (hx : (X.d 1 2).hom x = 0) :
    (f.f 1).hom x - (g.f 1).hom x = (Y.d 0 1).hom ((H.hom 1 0).hom x) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) (H.comm 1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)] at h
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply, hx, map_zero, zero_add] at h
  rw [h]; abel

/-- tex L3859–3860: "its image differs from `c(z)` by an integral boundary". PROVED. -/
theorem image_zperp_sub_mem_boundary (e : HomotopyEquiv C' C) {cz : C.X 1}
    (hz : (C.d 1 2).hom cz = 0) :
    ∃ b : C.X 0, (e.hom.f 1).hom ((e.inv.f 1).hom cz) - cz = (C.d 0 1).hom b := by
  refine ⟨(e.homotopyInvHomId.hom 1 0).hom cz, ?_⟩
  rw [← homotopy_apply_cocycle e.homotopyInvHomId hz]
  simp

/-- Two homotopy inverses of the same chain map are homotopic: `ψ ≃ ψ j ψ' ≃ ψ'` (tex L3755–3757,
"The inverse is unique in the derived category"). -/
noncomputable def homotopyInvOfSameHom (e e' : HomotopyEquiv C' C) (h : e.hom = e'.hom) :
    Homotopy e.inv e'.inv :=
  ((e'.homotopyHomInvId.compLeft e.inv).symm.trans (Homotopy.ofEq (by
    rw [← Category.assoc, ← h]))).trans
    ((e.homotopyInvHomId.compRight e'.inv).trans (Homotopy.ofEq (by simp)))

/-- tex L3755–3758: the functionals built from two homotopy inverses of `j` differ by the
coboundary `w ↦ ε PD₃(dw, y)`, so they agree on `H²(C_U)`. PROVED. -/
theorem pairedFunctional_sub_eq_coboundary (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S)
    (pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S) (ε : S)
    (hL : ∀ w y, pd2 w ((C'.d 0 1).hom y) = ε * pd3 ((CU.d 2 3).hom w) y)
    (e e' : HomotopyEquiv C' C) (h : e.hom = e'.hom) {cz : C.X 1}
    (hz : (C.d 1 2).hom cz = 0) :
    ∃ y : C'.X 0, ∀ w : CU.X 2,
      pairedFunctional pd2 e.inv cz w - pairedFunctional pd2 e'.inv cz w =
        ε * pd3 ((CU.d 2 3).hom w) y := by
  refine ⟨((homotopyInvOfSameHom e e' h).hom 1 0).hom cz, fun w => ?_⟩
  rw [pairedFunctional_apply, pairedFunctional_apply, ← map_sub,
    homotopy_apply_cocycle _ hz, hL]

end Functional

/-! ### Manuscript nodes -/

/-- **`ConeContractionInverse`** (`ex:arith-paired-functional`, tex L3853–3858; also L3818–3825):
"represent the comparison on the bounded free models and contract its acyclic cone over `S`. The
cone contraction yields a chain map `j⁻¹` and homotopies `jj⁻¹ ≃ 1` and `j⁻¹j ≃ 1` over `S`."
For every commutative ring `S` and chain map `j` of cochain complexes of `S`-modules, a
contraction of the mapping cone of `j` gives a homotopy equivalence with forward map `j`.
Kind: PROVED. -/
def ConeContractionInverse : Prop :=
  ∀ (S : Type u) [CommRing S] (K L : CochainComplex (ModuleCat.{u} S) ℤ) (j : K ⟶ L),
    Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone j)) 0) →
      ∃ e : HomotopyEquiv K L, e.hom = j

theorem coneContractionInverse_proof : ConeContractionInverse.{u} :=
  fun _ _ _ _ j ⟨h⟩ => homotopyEquiv_of_cone_contractible j h

/-- **`BoundedAcyclicFreeContractible`** (`ex:arith-paired-functional`, tex L3790–3794): "its
bounded acyclic free cone is contractible, by splitting from its last nonzero term and proceeding
downwards". A cochain complex of free `S`-modules, zero outside `[a, b]`, exact in every degree,
is contractible. Kind: PROVED (`DEPARTURE` in proof route only: Mathlib's K-projectivity of
bounded-above projective complexes). -/
def BoundedAcyclicFreeContractible : Prop :=
  ∀ (S : Type u) [CommRing S] (K : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [∀ n, Module.Free S (K.X n)],
    K.Acyclic → Nonempty (Homotopy (𝟙 K) 0)

theorem boundedAcyclicFreeContractible_proof : BoundedAcyclicFreeContractible.{u} :=
  fun _ _ K a b _ _ _ hK => contractible_of_acyclic_free K a b hK

/-- **`QuasiIsoFreeHomotopyInverse`** (`ex:arith-paired-functional`, tex L3790–3792): "A
quasi-isomorphism between these bounded free models has an integral homotopy inverse". For
complexes of free `S`-modules zero outside `[a, b]`, every quasi-isomorphism `j` is the forward
map of a homotopy equivalence over `S`. Kind: PROVED (`DEPARTURE` in proof route only, as above). -/
def QuasiIsoFreeHomotopyInverse : Prop :=
  ∀ (S : Type u) [CommRing S] (K L : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ n, Module.Free S (K.X n)] [∀ n, Module.Free S (L.X n)] (j : K ⟶ L) [QuasiIso j],
    ∃ e : HomotopyEquiv K L, e.hom = j

theorem quasiIsoFreeHomotopyInverse_proof : QuasiIsoFreeHomotopyInverse.{u} :=
  fun _ _ _ _ a b _ _ _ _ _ _ j _ => homotopyEquiv_of_quasiIso_free a b j

/-- **`FiniteSumContractible`** (`ex:arith-paired-functional`, tex L3846–3849): "Their full local
complexes have the integral contractions displayed above. Their direct sum, of any finite size, is
still an integral contraction." A finite biproduct of contractible cochain complexes of
`S`-modules is contractible. Kind: PROVED. -/
def FiniteSumContractible : Prop :=
  ∀ (S : Type u) [CommRing S] (ι : Type) [Fintype ι] (K : ι → CochainComplex (ModuleCat.{u} S) ℤ),
    (∀ i, Nonempty (Homotopy (𝟙 (K i)) 0)) → Nonempty (Homotopy (𝟙 (⨁ K)) 0)

theorem finiteSumContractible_proof : FiniteSumContractible.{u} :=
  fun _ _ _ _ K h => contractible_biproduct K h

/-- **`IntegralClosedLift`** (`ex:arith-paired-functional`, tex L3850–3863, with L3752–3754): if
the comparison `j : C_{U^⊥} → τ^* C_U` over `S` has a contractible cone, and `z` is a degree-one
cocycle carried by the conjugate transport `c` to `τ^* C_U`, then there is an integral chain map
`j⁻¹` such that `z^⊥ = j⁻¹ c(z)` is a cocycle, `j(z^⊥) − c(z)` is an integral boundary, and the
functional `λ_z = PD(−, z^⊥)` on `C_U^2` is closed ("This proves the existence of an actual integral
closed lift, rather than only a lift after rationalization", tex L3862–3863). The duality enters by
the components `PD₁, PD₂` and their Leibniz rule (`DEPARTURE`, form only; see the module
docstring). Kind: PROVED. -/
def IntegralClosedLift : Prop :=
  ∀ (S : Type u) [CommRing S] (CU C' C Z : CochainComplex (ModuleCat.{u} S) ℤ) (j : C' ⟶ C)
    (c : Z ⟶ C) (z : Z.X 1) (pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S)
    (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (ε : S),
    Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone j)) 0) →
    (Z.d 1 2).hom z = 0 →
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y)) →
    ∃ ψ : C ⟶ C',
      (C'.d 1 2).hom ((ψ.f 1).hom ((c.f 1).hom z)) = 0 ∧
      (∃ b : C.X 0, (j.f 1).hom ((ψ.f 1).hom ((c.f 1).hom z)) - (c.f 1).hom z = (C.d 0 1).hom b) ∧
      ∀ w : CU.X 1, pairedFunctional pd2 ψ ((c.f 1).hom z) ((CU.d 1 2).hom w) = 0

theorem integralClosedLift_proof : IntegralClosedLift.{u} := by
  intro S _ CU C' C Z j c z pd1 pd2 ε ⟨h⟩ hz hL
  obtain ⟨e, rfl⟩ := homotopyEquiv_of_cone_contractible j h
  have hcz : (C.d 1 2).hom ((c.f 1).hom z) = 0 := by
    have h' := congrArg (fun f => ModuleCat.Hom.hom f z) (c.comm 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
    rw [h', hz, map_zero]
  exact ⟨e.inv, zperp_cocycle e.inv hcz, image_zperp_sub_mem_boundary e hcz,
    pairedFunctional_closed pd1 pd2 ε hL e.inv hcz⟩

/-- **`PairedFunctionalWellDefined`** (`ex:arith-paired-functional`, tex L3755–3758): "The inverse
is unique in the derived category, so representatives built at distinct localizations define the
same generic functional." For two homotopy inverses of the same comparison `j` and a degree-one
cocycle `c(z)`, the two functionals `PD(−, j⁻¹ c(z))` differ by a coboundary `w ↦ ε PD₃(dw, y)`;
hence they agree on `H²(C_U)`. Kind: PROVED. -/
def PairedFunctionalWellDefined : Prop :=
  ∀ (S : Type u) [CommRing S] (CU C' C : CochainComplex (ModuleCat.{u} S) ℤ)
    (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S) (ε : S)
    (e e' : HomotopyEquiv C' C) (cz : C.X 1),
    (∀ w y, pd2 w ((C'.d 0 1).hom y) = ε * pd3 ((CU.d 2 3).hom w) y) →
    e.hom = e'.hom → (C.d 1 2).hom cz = 0 →
    ∃ y : C'.X 0, ∀ w : CU.X 2,
      pairedFunctional pd2 e.inv cz w - pairedFunctional pd2 e'.inv cz w =
        ε * pd3 ((CU.d 2 3).hom w) y

theorem pairedFunctionalWellDefined_proof : PairedFunctionalWellDefined.{u} :=
  fun _ _ _ _ _ pd2 pd3 ε e e' _ hL h hz =>
    pairedFunctional_sub_eq_coboundary pd2 pd3 ε hL e e' h hz

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
