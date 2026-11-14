/-! ## leaf-fold2: g9-abvarbc (ZInQKernel/Contrib/AbVarBC/*.lean), copied; see mk_abvarbc.py -/

-- ===== ZInQKernel/Contrib/AbVarBC/Dim.lean
section LF2_AbVarBC_Dim

/-!
# Base change of abelian varieties, I: the dimension

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).
The proofs of §1-§2 are those of task g0-dim (`scratch/g0-dim/Dim.lean`, namespace `G0Dim`),
moved into the namespace `ZInQ.Contrib.AbVarBC` so that they cannot collide with a later copy.

Main results (Mathlib only, no hypothesis):
* `dim_baseChange_scheme`: for `X` locally of finite type over a field `K` and any field
  extension `L/K`, `dim (X ×_K L) = dim X` (Stacks 00P4, globalized).
* `PkgI3.AbVar.dim_baseChange`: `(A.baseChange L).dim = A.dim` for the project's abelian
  varieties (`ZInQKernel/HDecomp/Objects.lean`).
* `PkgI3.AbVar.dim_finite`: `A.dim` is a natural number.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Order TensorProduct

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Commutative algebra -/
/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange_scheme {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end ZInQ.Contrib.AbVarBC

/-! ## §3. The project's abelian varieties -/

namespace PkgI3.AbVar

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Dimension is invariant under base change** (Stacks 00P4; proved, no hypothesis). -/
theorem dim_baseChange {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L]
    [Algebra K L] : (A.baseChange L).dim = A.dim :=
  ZInQ.Contrib.AbVarBC.dim_baseChange_scheme L A.X.left A.X.hom

/-- **The dimension of an abelian variety is a natural number** (proved, no hypothesis). -/
theorem dim_finite {K : Type} [Field K] (A : PkgI3.AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact ZInQ.Contrib.AbVarBC.dim_finite A.X.left A.X.hom

end PkgI3.AbVar

end LF2_AbVarBC_Dim

-- ===== ZInQKernel/Contrib/AbVarBC/Points.lean
section LF2_AbVarBC_Points

/-!
# Base change of abelian varieties, II: points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).
§1 is task unram-tate's `scratch/unram-tate/BCPoints.lean` (namespace `UnramTate`), moved into the
namespace `ZInQ.Contrib.AbVarBC`. §2 is new.

For the project's abelian varieties (`PkgI3.AbVar`, `ZInQKernel/HDecomp/Objects.lean`):
* `bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω` (points of a base change), natural for
  `L`-automorphisms of `Ω` (`bcPt_galAct`);
* `extPt κ : A.Pt Ω →* A.Pt Ω₂` along a `K`-embedding of fields `κ : Ω →ₐ[K] Ω₂`, **injective**
  (`extPt_injective`: `Spec Ω₂ → Spec Ω` is faithfully flat and quasi-compact, hence an effective
  epimorphism, Mathlib's Stacks 023Q), and Galois-natural (`extPt_galAct`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Points of a base change (task unram-tate) -/

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr

/-! ## §2. Points over an extension of fields -/

section Ext

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-embedding `κ : Ω → Ω₂`. -/
noncomputable def extHom (κ : Ω →ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem extHom_left (κ : Ω →ₐ[K] Ω₂) :
    (extHom κ).left = Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) := rfl

/-- `Spec` of a map of fields is an epimorphism of schemes (faithfully flat, quasi-compact). -/
theorem epi_spec_map_field (κ : Ω →+* Ω₂) : Epi (Spec.map (CommRingCat.ofHom κ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom κ)) := by
    constructor
    intro y
    refine ⟨IsLocalRing.closedPoint Ω₂, Subsingleton.elim _ _⟩
  haveI : Flat (Spec.map (CommRingCat.ofHom κ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [κ]
    change Module.Flat Ω Ω₂
    infer_instance
  infer_instance

instance epi_extHom (κ : Ω →ₐ[K] Ω₂) : Epi (extHom κ) := by
  haveI : Epi ((Over.forget _).map (extHom κ)) := epi_spec_map_field (κ : Ω →+* Ω₂)
  exact (Over.forget _).epi_of_epi_map this

/-- **Points along a field extension**: `A(Ω) → A(Ω₂)`, `p ↦ p ∘ Spec κ`. -/
noncomputable def extPt (κ : Ω →ₐ[K] Ω₂) : A.Pt Ω →* A.Pt Ω₂ where
  toFun p := extHom κ ≫ p
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem extPt_apply (κ : Ω →ₐ[K] Ω₂) (p : A.Pt Ω) : extPt A κ p = extHom κ ≫ p := rfl

/-- **`A(Ω) → A(Ω₂)` is injective.** -/
theorem extPt_injective (κ : Ω →ₐ[K] Ω₂) : Function.Injective (extPt A κ) :=
  fun _ _ h => (cancel_epi (extHom κ)).1 h

/-- `extPt κ` carries the action of `τ ∈ Aut_K(Ω)` to that of `σ ∈ Aut_K(Ω₂)` when
`κ ∘ τ = σ ∘ κ`. -/
theorem extPt_galAct (κ : Ω →ₐ[K] Ω₂) (τ : Ω ≃ₐ[K] Ω) (σ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, κ (τ x) = σ (κ x)) (p : A.Pt Ω) :
    extPt A κ (A.galAct τ p) = A.galAct σ (extPt A κ p) := by
  show extHom κ ≫ PkgI3.AbVar.galHom τ ≫ p = PkgI3.AbVar.galHom σ ≫ extHom κ ≫ p
  have hsq : extHom κ ≫ PkgI3.AbVar.galHom τ = PkgI3.AbVar.galHom σ ≫ extHom κ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x)
  rw [← Category.assoc, ← Category.assoc, hsq]

end Ext

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Points

-- ===== ZInQKernel/Contrib/AbVarBC/Tate.lean
section LF2_AbVarBC_Tate

/-!
# Base change of abelian varieties, III: Tate modules

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

For `A : PkgI3.AbVar K` (the kernel's abelian varieties, `ZInQKernel/HDecomp/Objects.lean`), a
field extension `L/K` and a `K`-embedding `κ : K̄ → L̄`:
* `ptBC A κ : A(K̄) →* A_L(L̄)` is injective (`ptBC_injective`) and Galois-natural
  (`ptBC_galAct`: if `κ ∘ τ = σ ∘ κ` for `τ ∈ G_K`, `σ ∈ G_L`);
* `tateBC A ℓ κ : T_ℓ(A) →ₗ[ℤ_ℓ] T_ℓ(A_L)` is injective and Galois-natural (`tateBC_galT`);
* it is bijective as soon as the `ℓ`-power torsion of `A_L(L̄)` comes from `A(K̄)`
  (`tateBC_bijective_of_torsionDescends`), or under leaf T26 `PkgI3.TateModuleFree`
  (`tateBC_bijective_of_tateModuleFree`, through the kernel glue `PkgI3.Tate.map_bijective` and
  `dim A_L = dim A`);
* `vBC A ℓ κ hb : V_ℓ(A_L) ≃ₗ[ℚ_ℓ] V_ℓ(A)` with `vBC_galRep`: it intertwines `ρ_{A_L}(σ)` with
  `ρ_A(τ)`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Tate modules along an injective map whose `ℓ`-power torsion is in the image -/

section TateGen

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- If `φ : M → N` is injective and every `ℓ`-power torsion element of `N` is in its image,
`T_ℓ(φ)` is bijective. -/
theorem tate_map_bijective_of_torsion (φ : M →+ N) (hφ : Function.Injective φ)
    (htors : ∀ (n : ℕ) (q : N), (ℓ ^ n) • q = 0 → ∃ p, φ p = q) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) φ) := by
  refine ⟨PkgI3.Tate.map_injective φ hφ, fun x => ?_⟩
  have hx : ∀ n, ∃ p, φ p = x.1 n := fun n =>
    htors n (x.1 n) (PkgI3.Tate.pow_smul_eq_zero x.2 n)
  choose y hy using hx
  refine ⟨⟨y, ?_, fun n => ?_⟩, ?_⟩
  · apply hφ
    rw [hy, x.2.1, map_zero]
  · apply hφ
    rw [map_nsmul, hy, hy, x.2.2 n]
  · apply Subtype.ext
    funext n
    exact hy n

end TateGen

/-! ## §2. Points and Tate modules of a base change -/

/-- An element of `G_K` as an automorphism of `K̄`. -/
abbrev galK {K : Type*} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)

/-- `A(K̄) → A(L̄) ≅ A_L(L̄)`. -/
noncomputable def ptBC : A.Pt (AlgebraicClosure K) →* (A.baseChange L).Pt (AlgebraicClosure L) :=
  (bcPt A (AlgebraicClosure L)).symm.toMonoidHom.comp (extPt A κ)

theorem ptBC_injective : Function.Injective (ptBC A κ) :=
  (bcPt A (AlgebraicClosure L)).symm.injective.comp (extPt_injective A κ)

/-- Galois-naturality of `ptBC`. -/
theorem ptBC_galAct (τ : Field.absoluteGaloisGroup K) (σ : Field.absoluteGaloisGroup L)
    (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (p : A.Pt (AlgebraicClosure K)) :
    ptBC A κ (A.galAct τ p) = (A.baseChange L).galAct σ (ptBC A κ p) := by
  have h1 := extPt_galAct A κ τ ((σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L).restrictScalars K)
    h p
  have h2 := bcPt_galAct A (AlgebraicClosure L) σ
    ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [MulEquiv.apply_symm_apply] at h2
  change (bcPt A (AlgebraicClosure L)).symm (extPt A κ (A.galAct τ p)) =
    (A.baseChange L).galAct σ ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [h1, ← h2, MulEquiv.symm_apply_apply]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) → T_ℓ(A_L)`. -/
noncomputable def tateBC : A.T ℓ →ₗ[ℤ_[ℓ]] (A.baseChange L).T ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (ptBC A κ))

theorem tateBC_injective : Function.Injective (tateBC A κ ℓ) :=
  PkgI3.Tate.map_injective _ (ptBC_injective A κ)

/-- Galois-naturality of `tateBC`. -/
theorem tateBC_galT (τ : Field.absoluteGaloisGroup K) (σ : Field.absoluteGaloisGroup L)
    (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (x : A.T ℓ) :
    tateBC A κ ℓ (A.galT τ x) = (A.baseChange L).galT σ (tateBC A κ ℓ x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (ptBC_galAct A κ τ σ h (Additive.toMul (x.1 n)))

/-- **Descent of `ℓ`-power torsion** (the content of "`A[ℓⁿ]` is finite étale"): every
`ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`. -/
def TorsionDescends : Prop :=
  ∀ (n : ℕ) (q : (A.baseChange L).Pt (AlgebraicClosure L)), q ^ (ℓ ^ n) = 1 →
    ∃ p, ptBC A κ p = q

theorem tateBC_bijective_of_torsionDescends (h : TorsionDescends A κ ℓ) :
    Function.Bijective (tateBC A κ ℓ) :=
  tate_map_bijective_of_torsion _ (ptBC_injective A κ) fun n q hq => h n (Additive.toMul q) hq

/-- **Under leaf T26 (`TateModuleFree`), `T_ℓ(A) → T_ℓ(A_L)` is bijective** (`ℓ ≠ char K`). -/
theorem tateBC_bijective_of_tateModuleFree (hT : PkgI3.TateModuleFree) (hℓ : (ℓ : K) ≠ 0) :
    Function.Bijective (tateBC A κ ℓ) := by
  have hℓL : (ℓ : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hℓ
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓ
  obtain ⟨-, hfinL, hrkL⟩ := hT L (A.baseChange L) ℓ hℓL
  rw [PkgI3.AbVar.dim_baseChange] at hrkL
  have hr : Module.finrank ℤ_[ℓ] (A.T ℓ) = Module.finrank ℤ_[ℓ] ((A.baseChange L).T ℓ) := by
    have := hrk.trans hrkL.symm
    exact_mod_cast this
  exact PkgI3.Tate.map_bijective _ (ptBC_injective A κ) hr

/-- **`V_ℓ(A_L) ≅ V_ℓ(A)`**, from a bijective `tateBC`. -/
noncomputable def vBC (hb : Function.Bijective (tateBC A κ ℓ)) :
    (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  ((LinearEquiv.ofBijective (tateBC A κ ℓ) hb).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).symm

/-- `vBC` intertwines `ρ_{A_L}(σ)` with `ρ_A(τ)` when `κ ∘ τ = σ ∘ κ`. -/
theorem vBC_galRep (hb : Function.Bijective (tateBC A κ ℓ)) (τ : Field.absoluteGaloisGroup K)
    (σ : Field.absoluteGaloisGroup L) (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (v : (A.baseChange L).V ℓ) :
    vBC A κ ℓ hb ((A.baseChange L).galRep ℓ σ v) = A.galRep ℓ τ (vBC A κ ℓ hb v) := by
  set e := (LinearEquiv.ofBijective (tateBC A κ ℓ) hb).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ with he
  have key : ∀ w : A.V ℓ, e (A.galRep ℓ τ w) = (A.baseChange L).galRep ℓ σ (e w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a t =>
      change e ((A.galT τ).baseChange ℚ_[ℓ] (a ⊗ₜ t)) =
        ((A.baseChange L).galT σ).baseChange ℚ_[ℓ] (e (a ⊗ₜ t))
      rw [LinearMap.baseChange_tmul, he, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        tateBC_galT A κ ℓ τ σ h]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  show e.symm ((A.baseChange L).galRep ℓ σ v) = A.galRep ℓ τ (e.symm v)
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, key, LinearEquiv.apply_symm_apply]

end BC

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Tate

-- ===== ZInQKernel/Contrib/AbVarBC/Torsion.lean
section LF2_AbVarBC_Torsion

/-!
# Base change of abelian varieties, V: descent of torsion points from finiteness of `[N]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

* `mem_range_of_isIntegral`: an element of a field `Ω₂ ⊇ K` integral over `K` lies in the image of
  any `K`-embedding `K̄ → Ω₂`.
* `exists_lift_of_isFinite`: for `g : Z → Spec K` finite and `κ : Ω → Ω₂` a `K`-embedding with
  `Ω` algebraically closed, every `Ω₂`-point of `Z` over `K` comes from an `Ω`-point (STANDARD:
  `Z = Spec R`, `R` finite over `K`, and the image of `R → Ω₂` is algebraic over `K`).
* `torsionDescends_of_isFinite`: if `[ℓⁿ] : A → A` is finite for every `n`, then
  `TorsionDescends A κ ℓ` (the `ℓ`-power torsion points of `A_L(L̄)` come from `A(K̄)`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Algebra -/

/-- An element integral over `K` lies in the image of any `K`-embedding of an algebraically
closed field. -/
theorem mem_range_of_isIntegral {K Ω Ω₂ : Type*} [Field K] [Field Ω] [IsAlgClosed Ω] [Field Ω₂]
    [Algebra K Ω] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) {x : Ω₂} (hx : IsIntegral K x) :
    x ∈ (κ : Ω →+* Ω₂).range := by
  have hf0 : (minpoly K x).map (algebraMap K Ω) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hx)
  refine Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) hf0 ?_
  rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  exact minpoly.aeval K x

/-! ## §2. Points of a scheme finite over a field -/

/-- **Points of a finite `K`-scheme over an algebraically closed field.** -/
theorem exists_lift_of_isFinite {K : Type} [Field K] {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω]
    [Field Ω₂] [Algebra K Ω] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) {Z : Scheme.{0}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (q : Spec (CommRingCat.of Ω₂) ⟶ Z)
    (hq : q ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ Z,
      Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p = q ∧
        p ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  let e := Z.isoSpec
  let φ := Spec.preimage (q ≫ e.hom)
  let θ := Spec.preimage (e.inv ≫ g)
  have hφ : Spec.map φ = q ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ g := Spec.map_preimage _
  have hθfin : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω₂) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, hq]
  -- every element of the image of `φ` is integral over `K`
  have hint : ∀ r, IsIntegral K (φ.hom r) := by
    intro r
    have hr : θ.hom.IsIntegralElem r := hθfin.to_isIntegral r
    obtain ⟨P, hPm, hP⟩ := hr
    refine ⟨P, hPm, ?_⟩
    have := congrArg φ.hom hP
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.eval₂_eq_eval_map] at this ⊢
    have h2 : φ.hom.comp θ.hom = algebraMap K Ω₂ := congrArg CommRingCat.Hom.hom hcomp
    rw [h2] at this
    exact this
  choose ψ0 hψ0 using fun r => mem_range_of_isIntegral κ (hint r)
  have hκinj : Function.Injective (κ : Ω →+* Ω₂) := (κ : Ω →+* Ω₂).injective
  let ψ : Γ(Z, ⊤) →+* Ω :=
    { toFun := ψ0
      map_one' := hκinj (by rw [hψ0, map_one, map_one])
      map_mul' := fun a b => hκinj (by rw [hψ0, map_mul, map_mul, hψ0, hψ0])
      map_zero' := hκinj (by rw [hψ0, map_zero, map_zero])
      map_add' := fun a b => hκinj (by rw [hψ0, map_add, map_add, hψ0, hψ0]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (κ : Ω →+* Ω₂) = φ := by
    ext r
    exact hψ0 r
  have hlift : Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ (Spec.map (CommRingCat.ofHom ψ) ≫
      e.inv) = q := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, hφ, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ e.inv, hlift, ?_⟩
  haveI := epi_spec_map_field (κ : Ω →+* Ω₂)
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)))).1
  rw [← Category.assoc, hlift, hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, κ.comp_algebraMap]

/-! ## §3. Torsion points of a base change -/

section Tors

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

/-- `q ≫ [N] = q ^ N` for `[N] = ((N : ℤ) : End A).hom`. -/
theorem comp_natCast_hom {T : Over (Spec (CommRingCat.of K))} (q : T ⟶ A.X) (N : ℕ) :
    q ≫ (((N : ℤ) : PkgI3.AbVar.End A)).hom = q ^ N := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, Int.cast_zero, PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one, pow_zero]
  | succ N ih =>
    rw [Nat.cast_succ, Int.cast_add, Int.cast_one, PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul, ih,
      pow_succ]
    congr 1

variable {L : Type} [Field L] [Algebra K L]

/-- **Torsion descent from finiteness of `[ℓⁿ]`.** If `[ℓⁿ] : A → A` is a finite morphism for
every `n`, then every `ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`. -/
theorem torsionDescends_of_isFinite (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : ∀ n : ℕ, IsFinite ((((ℓ ^ n : ℕ) : ℤ) : PkgI3.AbVar.End A).hom.left)) :
    TorsionDescends A κ ℓ := by
  intro n q hq
  set N := ℓ ^ n with hN
  set q₀ := bcPt A (AlgebraicClosure L) q with hq₀
  have h0 : q₀ ^ N = 1 := by rw [hq₀, ← map_pow, hq, map_one]
  have h1 : q₀ ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by rw [comp_natCast_hom, h0]
  haveI := hfin n
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have hq0 : q₀.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L))) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  have hfN : IsFinite fN := hfin n
  let z : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ pullback fN e :=
    pullback.lift q₀.left (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L)))) hq0
  obtain ⟨p0, hp0, hp0g⟩ := exists_lift_of_isFinite κ (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let p : A.Pt (AlgebraicClosure K) := Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl)
  refine ⟨p, ?_⟩
  change (bcPt A (AlgebraicClosure L)).symm (extPt A κ p) = q
  rw [MulEquiv.symm_apply_eq]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : AlgebraicClosure K →+* AlgebraicClosure L)) ≫
    p0 ≫ pullback.fst fN e = q₀.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

end Tors

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Torsion

-- ===== ZInQKernel/Contrib/AbVarBC/Mul.lean
section LF2_AbVarBC_Mul

/-!
# mul-rigidity: the textbook leaf `MulIsogeny` reduced to smaller named Props

Copyright: this file is part of the fork Deicyde/diophantine-z-q. It is task mul-rigidity's
`scratch/mul-rigidity/Mul.lean` (2026-11-13), copied by task g9-abvarbc into `Contrib` with the
namespaces `MulRigidity` and `G0FibreSimple` moved under `ZInQ.Contrib.AbVarBC` (no other change),
so that `Contrib/AbVarBC/G9Instance.lean` can use `MulIsogeny`, `KerUnitOpen` and the two
cotangent glue statements.

`MulIsogeny` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4″). Mathlib
proves "finite and surjective" from local properties of `[n]`:
* proper (`A` proper) and locally quasi-finite give finite (Zariski's main theorem, Mathlib
  `IsFinite.of_isProper_of_locallyQuasiFinite`, Stacks 02LS);
* a locally quasi-finite closed self-map of an irreducible Noetherian scheme is surjective
  (`surjective_of_lqf_self`, generic-point orbit), so `QuasiFiniteEndSurjective` is proved;
* formally unramified + locally of finite type gives locally quasi-finite;
* `[n]` is formally unramified once the unit section of `A[n]` is an open immersion
  (`diagonal_isPullback`: `Δ_f` is a base change of that section).
Chain: `KerUnitOpenOfCotangentSurj` + `CotangentMulN` (glue, unproved) ⇒ `KerUnitOpen` (leaf,
implied by the published `MulEtale`) ⇒ `MulUnramified` ⇒ `MulIsogeny`.
-/

noncomputable section

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Formally unramified and locally of finite type implies locally quasi-finite (Mathlib's algebra
instance `Algebra.QuasiFinite` from `EssFiniteType` and `FormallyUnramified`, made affine-local). -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : (f.appLE U V e).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance U V e
  have h2 : (f.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

variable {K : Type} [Field K]

/-- A `K`-morphism between abelian varieties is proper (source proper, target separated). -/
theorem isProper_left (A B : PkgI3.AbVar K) (f : A.X ⟶ B.X) : IsProper f.left := by
  have : IsProper (f.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp f.left B.X.hom

/-- **Glue.** A locally quasi-finite open `K`-endomorphism of an abelian variety is finite and
surjective. -/
theorem isIsogenyMor_of_lqf_of_isOpenMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    [LocallyQuasiFinite f.left] (ho : IsOpenMap f.left.base) : PkgI3.AbVar.IsIsogenyMor f := by
  have := isProper_left A A f
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite f.left, ⟨?_⟩⟩
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have hcl : IsClopen (Set.range f.left.base) :=
    ⟨f.left.isClosedMap.isClosed_range, ho.isOpen_range⟩
  have hne : (Set.range f.left.base).Nonempty :=
    ⟨_, ⟨η[A.X].left (IsLocalRing.closedPoint K), rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Under a locally quasi-finite morphism, a strict specialization maps to two distinct points
(the fibres are discrete, Mathlib `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem ne_of_specializes_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : f x ≠ f y := by
  intro heq
  have hd := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  let x' : (f.base ⁻¹' {f y} : Set X) := ⟨x, heq⟩
  let y' : (f.base ⁻¹' {f y} : Set X) := ⟨y, rfl⟩
  have h' : x' ⤳ y' := (subtype_specializes_iff x' y').mpr hxy
  exact hne (congrArg Subtype.val h'.eq)

/-- **A locally quasi-finite closed self-map of an irreducible Noetherian scheme is
surjective.** If `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ f ξ ⤳ f² ξ ⤳ ⋯` are strict
specializations (continuity, and `ne_of_specializes_of_lqf`), so the closures `cl{fᵐ ξ}` form a
strictly decreasing chain of closed sets, contradicting Noetherianity. So `ξ ∈ range f`, which is
closed, hence everything. -/
theorem surjective_of_lqf_self {X : Scheme} [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    Function.Surjective f.base := by
  set ξ := genericPoint X
  have hξ : ∀ x : X, ξ ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hfix : f ξ = ξ := by
    by_contra hne
    let s : ℕ → X := fun m => (f.base)^[m] ξ
    have hs : ∀ m, s m ⤳ s (m + 1) ∧ s m ≠ s (m + 1) := by
      intro m
      induction m with
      | zero => exact ⟨hξ _, fun h => hne h.symm⟩
      | succ m ih =>
        have e1 : s (m + 1) = f (s m) := Function.iterate_succ_apply' _ _ _
        have e2 : s (m + 1 + 1) = f (s (m + 1)) := Function.iterate_succ_apply' _ _ _
        rw [e1, e2]
        exact ⟨ih.1.map f.base.hom.continuous, ne_of_specializes_of_lqf f ih.1 ih.2⟩
    let c : ℕ → TopologicalSpace.Closeds X := fun m => ⟨closure {s m}, isClosed_closure⟩
    have hc' : StrictAnti c := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      refine lt_of_le_of_ne ?_ ?_
      · change closure {s (m + 1)} ⊆ closure {s m}
        exact specializes_iff_closure_subset.mp (hs m).1
      · intro h
        have h2 : closure {s (m + 1)} = closure {s m} := congrArg SetLike.coe h
        exact (hs m).2 (inseparable_iff_closure_eq.mpr h2.symm).eq
    exact not_strictAnti_of_wellFoundedLT c hc'
  intro y
  have hy : y ∈ closure {ξ} := specializes_iff_mem_closure.mp (hξ y)
  exact (hc.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨ξ, hfix⟩)) hy

end ZInQ.Contrib.AbVarBC.MulRigidity

namespace ZInQ.Contrib.AbVarBC.G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end ZInQ.Contrib.AbVarBC.G0FibreSimple

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Leaf (Mumford, *Abelian varieties*, §4 Application 2 and §6: `n_X` is separable when
`char k ∤ n`; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2: `n_A` is étale iff
`char k ∤ n`; locators UNVERIFIED).** In characteristic `0`, `[n]` is étale for `n ≠ 0`. A
consequence of the published statement (only characteristic `0`). -/
def MulEtale : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    Etale ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (the infinitesimal half of `MulEtale`; Mumford §4: `d(n_X) = n` on the tangent space
at `0`, so `n_X^* ω = n ω` for invariant differentials; locator UNVERIFIED).** In characteristic
`0`, `[n]` is formally unramified (`Ω_{[n]} = 0`) for `n ≠ 0`. Implied by `MulEtale`
(`mulUnramified_of_mulEtale`). -/
def MulUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    FormallyUnramified ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (dimension theory; Mumford §4 / Milne, *Abelian varieties*, Prop. 8.1: a homomorphism
of abelian varieties of the same dimension with finite kernel is surjective, an isogeny; locators
UNVERIFIED).** A locally quasi-finite endomorphism of an abelian variety is surjective
(any characteristic). -/
def QuasiFiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : PkgI3.AbVar.End A),
    LocallyQuasiFinite f.hom.left → Surjective f.hom.left

theorem mulUnramified_of_mulEtale (h : MulEtale) : MulUnramified := by
  intro k _ _ A n hn
  have := h k A n hn
  infer_instance

/-- **`MulIsogeny` from `MulEtale`** (glue proved here). -/
theorem mulIsogeny_of_mulEtale (h : MulEtale) : G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact isIsogenyMor_of_lqf_of_isOpenMap A _ (Scheme.Hom.isOpenMap _)

/-- **`MulIsogeny` from `MulUnramified` and `QuasiFiniteEndSurjective`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified (h1 : MulUnramified) (h2 : QuasiFiniteEndSurjective) :
    G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h1 k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, h2 k A _ inferInstance⟩

/-- **`QuasiFiniteEndSurjective` holds** (proved from Mathlib; it is not a leaf). -/
theorem quasiFiniteEndSurjective : QuasiFiniteEndSurjective := by
  intro k _ A f hf
  have := isProper_left A A f.hom
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsNoetherian A.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.X.hom }
  exact ⟨surjective_of_lqf_self f.hom.left f.hom.left.isClosedMap⟩

/-- **`MulIsogeny` from the single leaf `MulUnramified`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified' (h : MulUnramified) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified h quasiFiniteEndSurjective

end ZInQ.Contrib.AbVarBC.MulRigidity


/-! ## `MulUnramified` reduced to a statement at the origin of the kernel `A[n]` -/

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The unit section `Spec K → ker f = A ×_{f, A, e} Spec K` of the kernel of a homomorphism. -/
def kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    𝟙_ (Over (Spec (.of K))) ⟶ pullback f η[A.X] :=
  pullback.lift η[A.X] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

/-- `(x, y) ↦ x⁻¹ y : A ×_{f, A, f} A → ker f`. -/
def diffKer (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    pullback f f ⟶ pullback f η[A.X] :=
  pullback.lift ((pullback.fst f f)⁻¹ * pullback.snd f f) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel, Hom.one_def])

/-- **The diagonal of a homomorphism `f` is the base change of the unit section of `ker f`**
along `(x, y) ↦ x⁻¹ y` (the square is cartesian: `x⁻¹ y = e ⇔ x = y`). -/
theorem diagonal_isPullback (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsPullback (toUnit A.X) (pullback.diagonal f) (kerUnit A f) (diffKer A f) := by
  have key : ∀ {T : Over (Spec (.of K))} (a : T ⟶ pullback f f),
      a ≫ diffKer A f ≫ pullback.fst f η[A.X] = (a ≫ pullback.fst f f)⁻¹ * (a ≫ pullback.snd f f) := by
    intro T a
    simp only [diffKer, pullback.lift_fst, MonObj.comp_mul, GrpObj.comp_inv]
  refine IsPullback.flip ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst f f)
    ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, key, pullback.diagonal_fst, pullback.diagonal_snd, inv_mul_cancel,
        Category.assoc]
      simp only [kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  · intro c
    have hc := congrArg (· ≫ pullback.fst f η[A.X]) c.condition
    simp only [Category.assoc] at hc
    simp only [kerUnit, pullback.lift_fst] at hc
    rw [key, toUnit_unique c.snd (toUnit _), ← Hom.one_def, inv_mul_eq_one] at hc
    apply pullback.hom_ext
    · simp
    · simp [hc]
  · intro c
    exact toUnit_unique _ _
  · intro c m hm _
    rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- **Glue.** If the unit section of `ker f` is an open immersion, the homomorphism `f` is formally
unramified (its diagonal is an open immersion, as a base change of the unit section). -/
theorem formallyUnramified_of_kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f]
    (h : IsOpenImmersion (kerUnit A f).left) : FormallyUnramified f.left := by
  have hP := (Over.forget _).map_isPullback (diagonal_isPullback A f)
  have h1 : IsOpenImmersion (pullback.diagonal f).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hP h
  let e := PreservesPullback.iso (Over.forget (Spec (.of K))) f f
  have he : pullback.diagonal f.left = (pullback.diagonal f).left ≫ e.hom := by
    apply pullback.hom_ext
    · rw [pullback.diagonal_fst, Category.assoc]
      erw [PreservesPullback.iso_hom_fst]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.fst f f).left
      rw [← Over.comp_left, pullback.diagonal_fst]
      rfl
    · rw [pullback.diagonal_snd, Category.assoc]
      erw [PreservesPullback.iso_hom_snd]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.snd f f).left
      rw [← Over.comp_left, pullback.diagonal_snd]
      rfl
  have : IsOpenImmersion (pullback.diagonal f.left) := by rw [he]; infer_instance
  infer_instance

/-- **Leaf (Mumford, *Abelian varieties*, §4, Application 2 and §6: `A[n]` is étale, of order
`n^{2g}`, when `char k ∤ n`; equivalently `d[n] = n` on the tangent space at `0`; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Thm 8.2; locators UNVERIFIED).** In characteristic `0`, for
`n ≠ 0`, the unit section of the kernel `A[n] = A ×_{[n], A, e} Spec k` is an open immersion
(`A[n]` is unramified over `k` at the origin: its tangent space there, `ker(n · : Lie A → Lie A)`,
vanishes). A consequence of "`A[n]` is étale over `k`" (a section of an étale separated morphism
is an open immersion; `kerUnitOpen_of_mulEtale`). -/
def KerUnitOpen : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    IsOpenImmersion (kerUnit A ((n : PkgI3.AbVar.End A).hom)).left

/-- A section of a formally unramified morphism locally of finite type is an open immersion
(Stacks 024T; from Mathlib's `isOpenImmersion_diagonal` and
`MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`). -/
theorem isOpenImmersion_of_section {X Y : Scheme} (s : Y ⟶ X) (q : X ⟶ Y)
    [FormallyUnramified q] [LocallyOfFiniteType q] (h : s ≫ q = 𝟙 _) : IsOpenImmersion s := by
  set gr : Y ⟶ pullback (s ≫ q) q := pullback.lift (𝟙 Y) s (by simp)
  have e : s = gr ≫ pullback.snd _ _ := by simp [gr]
  rw [e]
  have h1 : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback s q)
      (FormallyUnramified.isOpenImmersion_diagonal q)
  have h2 : IsOpenImmersion (pullback.snd (s ≫ q) q) :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _
      (by rw [h]; exact (inferInstance : IsOpenImmersion (𝟙 Y)))
  infer_instance

/-- **`KerUnitOpen` is a consequence of `MulEtale`** (so it is implied by the published
statement): the kernel is a base change of `[n]`, hence étale over `k`, and its unit section is a
section of an étale morphism. -/
theorem kerUnitOpen_of_mulEtale (h : MulEtale) : KerUnitOpen := by
  intro k _ _ A n hn
  have hE : Etale ((n : PkgI3.AbVar.End A).hom).left := h k A n hn
  have hP := (Over.forget _).map_isPullback
    (IsPullback.of_hasPullback ((n : PkgI3.AbVar.End A).hom) η[A.X])
  have : Etale (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hP hE
  refine isOpenImmersion_of_section _ (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left ?_
  rw [← Over.comp_left]
  simp [kerUnit]

/-- `MulUnramified` from `KerUnitOpen` (glue proved here). -/
theorem mulUnramified_of_kerUnitOpen (h : KerUnitOpen) : MulUnramified := by
  intro k _ _ A n hn
  exact formallyUnramified_of_kerUnit A _ (h k A n hn)

/-- **`MulIsogeny` from the single leaf `KerUnitOpen`.** -/
theorem mulIsogeny_of_kerUnitOpen (h : KerUnitOpen) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified' (mulUnramified_of_kerUnitOpen h)

end ZInQ.Contrib.AbVarBC.MulRigidity


/-! ## `KerUnitOpen` reduced to two glue statements on the cotangent space at the origin -/

namespace ZInQ.Contrib.AbVarBC.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The origin of `A`, as a point of the underlying space. -/
def origin (A : PkgI3.AbVar K) : A.X.left := η[A.X].left (IsLocalRing.closedPoint K)

theorem map_origin (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    f.left (origin A) = origin A := by
  have h := congrArg (fun g : 𝟙_ (Over (Spec (.of K))) ⟶ A.X => g.left) (IsMonHom.one_hom f)
  simp only [Over.comp_left] at h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g : (𝟙_ (Over (Spec (.of K)))).left ⟶ A.X.left => g (IsLocalRing.closedPoint K)) h)

/-- The local ring `𝒪_{A,0}` at the origin. -/
abbrev O0 (A : PkgI3.AbVar K) : CommRingCat := A.X.left.presheaf.stalk (origin A)

/-- The local endomorphism `f^♯ : 𝒪_{A,0} → 𝒪_{A,0}` of a homomorphism `f` (which fixes `0`). -/
def stalkEndo (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : O0 A ⟶ O0 A :=
  (A.X.left.presheaf.stalkCongr (Inseparable.of_eq (map_origin A f).symm)).hom ≫
    f.left.stalkMap (origin A)

instance (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : IsLocalHom (stalkEndo A f).hom := by
  unfold stalkEndo
  rw [CommRingCat.hom_comp]
  infer_instance

/-- The cotangent map `m₀/m₀² → m₀/m₀²` of a homomorphism `f` at the origin. -/
def cotangentMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsLocalRing.CotangentSpace (O0 A) →ₗ[ℤ] IsLocalRing.CotangentSpace (O0 A) :=
  Ideal.mapCotangent _ _ (stalkEndo A f).hom.toIntAlgHom (fun x hx => by
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (isUnit_of_map_unit (stalkEndo A f).hom x hu))

/-- **Glue (commutative algebra of the fibre `ker f`; Nakayama).** For a homomorphism `f : A → A`
over `k` whose cotangent map at the origin is surjective, the unit section of `ker f` is an open
immersion. *Why true* (STANDARD): `𝒪_{ker f, 0} = 𝒪_{A,0} / f^♯(m₀)𝒪_{A,0}` (the fibre of `f`
over the rational point `0`), so surjectivity gives `m₀ = f^♯(m₀)𝒪 + m₀²`, hence
`m₀ = f^♯(m₀)𝒪` by Nakayama, so `𝒪_{ker f, 0} = k`; a rational point of a Noetherian scheme with
local ring a field is isolated, and the open point is `Spec k`. Glue, unproved. -/
def KerUnitOpenOfCotangentSurj : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : A.X ⟶ A.X) [IsMonHom f],
    Function.Surjective (cotangentMap A f) → IsOpenImmersion (kerUnit A f).left

/-- **Glue (the group law to first order; Mumford §4, `d(n_X) = n`, UNVERIFIED locator).** The
cotangent map of `[n]` at the origin is multiplication by `n`, for every `n ∈ ℤ` and in every
characteristic. *Why true* (STANDARD): the unit axioms give `μ^♯(φ) ≡ φ ⊗ 1 + 1 ⊗ φ` modulo
`m ⊗ m` on cotangent spaces, so the cotangent map of `f * g = μ ∘ (f, g)` is the sum of those of
`f` and `g`; induct on `n`. Glue, unproved. -/
def CotangentMulN : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ),
    cotangentMap A ((n : PkgI3.AbVar.End A).hom) = n • LinearMap.id

/-- The residue field at the origin has characteristic `0` when `k` does. -/
theorem charZero_residueField [CharZero K] (A : PkgI3.AbVar K) :
    CharZero (IsLocalRing.ResidueField (O0 A)) := by
  let φ : K →+* IsLocalRing.ResidueField (O0 A) :=
    (IsLocalRing.residue (O0 A)).comp ((A.X.left.presheaf.Γgerm (origin A)).hom.comp
      ((A.X.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).mp inferInstance

/-- **`KerUnitOpen` from the two glue statements** (proved here: in characteristic `0`,
multiplication by `n ≠ 0` is bijective on the cotangent space, a vector space over the residue
field). -/
theorem kerUnitOpen_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    KerUnitOpen := by
  intro k _ _ A n hn
  apply h1
  rw [h2]
  have := charZero_residueField A
  have hn' : (n : IsLocalRing.ResidueField (O0 A)) ≠ 0 := Int.cast_ne_zero.mpr hn
  intro v
  refine ⟨((n : IsLocalRing.ResidueField (O0 A))⁻¹) • v, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply,
    ← Int.cast_smul_eq_zsmul (IsLocalRing.ResidueField (O0 A)), smul_smul, mul_inv_cancel₀ hn',
    one_smul]

/-- **`MulIsogeny` from glue alone**: the two cotangent-space glue statements imply it, with no
literature leaf. -/
theorem mulIsogeny_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_kerUnitOpen (kerUnitOpen_of_cotangent h1 h2)

end ZInQ.Contrib.AbVarBC.MulRigidity



end

end LF2_AbVarBC_Mul

-- ===== ZInQKernel/Contrib/AbVarBC/Tangent.lean
section LF2_AbVarBC_Tangent

/-!
# Base change of abelian varieties, VIII: tangent vectors as dual-number points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

§1 For an affine open `U` of a scheme `X` and a local ring `Λ`, a morphism `p : Spec Λ → X`
sending the closed point into `U` is the same as a ring map `ptRing p : Γ(X, U) → Λ`
(`eq_ofRing_ptRing`, `ptRing_ofRing`, `ptRing_specMap_comp`, `ptRing_comp`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

/-! ## §1. Points of an affine open -/

section Gen

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
  {Λ : CommRingCat.{0}} [IsLocalRing Λ]

/-- The ring map `Γ(X, U) → Λ` of a `Λ`-point whose closed point lies in `U`. -/
def ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) : Γ(X, U) ⟶ Λ :=
  p.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge ≫ (Scheme.ΓSpecIso Λ).hom

theorem ptRing_congr {p q : Spec Λ ⟶ X} (e : p = q) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) : ptRing p hp = ptRing q hq := by
  subst e; rfl

/-- The point attached to a ring map `Γ(X, U) → Λ`. -/
def ofRing (φ : Γ(X, U) ⟶ Λ) : Spec Λ ⟶ X := Spec.map φ ≫ hU.fromSpec

theorem ofRing_mem (φ : Γ(X, U) ⟶ Λ) : ofRing hU φ (IsLocalRing.closedPoint Λ) ∈ U := by
  change ofRing hU φ _ ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem eq_ofRing_ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) :
    p = ofRing hU (ptRing p hp) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _)
    (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [ofRing, ptRing, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ptRing_ext (hU : IsAffineOpen U) {p q : Spec Λ ⟶ X} (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) (h : ptRing p hp = ptRing q hq) : p = q := by
  rw [eq_ofRing_ptRing hU p hp, eq_ofRing_ptRing hU q hq, h]

theorem ptRing_ofRing (φ : Γ(X, U) ⟶ Λ) : ptRing (ofRing hU φ) (ofRing_mem hU φ) = φ := by
  have h := eq_ofRing_ptRing hU (ofRing hU φ) (ofRing_mem hU φ)
  unfold ofRing at h
  rw [cancel_mono] at h
  exact (Spec.map_injective h).symm

/-- Naturality in the local ring. -/
theorem ptRing_specMap_comp (hU : IsAffineOpen U) {Λ' : CommRingCat.{0}} [IsLocalRing Λ'] (ρ : Λ ⟶ Λ')
    (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (Spec.map ρ ≫ p) (IsLocalRing.closedPoint Λ') ∈ U) :
    ptRing (Spec.map ρ ≫ p) hp' = ptRing p hp ≫ ρ := by
  have e : Spec.map ρ ≫ p = ofRing hU (ptRing p hp ≫ ρ) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU _), ptRing_ofRing]

/-- Naturality in the scheme. -/
theorem ptRing_comp (hU : IsAffineOpen U) {Y : Scheme.{0}} (f : X ⟶ Y) {U' : Y.Opens} (hU' : IsAffineOpen U')
    (hle : U ≤ f ⁻¹ᵁ U') (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (p ≫ f) (IsLocalRing.closedPoint Λ) ∈ U') :
    ptRing (p ≫ f) hp' = f.appLE U' U hle ≫ ptRing p hp := by
  have e : p ≫ f = ofRing hU' (f.appLE U' U hle ≫ ptRing p hp) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU' hU hle,
      ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU' _), ptRing_ofRing]

end Gen

/-! ## §2. Dual-number points of a `K`-scheme -/

section Dual

open TrivSqZeroExt

variable {K : Type} [Field K]

instance isLocalRing_tsze (V : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] : IsLocalRing (TrivSqZeroExt K V) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have h1 : a.fst + b.fst = 1 := by simpa using congrArg TrivSqZeroExt.fst h
    rcases eq_or_ne a.fst 0 with ha | ha
    · right
      rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      rw [ha, zero_add] at h1
      rw [h1]
      exact one_ne_zero
    · left
      rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      exact ha

/-- `Spec Λ` as a `K`-scheme. -/
def ptR (Λ : Type) [CommRing Λ] [Algebra K Λ] : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Λ)))

/-- `Spec ρ` over `K` for a `K`-algebra map `ρ`. -/
def specHom {Λ Λ' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    (ρ : Λ →ₐ[K] Λ') : ptR (K := K) Λ' ⟶ ptR Λ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (ρ : Λ →+* Λ'))) (by
    simp only [ptR, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem specHom_left {Λ Λ' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    (ρ : Λ →ₐ[K] Λ') :
    (specHom ρ).left = Spec.map (CommRingCat.ofHom (ρ : Λ →+* Λ')) := rfl

theorem specHom_comp {Λ Λ' Λ'' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    [CommRing Λ''] [Algebra K Λ''] (ρ : Λ →ₐ[K] Λ') (ρ' : Λ' →ₐ[K] Λ'') :
    specHom ρ' ≫ specHom ρ = specHom (ρ'.comp ρ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem specHom_id {Λ : Type} [CommRing Λ] [Algebra K Λ] :
    specHom (AlgHom.id K Λ) = 𝟙 (ptR Λ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id Λ)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

variable (A : PkgI3.AbVar K)

/-- The origin of `A` as a morphism `Spec K → A`. -/
def orig : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

/-- The trivial point is `Spec Λ → Spec K → A` through the origin. -/
theorem one_left {Λ : Type} [CommRing Λ] [Algebra K Λ] :
    (1 : ptR (K := K) Λ ⟶ A.X).left =
      Spec.map (CommRingCat.ofHom (algebraMap K Λ)) ≫ orig A := by
  rw [Hom.one_def, Over.comp_left]
  rfl

end Dual

/-! ## §3. Tangent vectors of an abelian variety at the origin -/

section AbTan

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

instance isLocalHom_fstHom (V : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] : IsLocalHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K) where
  map_nonunit _ hx := isUnit_iff_isUnit_fst.mpr hx

/-- A `V`-valued tangent vector at the origin: a point `Spec (K ⊕ V) → A` over `K` reducing to the
origin. -/
def AtOrigin {V : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
    (a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X) : Prop :=
  specHom (fstHom K K V) ≫ a = 1

variable {V W : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
  [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem atOrigin_one : AtOrigin A (1 : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X) :=
  MonObj.comp_one _

theorem atOrigin_mul {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (hb : AtOrigin A b) : AtOrigin A (a * b) := by
  unfold AtOrigin at *
  rw [MonObj.comp_mul, ha, hb, _root_.mul_one]

theorem atOrigin_map (g : V →ₗ[K] W) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X}
    (ha : AtOrigin A a) : AtOrigin A (specHom (map g) ≫ a) := by
  unfold AtOrigin at *
  rw [← Category.assoc, specHom_comp, fstHom_comp_map, ha]

theorem closedPoint_eq :
    Spec.map (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K)) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint (TrivSqZeroExt K V) := by
  haveI : IsLocalHom (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K)).hom := isLocalHom_fstHom V
  exact Spec_closedPoint (R := CommRingCat.of (TrivSqZeroExt K V)) (S := CommRingCat.of K)

/-- The closed point of a tangent vector at the origin is the origin. -/
theorem left_closedPoint {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    a.left (IsLocalRing.closedPoint (TrivSqZeroExt K V)) =
      orig A (IsLocalRing.closedPoint K) := by
  have h1 := congrArg (fun f => (f.left : Spec (CommRingCat.of K) ⟶ A.X.left)
    (IsLocalRing.closedPoint K)) ha
  simp only at h1
  rw [one_left, Over.comp_left] at h1
  erw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  rw [← closedPoint_eq]
  refine h1.trans ?_
  congr 1

end AbTan

/-! ## §4. The derivation of a tangent vector; additivity under the group law -/

section Deriv

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens} (hU : IsAffineOpen U)
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

variable {V W : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
  [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem mem_of_atOrigin (ho : orig A (IsLocalRing.closedPoint K) ∈ U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    a.left (IsLocalRing.closedPoint (TrivSqZeroExt K V)) ∈ U := by
  rw [left_closedPoint A ha]
  exact ho

theorem comp_orig_mem (ho : orig A (IsLocalRing.closedPoint K) ∈ U) {Λ : CommRingCat.{0}} (p : Spec Λ ⟶ Spec (CommRingCat.of K)) (x : Spec Λ) :
    (p ≫ orig A) x ∈ U := by
  show orig A (p x) ∈ U
  rw [Subsingleton.elim (p x) (IsLocalRing.closedPoint K)]
  exact ho

/-- The evaluation `Γ(A, U) → K` at the origin. -/
def ev0 : Γ(A.X.left, U) ⟶ CommRingCat.of K := ptRing (orig A) ho

/-- The ring map `Γ(A, U) → K ⊕ V` of a tangent vector at the origin. -/
def tRing {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    Γ(A.X.left, U) ⟶ CommRingCat.of (TrivSqZeroExt K V) :=
  ptRing (Λ := CommRingCat.of (TrivSqZeroExt K V)) a.left (mem_of_atOrigin A ho ha)

/-- The derivation `Γ(A, U) → V` of a tangent vector at the origin. -/
def D {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) (x : Γ(A.X.left, U)) : V :=
  ((tRing A ho ha).hom x).snd

theorem tRing_specHom (hU : IsAffineOpen U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (g : V →ₗ[K] W) :
    tRing A ho (atOrigin_map A g ha) =
      tRing A ho ha ≫ CommRingCat.ofHom ((map g : TrivSqZeroExt K V →ₐ[K] _) :
        TrivSqZeroExt K V →+* TrivSqZeroExt K W) :=
  ptRing_specMap_comp hU _ _ _ _

theorem tRing_congr {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (e : a = b)
    (ha : AtOrigin A a) (hb : AtOrigin A b) : tRing A ho ha = tRing A ho hb := by
  subst e; rfl

theorem tRing_one (hU : IsAffineOpen U) :
    tRing A ho (atOrigin_one A (V := V)) =
      ev0 A ho ≫ CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V)) := by
  unfold tRing ev0
  rw [← ptRing_specMap_comp hU _ _ ho (comp_orig_mem A ho _ _)]
  exact ptRing_congr (one_left A) _ _

theorem fst_tRing (hU : IsAffineOpen U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (x : Γ(A.X.left, U)) : ((tRing A ho ha).hom x).fst = (ev0 A ho).hom x := by
  have h1 : tRing A ho ha ≫ CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K) = ev0 A ho ≫ CommRingCat.ofHom (algebraMap K K) := by
    unfold tRing ev0
    rw [← ptRing_specMap_comp hU _ _ (mem_of_atOrigin A ho ha) (by
        show a.left (Spec.map (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
          TrivSqZeroExt K V →+* K)) (IsLocalRing.closedPoint K)) ∈ U
        rw [closedPoint_eq]
        exact mem_of_atOrigin A ho ha),
      ← ptRing_specMap_comp hU _ _ ho (comp_orig_mem A ho _ _)]
    refine ptRing_congr ?_ _ _
    have := congrArg (fun f => f.left) ha
    simp only [Over.comp_left, one_left] at this
    exact this
  have := congrArg (fun f => f.hom x) h1
  simpa using this

theorem D_one (hU : IsAffineOpen U) : D A ho (atOrigin_one A (V := V)) = 0 := by
  funext x
  unfold D
  rw [tRing_one A ho hU]
  simp [algebraMap_eq_inl]

/-- A tangent vector at the origin is determined by its derivation. -/
theorem eq_of_D_eq (hU : IsAffineOpen U) {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (hb : AtOrigin A b) (h : D A ho ha = D A ho hb) : a = b := by
  apply Over.OverMorphism.ext
  apply ptRing_ext hU (mem_of_atOrigin A ho ha) (mem_of_atOrigin A ho hb)
  ext x
  · exact (fst_tRing A ho hU ha x).trans (fst_tRing A ho hU hb x).symm
  · exact congrFun h x

end Deriv

/-! ## §5. Additivity: `D (v * w) = D v + D w` -/

section Mul

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens}
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

theorem map_fst_inr :
    (map (LinearMap.fst K K K)).comp (map (LinearMap.inr K K K)) =
      (inlAlgHom K K K).comp (fstHom K K K) := by
  rw [← map_comp_map]
  apply algHom_ext
  intro x
  rw [map_inr, AlgHom.comp_apply, fstHom_apply, fst_inr]
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.snd_apply, inr_zero, map_zero]

theorem map_snd_inl :
    (map (LinearMap.snd K K K)).comp (map (LinearMap.inl K K K)) =
      (inlAlgHom K K K).comp (fstHom K K K) := by
  rw [← map_comp_map]
  apply algHom_ext
  intro x
  rw [map_inr, AlgHom.comp_apply, fstHom_apply, fst_inr]
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.snd_apply, inr_zero, map_zero]

theorem map_fst_inl :
    (map (LinearMap.fst K K K)).comp (map (LinearMap.inl K K K)) = AlgHom.id K _ := by
  rw [← map_comp_map, LinearMap.fst_comp_inl, map_id]

theorem map_snd_inr :
    (map (LinearMap.snd K K K)).comp (map (LinearMap.inr K K K)) = AlgHom.id K _ := by
  rw [← map_comp_map, LinearMap.snd_comp_inr, map_id]

theorem map_add_inl :
    (map (LinearMap.fst K K K + LinearMap.snd K K K)).comp (map (LinearMap.inl K K K)) =
      AlgHom.id K _ := by
  rw [← map_comp_map]
  convert map_id (R' := K) (M := K)
  ext
  simp

theorem map_add_inr :
    (map (LinearMap.fst K K K + LinearMap.snd K K K)).comp (map (LinearMap.inr K K K)) =
      AlgHom.id K _ := by
  rw [← map_comp_map]
  convert map_id (R' := K) (M := K)
  ext
  simp

theorem spec_inl_fst_comp {a : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X} (ha : AtOrigin A a) :
    specHom ((inlAlgHom K K K).comp (fstHom K K K)) ≫ a = 1 := by
  rw [← specHom_comp, Category.assoc]
  unfold AtOrigin at ha
  rw [ha, MonObj.comp_one]

/-- **Additivity of the derivation under the group law.** -/
theorem D_mul (hU : IsAffineOpen U) {v w : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) (hw : AtOrigin A w) :
    D A ho (atOrigin_mul A hv hw) = D A ho hv + D A ho hw := by
  set c := (specHom (map (LinearMap.inl K K K)) ≫ v) * (specHom (map (LinearMap.inr K K K)) ≫ w)
    with hcdef
  have hc : AtOrigin A c := atOrigin_mul A (atOrigin_map A _ hv) (atOrigin_map A _ hw)
  have e1 : specHom (map (LinearMap.fst K K K)) ≫ c = v := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_fst_inl, map_fst_inr, specHom_id, Category.id_comp, spec_inl_fst_comp A hw,
      _root_.mul_one]
  have e2 : specHom (map (LinearMap.snd K K K)) ≫ c = w := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_snd_inl, map_snd_inr, specHom_id, Category.id_comp, spec_inl_fst_comp A hv,
      _root_.one_mul]
  have e3 : specHom (map (LinearMap.fst K K K + LinearMap.snd K K K)) ≫ c = v * w := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_add_inl, map_add_inr, specHom_id, Category.id_comp, Category.id_comp]
  have h1 := (tRing_congr A ho e1 (atOrigin_map A _ hc) hv).symm.trans
    (tRing_specHom A ho hU hc _)
  have h2 := (tRing_congr A ho e2 (atOrigin_map A _ hc) hw).symm.trans
    (tRing_specHom A ho hU hc _)
  have h3 := (tRing_congr A ho e3 (atOrigin_map A _ hc) (atOrigin_mul A hv hw)).symm.trans
    (tRing_specHom A ho hU hc _)
  funext x
  simp only [D, Pi.add_apply, h1, h2, h3, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom, AlgHom.coe_toRingHom, snd_map, LinearMap.add_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

end Mul

/-! ## §6. `[n]` on tangent vectors -/

section Zpow

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens}
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

theorem intCast_hom (n : ℤ) : ((n : PkgI3.AbVar.End A)).hom = (𝟙 A.X) ^ n := by
  rw [← zsmul_one]
  change (Additive.toMul (n • (1 : PkgI3.AbVar.End A))).1 = _
  rw [toMul_zsmul, Subgroup.coe_zpow]
  rfl

/-- `q ≫ [n] = q ^ n`. -/
theorem comp_intCast_hom {T : Over (Spec (CommRingCat.of K))} (q : T ⟶ A.X) (n : ℤ) :
    q ≫ ((n : PkgI3.AbVar.End A)).hom = q ^ n := by
  rw [intCast_hom, GrpObj.comp_zpow, Category.comp_id]

variable {V : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

theorem atOrigin_inv {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    AtOrigin A a⁻¹ := by
  unfold AtOrigin at *
  rw [GrpObj.comp_inv, ha, inv_one]

theorem atOrigin_zpow {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) (n : ℤ) :
    AtOrigin A (a ^ n) := by
  unfold AtOrigin at *
  rw [GrpObj.comp_zpow, ha, one_zpow]

theorem D_congr {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (e : a = b) (ha : AtOrigin A a)
    (hb : AtOrigin A b) : D A ho ha = D A ho hb := by
  subst e; rfl

theorem D_inv (hU : IsAffineOpen U) {v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) : D A ho (atOrigin_inv A hv) = - D A ho hv := by
  have h := D_mul A ho hU hv (atOrigin_inv A hv)
  rw [D_congr A ho (mul_inv_cancel v) _ (atOrigin_one A), D_one A ho hU] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem D_zpow (hU : IsAffineOpen U) {v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) (n : ℤ) : D A ho (atOrigin_zpow A hv n) = n • D A ho hv := by
  induction n using Int.induction_on with
  | zero =>
    rw [D_congr A ho (zpow_zero v) _ (atOrigin_one A), D_one A ho hU, zero_smul]
  | succ m ih =>
    rw [D_congr A ho (zpow_add_one v m) _ (atOrigin_mul A (atOrigin_zpow A hv m) hv),
      D_mul A ho hU (atOrigin_zpow A hv m) hv, ih, add_smul, one_smul]
  | pred m ih =>
    rw [D_congr A ho (zpow_sub_one v (-(m : ℤ))) _
      (atOrigin_mul A (atOrigin_zpow A hv _) (atOrigin_inv A hv)),
      D_mul A ho hU (atOrigin_zpow A hv _) (atOrigin_inv A hv), ih, D_inv A ho hU, sub_smul,
      one_smul, sub_eq_add_neg]

/-- **A tangent vector at the origin killed by `[n]`, `n ≠ 0`, characteristic `0`, is trivial.** -/
theorem eq_one_of_comp_intCast [CharZero K] (ho : orig A (IsLocalRing.closedPoint K) ∈ U) (hU : IsAffineOpen U)
    {v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X} (hv : AtOrigin A v) (n : ℤ) (hn : n ≠ 0)
    (h : v ≫ ((n : PkgI3.AbVar.End A)).hom = 1) : v = 1 := by
  rw [comp_intCast_hom] at h
  have h1 := D_zpow A ho hU hv n
  rw [D_congr A ho h _ (atOrigin_one A), D_one A ho hU] at h1
  have h2 : D A ho hv = 0 := by
    funext x
    have := congrFun h1 x
    simp only [Pi.zero_apply, Pi.smul_apply] at this
    rw [← Int.cast_smul_eq_zsmul K, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (Int.cast_ne_zero.mpr hn)
  refine eq_of_D_eq A ho hU hv (atOrigin_one A) ?_
  rw [h2, D_one A ho hU]

end Zpow

end ZInQ.Contrib.AbVarBC.Tangent

end

end LF2_AbVarBC_Tangent

-- ===== ZInQKernel/Contrib/AbVarBC/KerUnit.lean
section LF2_AbVarBC_KerUnit

/-!
# Base change of abelian varieties, IX: the unit section of `A[n]` is an open immersion

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

In characteristic `0` and for `n ≠ 0`, the unit section `kerUnit A [n] : Spec K → A[n]` is an
open immersion: mul-rigidity's leaf `KerUnitOpen` is a theorem (`kerUnitOpen`). Proof:
* §1 a `K`-derivation `D : Γ(A[n], W) → K` at the origin gives a tangent vector `v` of `A[n]`;
  its image in `A` is a tangent vector killed by `[n]`, hence trivial (`Tangent.lean` §6), so
  `v` is trivial and `D = 0` (`derivation_eq_zero`);
* §2 hence the maximal ideal `P` of the origin in `T = Γ(A[n], W)` satisfies `P = P²`
  (functionals on `P / P²` are derivations), so `P = (e)` with `e` idempotent (`T` Noetherian);
* §3 on the basic open `D(1 - e)` the structure map to `Spec K` is surjective on sections, so
  formally unramified, and the unit section is a section of it, hence an open immersion.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

open TrivSqZeroExt

/-! ## §1. Derivations at the origin of `A[n]` vanish -/

section Der

variable {K : Type} [Field K]

/-- The ring map `t ↦ ev t + ε D t` of a derivation `D` at `ev`. -/
def dualHom {T : Type} [CommRing T] (ev : T →+* K) (D : T → K)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = ev a * D b + ev b * D a) :
    T →+* TrivSqZeroExt K K where
  toFun t := inl (ev t) + inr (D t)
  map_one' := by
    have h : D 1 = 0 := by
      have := hmul 1 1
      rw [_root_.mul_one, map_one, _root_.one_mul] at this
      linear_combination -this
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [hmul]
      ring
  map_zero' := by
    have h : D 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      linear_combination -this
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [hadd]

end Der

section KerDer

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℤ)

/-- `[n] : A → A`. -/
abbrev mulN : A.X ⟶ A.X := ((n : PkgI3.AbVar.End A)).hom

/-- The kernel `A[n]` (as an object over `Spec K`). -/
abbrev KerN : Over (Spec (CommRingCat.of K)) := pullback (mulN A n) η[A.X]

/-- The unit section of `A[n]`, as a morphism of schemes. -/
def ks : Spec (CommRingCat.of K) ⟶ (KerN A n).left :=
  (MulRigidity.kerUnit A (mulN A n)).left

theorem ks_hom : ks A n ≫ (KerN A n).hom = 𝟙 _ :=
  Over.w (MulRigidity.kerUnit A (mulN A n))

theorem comp_mem_of_subsingleton {X : Scheme.{0}} {W : X.Opens}
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s (IsLocalRing.closedPoint K) ∈ W) {Λ : CommRingCat.{0}}
    (p : Spec Λ ⟶ Spec (CommRingCat.of K)) (x : Spec Λ) : (p ≫ s) x ∈ W := by
  show s (p x) ∈ W
  rw [Subsingleton.elim (p x) (IsLocalRing.closedPoint K)]
  exact hs

theorem exists_affine_orig :
    ∃ U : A.X.left.Opens, IsAffineOpen U ∧ orig A (IsLocalRing.closedPoint K) ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := A.X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (orig A (IsLocalRing.closedPoint K))) isOpen_univ
  exact ⟨U, hU, hxU⟩

/-- **A derivation at the origin of `A[n]` vanishes** (characteristic `0`, `n ≠ 0`). -/
theorem derivation_eq_zero [CharZero K] (hn : n ≠ 0) {W : (KerN A n).left.Opens}
    (hW : IsAffineOpen W) (hz0 : ks A n (IsLocalRing.closedPoint K) ∈ W)
    (D : Γ((KerN A n).left, W) → K) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = (ptRing (Λ := CommRingCat.of K) (ks A n) hz0).hom a * D b +
      (ptRing (Λ := CommRingCat.of K) (ks A n) hz0).hom b * D a)
    (hκ : ∀ x, D ((KerN A n).hom.appLE ⊤ W le_top x) = 0) : ∀ t, D t = 0 := by
  obtain ⟨U, hU, ho⟩ := exists_affine_orig A
  set ev := ptRing (Λ := CommRingCat.of K) (ks A n) hz0 with hev
  set φ : Γ((KerN A n).left, W) ⟶ CommRingCat.of (TrivSqZeroExt K K) :=
    CommRingCat.ofHom (dualHom ev.hom D hadd hmul) with hφ
  set v := ofRing hW φ with hv
  have hvmem := ofRing_mem hW φ
  have hpv : ptRing v hvmem = φ := ptRing_ofRing hW φ
  have htop : ∀ (Λ : CommRingCat.{0}) [IsLocalRing Λ] (p : Spec Λ ⟶ Spec (CommRingCat.of K)),
      p (IsLocalRing.closedPoint Λ) ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    fun _ _ _ => trivial
  -- the evaluation on sections coming from `K`
  have hevκ : ∀ x, ev.hom ((KerN A n).hom.appLE ⊤ W le_top x) =
      (ptRing (Λ := CommRingCat.of K) (𝟙 (Spec (CommRingCat.of K))) (htop _ _)).hom x := by
    intro x
    have h := ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top (ks A n) hz0
      (htop _ _)
    rw [ptRing_congr (ks_hom A n) _ (htop _ _)] at h
    rw [h]
    rfl
  -- `v` is a point over `K`
  have hvK : v ≫ (KerN A n).hom = Spec.map (CommRingCat.ofHom
      (algebraMap K (TrivSqZeroExt K K))) := by
    apply ptRing_ext (isAffineOpen_top _) (htop _ _) (htop _ _)
    rw [ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top v hvmem (htop _ _), hpv,
      ptRing_congr (Category.comp_id _).symm (htop _ _) (htop _ _),
      ptRing_specMap_comp (isAffineOpen_top _) _ _ (htop _ _)]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, hφ,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    change inl (ev.hom _) + inr (D _) = _
    rw [hκ, inr_zero, add_zero, hevκ, algebraMap_eq_inl]
  let vt : ptR (K := K) (TrivSqZeroExt K K) ⟶ KerN A n := Over.homMk v hvK
  -- its reduction is the unit section
  have hfst : specHom (fstHom K K K) ≫ vt = toUnit _ ≫ MulRigidity.kerUnit A (mulN A n) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ v = Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ ks A n
    have m1 : (Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) ≫ v) (IsLocalRing.closedPoint K) ∈ W := by
      show v (Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) (IsLocalRing.closedPoint K)) ∈ W
      rw [closedPoint_eq]
      exact hvmem
    have m2 := comp_mem_of_subsingleton (ks A n) hz0
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) (IsLocalRing.closedPoint K)
    apply ptRing_ext hW m1 m2
    rw [ptRing_specMap_comp hW _ _ hvmem, ptRing_specMap_comp hW _ _ hz0, hpv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, hφ,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    change (inl (ev.hom t) + inr (D t) : TrivSqZeroExt K K).fst = algebraMap K K (ev.hom t)
    rw [fst_add, fst_inl, fst_inr, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
  set u := vt ≫ pullback.fst (mulN A n) η[A.X] with hu
  have hu0 : AtOrigin A u := by
    unfold AtOrigin
    rw [hu, ← Category.assoc, hfst, Category.assoc, MulRigidity.kerUnit, pullback.lift_fst,
      Hom.one_def]
  have huf : u ≫ mulN A n = 1 := by
    rw [hu, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have hu1 : u = 1 := eq_one_of_comp_intCast A ho hU hu0 n hn huf
  have hvt : vt = toUnit _ ≫ MulRigidity.kerUnit A (mulN A n) := by
    apply pullback.hom_ext
    · rw [← hu, hu1, Category.assoc, MulRigidity.kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  have hvl : v = Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))) ≫ ks A n :=
    congrArg (fun g => g.left) hvt
  have m3 := comp_mem_of_subsingleton (ks A n) hz0
    (Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))))
    (IsLocalRing.closedPoint (TrivSqZeroExt K K))
  have key := (ptRing_congr hvl hvmem m3).trans (ptRing_specMap_comp hW _ _ hz0 m3)
  rw [hpv] at key
  intro t
  have := congrArg (fun g => (g.hom t).snd) key
  simp only [hφ, CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at this
  change (inl (ev.hom t) + inr (D t) : TrivSqZeroExt K K).snd = _ at this
  rw [snd_add, snd_inl, snd_inr, zero_add, algebraMap_eq_inl, snd_inl] at this
  exact this

end KerDer

/-! ## §2. Commutative algebra: no derivations means `P = P²` -/

section Alg

variable {K : Type} [Field K]

/-- If every `K`-derivation `T → K` at `ev` vanishes, the kernel `P` of `ev` satisfies `P ≤ P²`
(a functional on `P / P²` is a derivation). -/
theorem ker_le_sq_of_derivations {T : Type} [CommRing T] (ev : T →+* K) (jK : K →+* T)
    (hevj : ∀ c, ev (jK c) = c)
    (hD : ∀ D : T → K, (∀ a b, D (a + b) = D a + D b) →
      (∀ a b, D (a * b) = ev a * D b + ev b * D a) → (∀ c, D (jK c) = 0) → ∀ t, D t = 0) :
    RingHom.ker ev ≤ (RingHom.ker ev) ^ 2 := by
  intro a ha
  by_contra hna
  letI : Algebra K T := jK.toAlgebra
  have hsmul : ∀ (c : K) (t : T), c • t = jK c * t := fun c t => Algebra.smul_def c t
  set P := RingHom.ker ev with hP
  let P' : Submodule K T := P.restrictScalars K
  let N : Submodule K P' := ((P ^ 2).restrictScalars K).comap P'.subtype
  have hmem : ∀ t, t - jK (ev t) ∈ P' := fun t => by
    change t - jK (ev t) ∈ RingHom.ker ev
    rw [RingHom.mem_ker, map_sub, hevj, sub_self]
  let q : T → P' ⧸ N := fun t => N.mkQ ⟨t - jK (ev t), hmem t⟩
  have hqa : q a ≠ 0 := by
    intro h
    change N.mkQ ⟨a - jK (ev a), hmem a⟩ = 0 at h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    apply hna
    have h' : a - jK (ev a) ∈ P ^ 2 := h
    rwa [RingHom.mem_ker.mp ha, map_zero, sub_zero] at h'
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual K (P' ⧸ N), l (q a) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqa ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  have hadd : ∀ x y, l (q (x + y)) = l (q x) + l (q y) := by
    intro x y
    rw [← map_add]
    congr 1
    change N.mkQ _ = N.mkQ _ + N.mkQ _
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    ring
  have hmul : ∀ x y, l (q (x * y)) = ev x * l (q y) + ev y * l (q x) := by
    intro x y
    suffices hq : q (x * y) = ev x • q y + ev y • q x by
      rw [hq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change N.mkQ _ = ev x • N.mkQ _ + ev y • N.mkQ _
    rw [← map_smul, ← map_smul, ← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    change ((⟨x * y - jK (ev (x * y)), hmem _⟩ : P') -
      (ev x • ⟨y - jK (ev y), hmem y⟩ + ev y • ⟨x - jK (ev x), hmem x⟩) : P').1 ∈ P ^ 2
    have e1 : ((⟨x * y - jK (ev (x * y)), hmem _⟩ : P') -
        (ev x • ⟨y - jK (ev y), hmem y⟩ + ev y • ⟨x - jK (ev x), hmem x⟩) : P').1 =
        (x - jK (ev x)) * (y - jK (ev y)) := by
      simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, hsmul, map_mul]
      ring
    rw [e1, pow_two]
    exact Ideal.mul_mem_mul (hmem x) (hmem y)
  have hj : ∀ c, l (q (jK c)) = 0 := by
    intro c
    have : q (jK c) = 0 := by
      change N.mkQ _ = 0
      have : (⟨jK c - jK (ev (jK c)), hmem _⟩ : P') = 0 := by
        apply Subtype.ext
        simp [hevj]
      rw [this, map_zero]
    rw [this, map_zero]
  exact hl (hD (fun t => l (q t)) hadd hmul hj a)

end Alg

/-! ## §3. The unit section of `A[n]` is an open immersion -/

section Final

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℤ)

theorem locallyOfFiniteType_kerN : LocallyOfFiniteType (KerN A n).hom := by
  have h1 : LocallyOfFiniteType (mulN A n).left := by
    have : LocallyOfFiniteType ((mulN A n).left ≫ A.X.hom) := by
      rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ A.X.hom
  have hP := (Over.forget _).map_isPullback (IsPullback.of_hasPullback (mulN A n) η[A.X])
  have h2 : LocallyOfFiniteType (pullback.snd (mulN A n) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType) hP h1
  have h3 : (pullback.snd (mulN A n) η[A.X]).left ≫
      (𝟙_ (Over (Spec (CommRingCat.of K)))).hom = (KerN A n).hom := Over.w _
  rw [← h3]
  change LocallyOfFiniteType (_ ≫ 𝟙 _)
  rw [Category.comp_id]
  exact h2

theorem id_appLE_top (h : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
    (𝟙 (Spec (CommRingCat.of K))) ⁻¹ᵁ ⊤) :
    Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of K))) ⊤ ⊤ h = 𝟙 _ := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact (Spec (CommRingCat.of K)).presheaf.map_id (Opposite.op ⊤)

theorem ptRing_id_top :
    ptRing (Λ := CommRingCat.of K) (𝟙 (Spec (CommRingCat.of K)))
      (show _ ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
  unfold ptRing
  rw [id_appLE_top, Category.id_comp]

/-- **mul-rigidity's leaf `KerUnitOpen`, proved**: in characteristic `0`, for `n ≠ 0`, the unit
section of `A[n]` is an open immersion. -/
theorem ks_isOpenImmersion [CharZero K] (hn : n ≠ 0) : IsOpenImmersion (ks A n) := by
  set Z := (KerN A n).left with hZ
  obtain ⟨_, ⟨W, hW, rfl⟩, hz0, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ks A n (IsLocalRing.closedPoint K))) isOpen_univ
  haveI := locallyOfFiniteType_kerN A n
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (KerN A n).hom
  haveI : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  set ev := ptRing (Λ := CommRingCat.of K) (ks A n) hz0 with hev
  set κ := (KerN A n).hom.appLE ⊤ W le_top with hκ
  let jK : K →+* Γ(Z, W) := κ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have htop : ∀ (Λ : CommRingCat.{0}) [IsLocalRing Λ] (p : Spec Λ ⟶ Spec (CommRingCat.of K)),
      p (IsLocalRing.closedPoint Λ) ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    fun _ _ _ => trivial
  have hevκ : ∀ x, ev.hom (κ.hom x) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x := by
    intro x
    have h := ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top (ks A n) hz0
      (htop _ _)
    rw [ptRing_congr (ks_hom A n) _ (htop _ _), ptRing_id_top] at h
    rw [h]
    rfl
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hevj : ∀ c, ev.hom (jK c) = c := by
    intro c
    change ev.hom (κ.hom (eK.symm c)) = c
    rw [hevκ]
    exact eK.apply_symm_apply c
  have hκj : ∀ x, κ.hom x = jK ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x) := by
    intro x
    change κ.hom x = κ.hom (eK.symm (eK x))
    rw [RingEquiv.symm_apply_apply]
  have hPP := ker_le_sq_of_derivations ev.hom jK hevj (fun D hadd hmul hj =>
    derivation_eq_zero A n hn hW hz0 D hadd hmul (fun x => by rw [hκj]; exact hj _))
  have hidem : IsIdempotentElem (RingHom.ker ev.hom) := by
    unfold IsIdempotentElem
    rw [← pow_two]
    exact le_antisymm (Ideal.pow_le_self two_ne_zero) hPP
  obtain ⟨e, he, hPe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hidem
  have heP : e ∈ RingHom.ker ev.hom := by
    rw [hPe]; exact Submodule.mem_span_singleton_self e
  set g : Γ(Z, W) := 1 - e with hg
  have hevg : ev.hom g = 1 := by
    rw [hg, map_sub, map_one, RingHom.mem_ker.mp heP, sub_zero]
  -- the origin lies in `D(g)`
  have hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ ks A n ⁻¹ᵁ W :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ks A n) hz0).ge
  have hz0' : ks A n (IsLocalRing.closedPoint K) ∈ Z.basicOpen g := by
    have hb := Scheme.basicOpen_appLE (ks A n) ⊤ W hle g
    have hu : IsUnit ((ks A n).appLE W ⊤ hle g) := by
      have h1 : eK ((ks A n).appLE W ⊤ hle g) = 1 := hevg
      have : (ks A n).appLE W ⊤ hle g = 1 := by
        rw [← eK.symm_apply_apply ((ks A n).appLE W ⊤ hle g), h1, map_one]
      rw [this]
      exact isUnit_one
    rw [Scheme.basicOpen_of_isUnit _ hu] at hb
    have hmem : IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) := trivial
    rw [hb] at hmem
    exact hmem.2
  set W' := Z.basicOpen g with hW'def
  have hW' : IsAffineOpen W' := hW.basicOpen g
  haveI hloc := hW.isLocalization_basicOpen g
  have hge : algebraMap Γ(Z, W) Γ(Z, W') g * algebraMap Γ(Z, W) Γ(Z, W') e = 0 := by
    have hge0 : g * e = 0 := by
      change (1 - e) * e = 0
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]
    rw [← map_mul, hge0, map_zero]
  have hgu : IsUnit (algebraMap Γ(Z, W) Γ(Z, W') g) := IsLocalization.Away.algebraMap_isUnit g
  have hre : algebraMap Γ(Z, W) Γ(Z, W') e = 0 := hgu.mul_right_eq_zero.mp hge
  have hrg : algebraMap Γ(Z, W) Γ(Z, W') g = 1 := by
    have h := map_sub (algebraMap Γ(Z, W) Γ(Z, W')) 1 e
    rw [map_one, hre, sub_zero] at h
    exact h
  have hrP : ∀ t ∈ RingHom.ker ev.hom, algebraMap Γ(Z, W) Γ(Z, W') t = 0 := by
    intro t ht
    rw [hPe] at ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    rw [smul_eq_mul, map_mul, hre, MulZeroClass.mul_zero]
  set κ' := (KerN A n).hom.appLE ⊤ W' le_top with hκ'def
  have hκ' : κ' = κ ≫ Z.presheaf.map (homOfLE (Z.basicOpen_le g)).op := by
    rw [hκ'def, hκ]
    exact (Scheme.Hom.appLE_map (KerN A n).hom le_top (homOfLE (Z.basicOpen_le g)).op).symm
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ κ').hom := by
    intro y
    obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) y
    obtain ⟨k, hk⟩ := s.2
    refine ⟨ev.hom t, ?_⟩
    have hs1 : algebraMap Γ(Z, W) Γ(Z, W') (s : Γ(Z, W)) = 1 := by
      rw [← hk, map_pow, hrg, one_pow]
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, hs1, _root_.mul_one]
    have hmem : t - jK (ev.hom t) ∈ RingHom.ker ev.hom := by
      rw [RingHom.mem_ker, map_sub, hevj, sub_self]
    have h0 := hrP _ hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, hκ']
    rfl
  let i := hW'.fromSpec
  have hrange : Set.range (ks A n) ⊆ Set.range i := by
    rw [hW'.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]
    exact hz0'
  let s' := IsOpenImmersion.lift i (ks A n) hrange
  have hs' : s' ≫ i = ks A n := IsOpenImmersion.lift_fac _ _ _
  have hiK : i ≫ (KerN A n).hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ κ') := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (KerN A n).hom (isAffineOpen_top _) hW' le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp]
    exact h.symm
  haveI : FormallyUnramified (i ≫ (KerN A n).hom) := by
    rw [hiK, HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact RingHom.FormallyUnramified.of_surjective hsurj
  have hsec : s' ≫ (i ≫ (KerN A n).hom) = 𝟙 _ := by
    rw [← Category.assoc, hs', ks_hom]
  haveI := MulRigidity.isOpenImmersion_of_section s' (i ≫ (KerN A n).hom) hsec
  rw [← hs']
  infer_instance

end Final

end ZInQ.Contrib.AbVarBC.Tangent

end

end LF2_AbVarBC_KerUnit

-- ===== ZInQKernel/Contrib/AbVarBC/G9Instance.lean
section LF2_AbVarBC_G9Instance

/-!
# Base change of abelian varieties, IV: the instance `G9Bridge.AbVarBaseChange`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

`G9Bridge.AbVarBaseChange` (task g9-derham, `ZInQKernel/Contrib/G9/LocalModel.lean`) is stated over
two verbatim copies of the kernel's abelian varieties: `_root_.HDec.PkgI3.AbVar`
(`Contrib/G9/I3Layer.lean`) and `_root_.HDec.PkgI4.I3.AbVar` (`Contrib/G9/I4Layer.lean`).
§1 transports between the copies and the kernel's `PkgI3.AbVar` (all identities are `rfl`);
§2 derives the instance from the general lemmas of `Contrib/AbVarBC/{Dim,Points,Tate}.lean`.

* `abVarBaseChange_of_torsionDescends`: from descent of `ℓ`-power torsion points;
* `abVarBaseChange_of_tateModuleFree`: from leaf T26 `PkgI3.TateModuleFree` (I3.M0);
* `g9Glue_of_tateModuleFree`: `TateModuleFree → R10Weights → G9Glue`.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Transport between the copies -/

section Transport

variable {K : Type} [Field K]

/-- G9's copy of pkg-I3's abelian variety, as a kernel `PkgI3.AbVar`. -/
def ofG9 (A : _root_.HDec.PkgI3.AbVar K) : _root_.HDec.PkgI3.AbVar K :=
  @_root_.HDec.PkgI3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

/-- A kernel `PkgI3.AbVar`, as pkg-I4's copy `PkgI4.I3.AbVar` (in G9's namespace). -/
def toI4 (A : _root_.HDec.PkgI3.AbVar K) : _root_.HDec.PkgI4.I3.AbVar K :=
  @_root_.HDec.PkgI4.I3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

theorem dim_ofG9 (A : _root_.HDec.PkgI3.AbVar K) : (ofG9 A).dim = A.dim := rfl

theorem dim_toI4 (A : _root_.HDec.PkgI3.AbVar K) : (toI4 A).dim = A.dim := rfl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ` of G9's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vOfG9 (A : _root_.HDec.PkgI3.AbVar K) : A.V ℓ ≃ₗ[ℚ_[ℓ]] (ofG9 A).V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vOfG9_galRep (A : _root_.HDec.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : A.V ℓ) : vOfG9 ℓ A (A.galRep ℓ σ v) = (ofG9 A).galRep ℓ σ (vOfG9 ℓ A v) := rfl

theorem vOfG9_symm_galRep (A : _root_.HDec.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (ofG9 A).V ℓ) :
    (vOfG9 ℓ A).symm ((ofG9 A).galRep ℓ σ v) = A.galRep ℓ σ ((vOfG9 ℓ A).symm v) := rfl

/-- `V_ℓ` of pkg-I4's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vToI4 (A : _root_.HDec.PkgI3.AbVar K) : (toI4 A).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vToI4_galRep (A : _root_.HDec.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (toI4 A).V ℓ) : vToI4 ℓ A ((toI4 A).galRep ℓ σ v) = A.galRep ℓ σ (vToI4 ℓ A v) := rfl

end Transport

/-! ## §2. The instance -/

/-- `Field.absoluteGaloisGroup.map i` is restriction along the `K`-embedding `K̄ → L̄` it is
built from (`IsAlgClosed.lift`). -/
theorem map_comm {K L : Type} [Field K] [Field L] (i : K →+* L) :
    letI : Algebra K L := i.toAlgebra
    ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
      (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
          (galK (Field.absoluteGaloisGroup.map i σ) x) =
        galK σ ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) x) := by
  letI : Algebra K L := i.toAlgebra
  let g0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g0.toAlgebra
  exact fun σ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) (AlgebraicClosure K) x

/-- **`AbVarBaseChange` from descent of `ℓ`-power torsion points.** The hypothesis is the
statement "every `ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`" for the kernel's
objects and the embedding `K̄ → L̄` of `Field.absoluteGaloisGroup.map`. -/
theorem abVarBaseChange_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange := by
  intro K _ _ A L _ i ℓ _
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_torsionDescends (ofG9 A) κ ℓ (hD K (ofG9 A) L i ℓ)
  refine ⟨toI4 ((ofG9 A).baseChange L),
    (vToI4 ℓ _).trans ((vBC (ofG9 A) κ ℓ hb).trans (vOfG9 ℓ A).symm), ?_, ?_⟩
  · exact (dim_toI4 _).trans (((ofG9 A).dim_baseChange L).trans (dim_ofG9 A))
  · intro σ v
    simp only [LinearEquiv.trans_apply]
    rw [vToI4_galRep, vBC_galRep (ofG9 A) κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ
      (map_comm i σ)]
    exact vOfG9_symm_galRep ℓ A _ _

/-- **`AbVarBaseChange` from leaf T26 (`PkgI3.TateModuleFree`, Mumford §§4, 18-19).** -/
theorem abVarBaseChange_of_tateModuleFree (hT : _root_.HDec.PkgI3.TateModuleFree) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange := by
  intro K _ _ A L _ i ℓ hℓ
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_tateModuleFree (ofG9 A) κ ℓ hT
    (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
  refine ⟨toI4 ((ofG9 A).baseChange L),
    (vToI4 ℓ _).trans ((vBC (ofG9 A) κ ℓ hb).trans (vOfG9 ℓ A).symm), ?_, ?_⟩
  · exact (dim_toI4 _).trans (((ofG9 A).dim_baseChange L).trans (dim_ofG9 A))
  · intro σ v
    simp only [LinearEquiv.trans_apply]
    rw [vToI4_galRep, vBC_galRep (ofG9 A) κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ
      (map_comm i σ)]
    exact vOfG9_symm_galRep ℓ A _ _

/-- **G9 from T26 and the weight clause**: `TateModuleFree → R10Weights → G9Glue`. -/
theorem g9Glue_of_tateModuleFree (hT : _root_.HDec.PkgI3.TateModuleFree)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_tateModuleFree hT) hW

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_G9Instance

-- ===== ZInQKernel/Contrib/AbVarBC/G9Mul.lean
section LF2_AbVarBC_G9Mul

/-!
# Base change of abelian varieties, VI: `AbVarBaseChange` from finiteness of `[n]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

The `V_ℓ` clause of `G9Bridge.AbVarBaseChange` needs exactly the descent of `ℓ`-power torsion
points (`TorsionDescends`), which follows from finiteness of `[ℓⁿ]`
(`torsionDescends_of_isFinite`). Finiteness of `[n]` is mul-rigidity's `MulIsogeny`
(Mumford §4; Milne Thm 8.2), which mul-rigidity reduced to the single point statement
`KerUnitOpen` and further to two cotangent-space glue statements. Hence:

* `abVarBaseChangeK_of_mulIsogeny`: the kernel-level statement `AbVarBaseChangeK`;
* `abVarBaseChange_of_mulIsogeny`, `…_of_kerUnitOpen`, `…_of_mulEtale`, `…_of_cotangent`;
* `g9Glue_of_kerUnitOpen`, `g9Glue_of_cotangent`.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-- **The statement of `G9Bridge.AbVarBaseChange` over the kernel's `PkgI3.AbVar`**, with the
witness pinned to `A.baseChange L`. -/
def AbVarBaseChangeK : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) (L : Type) [Field L]
    (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
    letI : Algebra K L := i.toAlgebra
    (A.baseChange L).dim = A.dim ∧
      ∃ c : (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ,
        ∀ σ v, c ((A.baseChange L).galRep ℓ σ v) =
          A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

/-- `AbVarBaseChangeK` from torsion descent. -/
theorem abVarBaseChangeK_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ) :
    AbVarBaseChangeK := by
  intro K _ _ A L _ i ℓ _
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_torsionDescends A κ ℓ (hD K A L i ℓ)
  exact ⟨A.dim_baseChange L, vBC A κ ℓ hb, fun σ v =>
    vBC_galRep A κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ (map_comm i σ) v⟩

/-- `MulIsogeny` gives torsion descent. -/
theorem torsionDescends_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) {K : Type} [Field K]
    [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) {L : Type} [Field L] [Algebra K L]
    (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    TorsionDescends A κ ℓ :=
  torsionDescends_of_isFinite A κ ℓ fun n =>
    (h K A _ (by exact_mod_cast (pow_pos hℓ.out.pos n).ne')).1

/-- **`AbVarBaseChangeK` from `MulIsogeny`.** -/
theorem abVarBaseChangeK_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) : AbVarBaseChangeK :=
  abVarBaseChangeK_of_torsionDescends fun K _ _ A L _ i ℓ _ => by
    letI : Algebra K L := i.toAlgebra
    exact torsionDescends_of_mulIsogeny h A _ ℓ

/-- **`AbVarBaseChange` from `MulIsogeny`** (`[n]` finite and surjective in characteristic 0). -/
theorem abVarBaseChange_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_torsionDescends fun K _ _ A L _ i ℓ _ => by
    letI : Algebra K L := i.toAlgebra
    exact torsionDescends_of_mulIsogeny h A _ ℓ

/-- **`AbVarBaseChange` from the point statement `KerUnitOpen`** (the unit section of `A[n]` is an
open immersion, char 0, `n ≠ 0`; a consequence of the published `MulEtale`). -/
theorem abVarBaseChange_of_kerUnitOpen (h : MulRigidity.KerUnitOpen) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_kerUnitOpen h)

/-- **`AbVarBaseChange` from `MulEtale`** (Mumford §4 Appl. 2, Milne Thm 8.2; char 0). -/
theorem abVarBaseChange_of_mulEtale (h : MulRigidity.MulEtale) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_mulEtale h)

/-- **`AbVarBaseChange` from the two cotangent-space glue statements** (no literature leaf). -/
theorem abVarBaseChange_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_cotangent h1 h2)

/-- `G9Glue` from `KerUnitOpen` and the weight clause. -/
theorem g9Glue_of_kerUnitOpen (h : MulRigidity.KerUnitOpen)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_kerUnitOpen h) hW

/-- `G9Glue` from the two cotangent glue statements and the weight clause. -/
theorem g9Glue_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_cotangent h1 h2) hW

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_G9Mul

-- ===== ZInQKernel/Contrib/AbVarBC/Main.lean
section LF2_AbVarBC_Main

/-!
# Base change of abelian varieties: main results

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

All statements below are proved from Mathlib alone (no leaf, no hypothesis):
* `kerUnitOpen : MulRigidity.KerUnitOpen` (mul-rigidity's leaf: the unit section of `A[n]` is an
  open immersion in characteristic `0`, `n ≠ 0`), from `Tangent.ks_isOpenImmersion`;
* `mulIsogeny : G0FibreSimple.MulIsogeny` (`[n]` is finite and surjective in characteristic `0`);
* `torsionDescends`, `tateBC_bijective`: `T_ℓ(A) ≅ T_ℓ(A_L)` Galois-equivariantly;
* `abVarBaseChangeK : AbVarBaseChangeK` (the kernel-level statement);
* **`abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange`** (task g9-derham's bridge);
* `g9Glue_of_r10Weights : G9Bridge.R10Weights → G0Galois.G9Glue`.
-/

namespace ZInQ.Contrib.AbVarBC

/-- **mul-rigidity's leaf `KerUnitOpen`, proved.** -/
theorem kerUnitOpen : MulRigidity.KerUnitOpen := by
  intro k _ _ A n hn
  exact Tangent.ks_isOpenImmersion A n hn

/-- **`MulIsogeny`, proved**: in characteristic `0`, `[n]` is finite and surjective for `n ≠ 0`. -/
theorem mulIsogeny : G0FibreSimple.MulIsogeny :=
  MulRigidity.mulIsogeny_of_kerUnitOpen kerUnitOpen

/-- `ℓ`-power torsion points of `A_L(L̄)` come from `A(K̄)` (characteristic `0`). -/
theorem torsionDescends {K : Type} [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) {L : Type}
    [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ)
    [Fact ℓ.Prime] : TorsionDescends A κ ℓ :=
  torsionDescends_of_mulIsogeny mulIsogeny A κ ℓ

/-- **`T_ℓ(A) → T_ℓ(A_L)` is bijective** (characteristic `0`). -/
theorem tateBC_bijective {K : Type} [Field K] [CharZero K] (A : _root_.HDec.PkgI3.AbVar K) {L : Type}
    [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ)
    [Fact ℓ.Prime] : Function.Bijective (tateBC A κ ℓ) :=
  tateBC_bijective_of_torsionDescends A κ ℓ (torsionDescends A κ ℓ)

/-- **Base change of abelian varieties, kernel form, proved.** -/
theorem abVarBaseChangeK : AbVarBaseChangeK :=
  abVarBaseChangeK_of_mulIsogeny mulIsogeny

/-- **`G9Bridge.AbVarBaseChange`, proved** (no hypothesis). -/
theorem abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny mulIsogeny

/-- **G9 from the weight clause alone**: `R10Weights → G9Glue`. -/
theorem g9Glue_of_r10Weights (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    _root_.HDec.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange abVarBaseChange hW

end ZInQ.Contrib.AbVarBC

end LF2_AbVarBC_Main
