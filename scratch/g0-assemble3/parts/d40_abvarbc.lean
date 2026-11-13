/-! ## g0-assemble3: g9-abvarbc (ZInQKernel/Contrib/AbVarBC/{Dim,Points,Tate,Torsion,Mul,G9Instance,G9Mul}.lean, in
import order, verbatim minus imports and `#print` lines; each in its own section). Edits (g9-derham's layer copies
`ZInQ.Contrib.G9.{PkgI3, PkgI4.I3}.AbVar` and `G0Galois` are not in this file, as for part a95: names resolve to
Leaves.lean's): `ZInQ.Contrib.G9.PkgI3.AbVar` → `_root_.PkgI3.AbVar`, `ZInQ.Contrib.G9.PkgI4.I3.AbVar` →
`_root_.PkgI4.I3.AbVar`, `ZInQ.Contrib.G9.G0Galois.G9Glue` → `_root_.G0Galois.G9Glue`; an `end` is appended where a
file leaves its `noncomputable section` open at end of file. `KerUnit`, `Tangent` and `Main`
(its own proof of `MulIsogeny`) are not copied: `MulIsogeny` is infra-stalks' `MulRigidity.mulIsogeny` (part b10),
applied through `G9Mul`'s `abVarBaseChange_of_mulIsogeny` in part d45. -/
section G0A3file_Dim
-- (file ZInQKernel/Contrib/AbVarBC/Dim.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

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

end G0A3file_Dim

section G0A3file_Points
-- (file ZInQKernel/Contrib/AbVarBC/Points.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

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

end G0A3file_Points

section G0A3file_Tate
-- (file ZInQKernel/Contrib/AbVarBC/Tate.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

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

end G0A3file_Tate

section G0A3file_Torsion
-- (file ZInQKernel/Contrib/AbVarBC/Torsion.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

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

end G0A3file_Torsion

section G0A3file_Mul
-- (file ZInQKernel/Contrib/AbVarBC/Mul.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

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

end G0A3file_Mul

section G0A3file_G9Instance
-- (file ZInQKernel/Contrib/AbVarBC/G9Instance.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

/-!
# Base change of abelian varieties, IV: the instance `G9Bridge.AbVarBaseChange`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

`G9Bridge.AbVarBaseChange` (task g9-derham, `ZInQKernel/Contrib/G9/LocalModel.lean`) is stated over
two verbatim copies of the kernel's abelian varieties: `_root_.PkgI3.AbVar`
(`Contrib/G9/I3Layer.lean`) and `_root_.PkgI4.I3.AbVar` (`Contrib/G9/I4Layer.lean`).
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
def ofG9 (A : _root_.PkgI3.AbVar K) : _root_.PkgI3.AbVar K :=
  @_root_.PkgI3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

/-- A kernel `PkgI3.AbVar`, as pkg-I4's copy `PkgI4.I3.AbVar` (in G9's namespace). -/
def toI4 (A : _root_.PkgI3.AbVar K) : _root_.PkgI4.I3.AbVar K :=
  @_root_.PkgI4.I3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

theorem dim_ofG9 (A : _root_.PkgI3.AbVar K) : (ofG9 A).dim = A.dim := rfl

theorem dim_toI4 (A : _root_.PkgI3.AbVar K) : (toI4 A).dim = A.dim := rfl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ` of G9's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vOfG9 (A : _root_.PkgI3.AbVar K) : A.V ℓ ≃ₗ[ℚ_[ℓ]] (ofG9 A).V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vOfG9_galRep (A : _root_.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : A.V ℓ) : vOfG9 ℓ A (A.galRep ℓ σ v) = (ofG9 A).galRep ℓ σ (vOfG9 ℓ A v) := rfl

theorem vOfG9_symm_galRep (A : _root_.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (ofG9 A).V ℓ) :
    (vOfG9 ℓ A).symm ((ofG9 A).galRep ℓ σ v) = A.galRep ℓ σ ((vOfG9 ℓ A).symm v) := rfl

/-- `V_ℓ` of pkg-I4's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vToI4 (A : _root_.PkgI3.AbVar K) : (toI4 A).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vToI4_galRep (A : _root_.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
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
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
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
theorem abVarBaseChange_of_tateModuleFree (hT : _root_.PkgI3.TateModuleFree) :
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
theorem g9Glue_of_tateModuleFree (hT : _root_.PkgI3.TateModuleFree)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : _root_.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_tateModuleFree hT) hW

end ZInQ.Contrib.AbVarBC

end G0A3file_G9Instance

section G0A3file_G9Mul
-- (file ZInQKernel/Contrib/AbVarBC/G9Mul.lean, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)

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
  ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
    (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
    letI : Algebra K L := i.toAlgebra
    (A.baseChange L).dim = A.dim ∧
      ∃ c : (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ,
        ∀ σ v, c ((A.baseChange L).galRep ℓ σ v) =
          A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

/-- `AbVarBaseChangeK` from torsion descent. -/
theorem abVarBaseChangeK_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
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
    [CharZero K] (A : _root_.PkgI3.AbVar K) {L : Type} [Field L] [Algebra K L]
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
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : _root_.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_kerUnitOpen h) hW

/-- `G9Glue` from the two cotangent glue statements and the weight clause. -/
theorem g9Glue_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    _root_.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_cotangent h1 h2) hW

end ZInQ.Contrib.AbVarBC

end G0A3file_G9Mul
