import Mathlib

/-!
# Flat modules over a local ring with nilpotent maximal ideal are free (Lane RC6)

This file formalizes the first paragraph of the proof of Lemma `ex:limits-inner-limit`
("Finite free models and retained inner-limit diagrams"), manuscript lines 4409-4414:

> Let $A$ be an Artin local ring with nilpotent maximal ideal $\mathfrak m$.
> A flat $A$-module is free, including in infinite rank: lift a basis
> modulo $\mathfrak m$, use nilpotence for surjectivity, and flatness and
> nilpotence for vanishing of the kernel. A continuous finite-coefficient
> cochain module is a filtered union of modules of functions on finite
> clopen partitions, hence is flat.

All main declarations are `PROVED`.

## Main declarations

* `nakayama_nilpotent_le`, `nakayama_nilpotent`, `eq_bot_of_le_smul_of_isNilpotent`:
  Nakayama's lemma for a nilpotent ideal, with no finiteness hypothesis
  ("use nilpotence for surjectivity").
* `ker_inf_smul_top_eq_smul_ker`: for `0 → K → F → M → 0` with `M` flat,
  `K ∩ I F = I K`, i.e. `Tor₁(A/I, M) = 0` ("flatness ... for vanishing of the kernel").
* `exists_residual_lift`, `lifted_residual_basis_span`,
  `lifted_residual_basis_linearIndependent`, `lifted_residual_bases_are_bases`,
  `liftedResidualBasis`, `liftedResidualBasisOfBasis`: lifted residual bases are bases
  ("lift a basis modulo 𝔪").
* `flat_module_free`: a flat module over a local ring with nilpotent maximal ideal is free,
  with no finiteness assumption ("A flat A-module is free, including in infinite rank").
* `flat_of_directed_union`: a directed union of flat submodules is flat.
* `blockFunctions`, `locallyConstant_directed_union_free`, `flat_locallyConstant`,
  `free_locallyConstant`,
  `flat_continuousCochains`, `free_continuousCochains`, `free_pi_continuousCochains`:
  the cochain module is the directed union of the modules of functions on finite clopen
  partitions, hence flat, hence free over `A`.
* `ElliotRing`, `ElliotRing.isLocalRing`, `ElliotRing.isNilpotent_maximalIdeal`: Elliot's
  coefficient rings `A_i = (ℤ/2^i)[t]/(t^i)` (manuscript line 2725) satisfy the hypotheses;
  `examples` at the end show the hypotheses are satisfiable (also for `ZMod 4`).

## Conventions

The maximal ideal is `IsLocalRing.maximalIdeal A` (written `𝔪` in docstrings), the residue
field is `IsLocalRing.ResidueField A` (written `k`). "M modulo 𝔪" is realized as the
`k`-vector space `k ⊗[A] M`; it is canonically `M ⧸ 𝔪 • ⊤` as an `A`-module
(`TensorProduct.quotTensorEquivQuotSMul`), and the kernel of `x ↦ 1 ⊗ₜ x` is exactly
`𝔪 • ⊤` (`ker_residue_tmul`).
-/

namespace ZInQ.Manuscript.RC.Limits

open TensorProduct IsLocalRing

universe u v w

/-! ### Nakayama's lemma for a nilpotent ideal -/

section Nakayama

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- Nakayama's lemma for a nilpotent ideal, general form: if `N' ≤ N ⊔ I • N'` and `I` is
nilpotent, then `N' ≤ N`.  No finiteness hypothesis is needed: iterating gives
`N' ≤ N ⊔ I ^ k • N'` for every `k`, and `I ^ n = 0`.

Manuscript lines 4410-4411 ("use nilpotence for surjectivity"); also used for the
vanishing of the kernel.  Kind: `PROVED`. -/
theorem nakayama_nilpotent_le {I : Ideal A} (hI : IsNilpotent I)
    {N N' : Submodule A M} (h : N' ≤ N ⊔ I • N') : N' ≤ N := by
  obtain ⟨n, hn⟩ := hI
  have key : ∀ k : ℕ, N' ≤ N ⊔ I ^ k • N' := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact le_sup_right
    | succ k ih =>
      calc N' ≤ N ⊔ I • N' := h
        _ ≤ N ⊔ I • (N ⊔ I ^ k • N') := sup_le_sup_left (Submodule.smul_mono le_rfl ih) _
        _ = N ⊔ (I • N ⊔ I • I ^ k • N') := by rw [Submodule.smul_sup]
        _ ≤ N ⊔ I ^ (k + 1) • N' := by
          refine sup_le le_sup_left (sup_le (le_sup_of_le_left Submodule.smul_le_right) ?_)
          rw [pow_succ', Submodule.mul_smul]
          exact le_sup_right
  have hlast := key n
  rwa [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at hlast

/-- Nakayama's lemma for a nilpotent ideal, in the form used for surjectivity:
if `N ⊔ I • ⊤ = ⊤` (i.e. `N + I M = M`) and `I` is nilpotent, then `N = ⊤`.
No finite generation of `M` or `N` is assumed.

Manuscript lines 4410-4411 ("use nilpotence for surjectivity").  Kind: `PROVED`. -/
theorem nakayama_nilpotent {I : Ideal A} (hI : IsNilpotent I) {N : Submodule A M}
    (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ :=
  top_le_iff.mp (nakayama_nilpotent_le hI h.ge)

/-- Nakayama's lemma for a nilpotent ideal, in the form used for the kernel:
if `N ≤ I • N` (i.e. `N = I N`) and `I` is nilpotent, then `N = 0`.

Manuscript line 4412 ("nilpotence for vanishing of the kernel").  Kind: `PROVED`. -/
theorem eq_bot_of_le_smul_of_isNilpotent {I : Ideal A} (hI : IsNilpotent I)
    {N : Submodule A M} (h : N ≤ I • N) : N = ⊥ :=
  le_bot_iff.mp (nakayama_nilpotent_le hI (by rwa [bot_sup_eq]))

end Nakayama

/-! ### Flatness: `K ∩ I F = I K` -/

section Tor

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- The flatness step: for an exact sequence `0 → K → F → M → 0` (here `K = ker φ` for a
surjection `φ : F → M`) with `M` flat, and any ideal `I`, one has `K ∩ I F = I K`.
Equivalently `(A ⧸ I) ⊗ K → (A ⧸ I) ⊗ F` is injective, which is the vanishing of
`Tor₁(A ⧸ I, M)`; this is obtained from Mathlib's
`lTensor_injective_of_exact_of_exact_of_rTensor_injective`, using that `I ⊗ M → M` is
injective (flatness of `M`).

Manuscript line 4412 ("flatness ... for vanishing of the kernel").  Kind: `PROVED`.
DEPARTURE (generalization only): `F` is an arbitrary module (not necessarily free) and `I`
is an arbitrary ideal; the manuscript uses `F = A^(I)` and `I = 𝔪`. -/
theorem ker_inf_smul_top_eq_smul_ker [Module.Flat A M] {F : Type w} [AddCommGroup F]
    [Module A F] (φ : F →ₗ[A] M) (hφ : Function.Surjective φ) (I : Ideal A) :
    LinearMap.ker φ ⊓ I • ⊤ = I • LinearMap.ker φ := by
  apply le_antisymm
  · rintro x ⟨hxK, hxI⟩
    have hinj : Function.Injective ((LinearMap.ker φ).subtype.lTensor (A ⧸ I)) :=
      lTensor_injective_of_exact_of_exact_of_rTensor_injective
        (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
        (LinearMap.exact_subtype_ker_map φ) hφ
        (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
        (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
    have h1 : (1 : A ⧸ I) ⊗ₜ[A] x = 0 := by
      rw [← TensorProduct.mk_apply, ← LinearMap.mem_ker, LinearMap.ker_tensorProductMk]
      exact hxI
    have h2 : (1 : A ⧸ I) ⊗ₜ[A] (⟨x, hxK⟩ : LinearMap.ker φ) = 0 := by
      apply hinj
      rw [LinearMap.lTensor_tmul, map_zero]
      exact h1
    have h3 : (⟨x, hxK⟩ : LinearMap.ker φ) ∈ I • (⊤ : Submodule A (LinearMap.ker φ)) := by
      rw [← LinearMap.ker_tensorProductMk, LinearMap.mem_ker, TensorProduct.mk_apply]
      exact h2
    exact (Submodule.mem_smul_top_iff I _ _).mp h3
  · exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)

end Tor

/-! ### Lifted residual bases are bases -/

section LiftedBasis

variable {A : Type u} [CommRing A] [IsLocalRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- "M modulo 𝔪": the kernel of `x ↦ 1 ⊗ₜ x : M → k ⊗[A] M` is `𝔪 • ⊤ = 𝔪 M`.
Kind: `PROVED` (Mathlib's `LinearMap.ker_tensorProductMk`, as `k = A ⧸ 𝔪`). -/
theorem ker_residue_tmul :
    LinearMap.ker (TensorProduct.mk A (ResidueField A) M 1) = maximalIdeal A • ⊤ :=
  LinearMap.ker_tensorProductMk M

/-- Every residue class modulo `𝔪` lifts to `M`: `x ↦ 1 ⊗ₜ x : M → k ⊗[A] M` is surjective.
Kind: `PROVED`. -/
theorem exists_residual_lift (y : ResidueField A ⊗[A] M) :
    ∃ x : M, (1 : ResidueField A) ⊗ₜ[A] x = y :=
  TensorProduct.mk_surjective A M (ResidueField A)
    (by rw [ResidueField.algebraMap_eq]; exact residue_surjective) y

/-- If the residues `1 ⊗ₜ v i` span `k ⊗[A] M` over `k`, then the span of the `v i`
together with `𝔪 M` is all of `M`, i.e. `N + 𝔪 M = M` for `N = span A (range v)`.

Manuscript lines 4410-4411 ("lift a basis modulo 𝔪").  Kind: `PROVED`. -/
theorem lifted_residual_basis_span_sup {ι : Type w} (v : ι → M)
    (hsp : Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⊤) :
    Submodule.span A (Set.range v) ⊔ maximalIdeal A • ⊤ = ⊤ := by
  have hsurj : Function.Surjective (algebraMap A (ResidueField A)) := by
    rw [ResidueField.algebraMap_eq]
    exact residue_surjective
  rw [eq_top_iff]
  rintro x -
  have hx : (1 : ResidueField A) ⊗ₜ[A] x ∈ Submodule.span A
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) := by
    rw [← Submodule.restrictScalars_span A (ResidueField A) hsurj, hsp]
    trivial
  have hmap : Submodule.span A (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) =
      (Submodule.span A (Set.range v)).map (TensorProduct.mk A (ResidueField A) M 1) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hxy : x - y ∈ maximalIdeal A • (⊤ : Submodule A M) := by
    rw [← ker_residue_tmul, LinearMap.mem_ker, map_sub, hyx, TensorProduct.mk_apply, sub_self]
  have hsplit : x = y + (x - y) := by abel
  rw [hsplit]
  exact Submodule.add_mem_sup hy hxy

/-- Lifted residual bases span: if `𝔪` is nilpotent and the residues `1 ⊗ₜ v i` span
`k ⊗[A] M`, then the `v i` span `M`, i.e. the induced map `A^(ι) → M` is surjective.
No finiteness hypothesis.

Manuscript lines 4410-4411 ("lift a basis modulo 𝔪, use nilpotence for surjectivity").
Kind: `PROVED`. -/
theorem lifted_residual_basis_span (hnil : IsNilpotent (maximalIdeal A)) {ι : Type w}
    (v : ι → M)
    (hsp : Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⊤) :
    Submodule.span A (Set.range v) = ⊤ :=
  nakayama_nilpotent hnil (lifted_residual_basis_span_sup v hsp)

/-- If the residues `1 ⊗ₜ v i` are linearly independent over `k`, then the kernel `K` of
the induced map `A^(ι) → M` lies in `𝔪 A^(ι)`: every coefficient of a relation lies in `𝔪`.

Manuscript lines 4410-4412 (first half of "vanishing of the kernel").  Kind: `PROVED`. -/
theorem ker_linearCombination_le_maximalIdeal_smul {ι : Type w} (v : ι → M)
    (hli : LinearIndependent (ResidueField A) fun i => (1 : ResidueField A) ⊗ₜ[A] v i) :
    LinearMap.ker (Finsupp.linearCombination A v) ≤ maximalIdeal A • ⊤ := by
  intro f hf
  rw [LinearMap.mem_ker, Finsupp.linearCombination_apply] at hf
  have hcoef : ∀ i, f i ∈ maximalIdeal A := by
    intro i
    by_cases hi : i ∈ f.support
    · rw [← residue_eq_zero_iff]
      refine linearIndependent_iff'.mp hli f.support (fun j => residue A (f j)) ?_ i hi
      have h0 := congrArg (TensorProduct.mk A (ResidueField A) M 1) hf
      rw [map_zero, Finsupp.sum, map_sum] at h0
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h0
      rw [LinearMap.map_smul, TensorProduct.mk_apply, ← ResidueField.algebraMap_eq,
        algebraMap_smul]
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact zero_mem _
  rw [← Finsupp.sum_single f, Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← Finsupp.smul_single_one]
  exact Submodule.smul_mem_smul (hcoef i) Submodule.mem_top

/-- Lifted residual bases are linearly independent: if `𝔪` is nilpotent, `M` is flat and the
residues `1 ⊗ₜ v i` form a `k`-basis of `k ⊗[A] M`, then `v` is linearly independent over `A`.
Elliot's argument: the map `φ : A^(ι) → M` is surjective (`lifted_residual_basis_span`); its
kernel `K` lies in `𝔪 A^(ι)` (`ker_linearCombination_le_maximalIdeal_smul`), so by flatness
`K = K ∩ 𝔪 A^(ι) = 𝔪 K` (`ker_inf_smul_top_eq_smul_ker`), hence `K = 0` by nilpotence
(`eq_bot_of_le_smul_of_isNilpotent`).

Manuscript lines 4410-4412 ("flatness and nilpotence for vanishing of the kernel").
Kind: `PROVED`.  (Mathlib also has `Module.IsLocalRing.linearIndependent_of_flat`, a
different route via the equational criterion that does not need nilpotence; it is not
used here, to follow the manuscript's argument.) -/
theorem lifted_residual_basis_linearIndependent (hnil : IsNilpotent (maximalIdeal A))
    [Module.Flat A M] {ι : Type w} (v : ι → M)
    (hli : LinearIndependent (ResidueField A) fun i => (1 : ResidueField A) ⊗ₜ[A] v i)
    (hsp : Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⊤) :
    LinearIndependent A v := by
  have hφ : Function.Surjective (Finsupp.linearCombination A v) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact lifted_residual_basis_span hnil v hsp
  rw [linearIndependent_iff_ker]
  apply eq_bot_of_le_smul_of_isNilpotent hnil
  rw [← ker_inf_smul_top_eq_smul_ker _ hφ]
  exact le_inf le_rfl (ker_linearCombination_le_maximalIdeal_smul v hli)

/-- Lifted residual bases are bases: over a local ring `A` with nilpotent maximal ideal `𝔪`,
for a flat module `M` and any family `v : ι → M` whose residues `1 ⊗ₜ v i` form a basis of
the `k`-vector space `k ⊗[A] M` ("M modulo 𝔪"), the family `v` is an `A`-basis of `M`
(`coe_liftedResidualBasis`).  No finiteness hypothesis on `M` or `ι`.

Manuscript lines 4410-4412 ("lift a basis modulo 𝔪, use nilpotence for surjectivity, and
flatness and nilpotence for vanishing of the kernel").  Kind: `PROVED`.
DEPARTURE (form only): "M modulo 𝔪" is the `k`-vector space `k ⊗[A] M`, canonically
isomorphic to `M ⧸ 𝔪 M` (`TensorProduct.quotTensorEquivQuotSMul`; the kernel of
`x ↦ 1 ⊗ₜ x` is `𝔪 M` by `ker_residue_tmul`). -/
noncomputable def liftedResidualBasis (hnil : IsNilpotent (maximalIdeal A)) [Module.Flat A M]
    {ι : Type w} (v : ι → M)
    (hli : LinearIndependent (ResidueField A) fun i => (1 : ResidueField A) ⊗ₜ[A] v i)
    (hsp : Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⊤) :
    Module.Basis ι A M :=
  Module.Basis.mk (lifted_residual_basis_linearIndependent hnil v hli hsp)
    (lifted_residual_basis_span hnil v hsp).ge

/-- The basis `liftedResidualBasis` is the given family `v`.  Kind: `PROVED`. -/
@[simp]
theorem coe_liftedResidualBasis (hnil : IsNilpotent (maximalIdeal A)) [Module.Flat A M]
    {ι : Type w} (v : ι → M)
    (hli : LinearIndependent (ResidueField A) fun i => (1 : ResidueField A) ⊗ₜ[A] v i)
    (hsp : Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⊤) :
    ⇑(liftedResidualBasis hnil v hli hsp) = v :=
  Module.Basis.coe_mk _ _

/-- **Lifted residual bases are bases** (existence form of `liftedResidualBasis`): over a
local ring with nilpotent maximal ideal, for a flat module `M`, any family `v : ι → M` whose
image in `k ⊗[A] M` ("M modulo 𝔪") is a `k`-basis is itself an `A`-basis of `M`.

Manuscript lines 4410-4412.  Kind: `PROVED`.  DEPARTURE (form only): as for
`liftedResidualBasis`. -/
theorem lifted_residual_bases_are_bases (hnil : IsNilpotent (maximalIdeal A))
    [Module.Flat A M] {ι : Type w} (v : ι → M)
    (hli : LinearIndependent (ResidueField A) fun i => (1 : ResidueField A) ⊗ₜ[A] v i)
    (hsp : Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⊤) :
    ∃ b : Module.Basis ι A M, ⇑b = v :=
  ⟨liftedResidualBasis hnil v hli hsp, coe_liftedResidualBasis hnil v hli hsp⟩

/-- Lifted residual bases are bases, basis form: given a `k`-basis `b` of `k ⊗[A] M` and
lifts `v i` with `1 ⊗ₜ v i = b i`, the family `v` is an `A`-basis of `M`
(`coe_liftedResidualBasisOfBasis`).

Manuscript lines 4410-4412 ("lift a basis modulo 𝔪").  Kind: `PROVED`. -/
noncomputable def liftedResidualBasisOfBasis (hnil : IsNilpotent (maximalIdeal A))
    [Module.Flat A M] {ι : Type w}
    (b : Module.Basis ι (ResidueField A) (ResidueField A ⊗[A] M)) (v : ι → M)
    (hv : ∀ i, (1 : ResidueField A) ⊗ₜ[A] v i = b i) : Module.Basis ι A M :=
  have hb : (fun i => (1 : ResidueField A) ⊗ₜ[A] v i) = ⇑b := funext hv
  liftedResidualBasis hnil v (by rw [hb]; exact b.linearIndependent)
    (by rw [hb]; exact b.span_eq)

/-- The basis `liftedResidualBasisOfBasis` is the given family of lifts `v`.
Kind: `PROVED`. -/
@[simp]
theorem coe_liftedResidualBasisOfBasis (hnil : IsNilpotent (maximalIdeal A))
    [Module.Flat A M] {ι : Type w}
    (b : Module.Basis ι (ResidueField A) (ResidueField A ⊗[A] M)) (v : ι → M)
    (hv : ∀ i, (1 : ResidueField A) ⊗ₜ[A] v i = b i) :
    ⇑(liftedResidualBasisOfBasis hnil b v hv) = v := by
  unfold liftedResidualBasisOfBasis
  exact coe_liftedResidualBasis _ _ _ _

/-- **A flat `A`-module is free, including in infinite rank.**  Let `A` be a local ring
whose maximal ideal `𝔪` is nilpotent.  Every flat `A`-module `M`, with no finiteness
assumption, is free.  Proof (Elliot): choose a basis of the `k`-vector space
`k ⊗[A] M = M ⧸ 𝔪 M`, lift it to a family `v` in `M`, and apply
`liftedResidualBasisOfBasis`.

Manuscript lines 4409-4412.  Kind: `PROVED`.
DEPARTURE (generalization only): the manuscript's "Artin local ring with nilpotent maximal
ideal" is formalized as `IsLocalRing A` plus `IsNilpotent (maximalIdeal A)`; the Artinian
hypothesis is not used (for a Noetherian local ring the two are equivalent, Mathlib's
`isArtinianRing_iff_isNilpotent_maximalIdeal`; an Artinian local ring satisfies the
hypothesis by `isNilpotent_maximalIdeal_of_isArtinianRing`).  Mathlib's
`Module.free_of_flat_of_isLocalRing` is the finitely generated case (over any local ring). -/
theorem flat_module_free (hnil : IsNilpotent (maximalIdeal A)) [Module.Flat A M] :
    Module.Free A M := by
  let b := Module.Free.chooseBasis (ResidueField A) (ResidueField A ⊗[A] M)
  choose v hv using fun i => exists_residual_lift (b i)
  exact Module.Free.of_basis (liftedResidualBasisOfBasis hnil b v hv)

/-- An Artinian local ring has nilpotent maximal ideal, so it satisfies the hypothesis of
`flat_module_free`.  Kind: `PROVED`. -/
theorem isNilpotent_maximalIdeal_of_isArtinianRing [IsArtinianRing A] :
    IsNilpotent (maximalIdeal A) := by
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

end LiftedBasis

/-! ### Directed unions of flat submodules are flat -/

section DirectedUnion

/-- A module that is the union of a directed family of flat (for example free) submodules is
flat.  Proof by the equational criterion for flatness
(`Module.Flat.iff_forall_isTrivialRelation`): a relation `∑ fⱼ xⱼ = 0` in `M` involves
finitely many `xⱼ`, which all lie in one `S i` by directedness; the relation is trivial in
the flat module `S i`, hence in `M`.

Manuscript lines 4412-4414 ("is a filtered union of modules ... hence is flat").
Kind: `PROVED`. -/
theorem flat_of_directed_union {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M]
    [Module A M] {ι : Type w} (S : ι → Submodule A M) (hdir : Directed (· ≤ ·) S)
    (hsup : ⨆ i, S i = ⊤) (hflat : ∀ i, Module.Flat A (S i)) : Module.Flat A M := by
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x hfx
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hx : ∀ j, x j = 0 := fun j => by
      have hj : x j ∈ ⨆ i, S i := hsup ▸ Submodule.mem_top
      rw [iSup_of_empty] at hj
      exact (Submodule.mem_bot A).mp hj
    exact ⟨0, fun _ => Fin.elim0, Fin.elim0, fun j => by simp [hx j], fun j => Fin.elim0 j⟩
  · classical
    have hmem : ∀ j, ∃ i, x j ∈ S i := fun j =>
      (Submodule.mem_iSup_of_directed S hdir).mp (hsup ▸ Submodule.mem_top)
    choose c hc using hmem
    obtain ⟨i₀, hi₀⟩ := hdir.finset_le (Finset.univ.image c)
    have hx₀ : ∀ j, x j ∈ S i₀ := fun j =>
      hi₀ (c j) (Finset.mem_image_of_mem c (Finset.mem_univ j)) (hc j)
    have := hflat i₀
    let x' : Fin l → S i₀ := fun j => ⟨x j, hx₀ j⟩
    have hrel : ∑ j, f j • x' j = 0 := by
      apply Subtype.ext
      simpa [x'] using hfx
    obtain ⟨m, a, y, hxy, hfa⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
    refine ⟨m, a, fun j => (y j : M), fun j => ?_, hfa⟩
    have hj := congrArg Subtype.val (hxy j)
    simpa [x'] using hj

end DirectedUnion

/-! ### Continuous cochains with discrete coefficients -/

section Cochains

variable (A : Type u) [CommRing A] {X : Type v} [TopologicalSpace X]
  (N : Type w) [AddCommGroup N] [Module A N]

/-- Functions on the blocks of a finite clopen partition, pulled back to `X`.  A finite
clopen partition of `X` is modeled by `Q : DiscreteQuotient X` (its blocks are the fibers of
`Q.proj`, which are clopen; there are finitely many when `X` is compact).  This is the
`A`-linear map `(Q → N) → LocallyConstant X N`, `g ↦ g ∘ Q.proj`.

Manuscript lines 4412-4414 ("modules of functions on finite clopen partitions").
Kind: `PROVED` (definition). -/
def blockFunctionsMap (Q : DiscreteQuotient X) : (Q → N) →ₗ[A] LocallyConstant X N where
  toFun g := ⟨g ∘ Q.proj, (IsLocallyConstant.of_discrete g).comp_continuous Q.proj_continuous⟩
  map_add' _ _ := LocallyConstant.ext fun _ => rfl
  map_smul' _ _ := LocallyConstant.ext fun _ => rfl

/-- Evaluation of `blockFunctionsMap`.  Kind: `PROVED`. -/
@[simp]
theorem blockFunctionsMap_apply (Q : DiscreteQuotient X) (g : Q → N) (x : X) :
    blockFunctionsMap A N Q g x = g (Q.proj x) :=
  rfl

/-- The module of functions on the finite clopen partition `Q`: the locally constant
functions `X → N` that are constant on each block of `Q` (`mem_blockFunctions_iff`).

Manuscript lines 4412-4414 ("modules of functions on finite clopen partitions").
Kind: `PROVED` (definition). -/
def blockFunctions (Q : DiscreteQuotient X) : Submodule A (LocallyConstant X N) :=
  LinearMap.range (blockFunctionsMap A N Q)

/-- `blockFunctions A N Q` consists exactly of the functions constant on the blocks of `Q`.
Kind: `PROVED`. -/
theorem mem_blockFunctions_iff (Q : DiscreteQuotient X) (f : LocallyConstant X N) :
    f ∈ blockFunctions A N Q ↔ ∀ x y, Q.proj x = Q.proj y → f x = f y := by
  constructor
  · rintro ⟨g, rfl⟩ x y hxy
    rw [blockFunctionsMap_apply, blockFunctionsMap_apply, hxy]
  · intro hf
    refine ⟨fun q => f (Q.proj_surjective q).choose, ?_⟩
    ext x
    rw [blockFunctionsMap_apply]
    exact hf _ _ (Q.proj_surjective (Q.proj x)).choose_spec

/-- `g ↦ g ∘ Q.proj` is injective, since `Q.proj` is surjective.  Kind: `PROVED`. -/
theorem blockFunctionsMap_injective (Q : DiscreteQuotient X) :
    Function.Injective (blockFunctionsMap A N Q) := by
  intro g₁ g₂ h
  funext q
  obtain ⟨x, rfl⟩ := Q.proj_surjective q
  rw [← blockFunctionsMap_apply A N Q g₁ x, ← blockFunctionsMap_apply A N Q g₂ x, h]

/-- The module of functions on a finite clopen partition is isomorphic to `Q → N`, a finite
power of `N`; it is flat when `N` is (for instance free, e.g. `N = A ^ r`).
Kind: `PROVED`. -/
theorem flat_blockFunctions [CompactSpace X] [Module.Flat A N] (Q : DiscreteQuotient X) :
    Module.Flat A (blockFunctions A N Q) := by
  have : Fintype Q := Fintype.ofFinite Q
  have : Module.Flat A (Q → N) := Module.Flat.of_linearEquiv
    (DFinsupp.linearEquivFunOnFintype (R := A) (M := fun _ : Q => N)).symm
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofInjective _ (blockFunctionsMap_injective A N Q)).symm

/-- The module of functions on a finite clopen partition is free when `N` is free (e.g.
`N = A` or `N = A ^ r`): it is isomorphic to the finite power `Q → N`.
Kind: `PROVED`. -/
theorem free_blockFunctions [CompactSpace X] [Module.Free A N] (Q : DiscreteQuotient X) :
    Module.Free A (blockFunctions A N Q) :=
  Module.Free.of_equiv (LinearEquiv.ofInjective _ (blockFunctionsMap_injective A N Q))

/-- The modules of functions on finite clopen partitions form a directed (filtered) family:
`Q₁ ⊓ Q₂` refines both `Q₁` and `Q₂`.  Kind: `PROVED`. -/
theorem directed_blockFunctions :
    Directed (· ≤ ·) (blockFunctions A N : DiscreteQuotient X → Submodule A _) := by
  intro Q₁ Q₂
  refine ⟨Q₁ ⊓ Q₂, ?_, ?_⟩
  · intro f hf
    rw [mem_blockFunctions_iff] at hf ⊢
    intro x y hxy
    apply hf
    rw [← DiscreteQuotient.ofLE_proj (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁) x,
      ← DiscreteQuotient.ofLE_proj (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁) y, hxy]
  · intro f hf
    rw [mem_blockFunctions_iff] at hf ⊢
    intro x y hxy
    apply hf
    rw [← DiscreteQuotient.ofLE_proj (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂) x,
      ← DiscreteQuotient.ofLE_proj (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂) y, hxy]

/-- Every locally constant function lies in the module of functions on some finite clopen
partition (its own fibers, `LocallyConstant.discreteQuotient`), so these modules exhaust
`LocallyConstant X N`.  Kind: `PROVED`. -/
theorem iSup_blockFunctions :
    ⨆ Q : DiscreteQuotient X, blockFunctions A N Q = ⊤ := by
  rw [eq_top_iff]
  intro f _
  refine Submodule.mem_iSup_of_mem f.discreteQuotient ⟨⇑f.lift, ?_⟩
  ext x
  rfl

/-- **The cochain module is a filtered union of modules of functions on finite clopen
partitions**: for compact `X` and free `N` (e.g. `N = A` or `N = A ^ r`), the submodules
`blockFunctions A N Q` (`Q` a finite clopen partition) of `LocallyConstant X N` form a
directed family, exhaust `LocallyConstant X N`, and are free.

Manuscript lines 4412-4414.  Kind: `PROVED`. -/
theorem locallyConstant_directed_union_free [CompactSpace X] [Module.Free A N] :
    Directed (· ≤ ·) (blockFunctions A N : DiscreteQuotient X → Submodule A _) ∧
      ⨆ Q : DiscreteQuotient X, blockFunctions A N Q = ⊤ ∧
      ∀ Q : DiscreteQuotient X, Module.Free A (blockFunctions A N Q) :=
  ⟨directed_blockFunctions A N, iSup_blockFunctions A N, free_blockFunctions A N⟩

/-- **A continuous finite-coefficient cochain module is flat.**  For a compact space `X`
(e.g. a profinite group power `G ^ n`) and a flat `A`-module `N` (e.g. finite free
`N = A ^ r`), the module `LocallyConstant X N` of locally constant (equivalently, for
discrete `N`, continuous: `IsLocallyConstant.iff_continuous`) functions is the directed
union of the modules `blockFunctions A N Q` of functions on finite clopen partitions,
hence flat (`flat_of_directed_union`).

Manuscript lines 4412-4414.  Kind: `PROVED`.
DEPARTURE (generalization only): only compactness of `X` is used (Hausdorff and total
disconnectedness are not needed), and the coefficient module is any flat module. -/
theorem flat_locallyConstant [CompactSpace X] [Module.Flat A N] :
    Module.Flat A (LocallyConstant X N) :=
  flat_of_directed_union (blockFunctions A N) (directed_blockFunctions A N)
    (iSup_blockFunctions A N) (flat_blockFunctions A N)

/-- Over a local ring with nilpotent maximal ideal, the cochain module
`LocallyConstant X N` (compact `X`, flat `N`) is free, by `flat_locallyConstant` and
`flat_module_free`.

Manuscript lines 4409-4414.  Kind: `PROVED`. -/
theorem free_locallyConstant [IsLocalRing A] (hnil : IsNilpotent (maximalIdeal A))
    [CompactSpace X] [Module.Flat A N] : Module.Free A (LocallyConstant X N) :=
  have := flat_locallyConstant A (X := X) N
  flat_module_free hnil

/-- Continuous cochains `G ^ n → A ^ r` with discrete finite free coefficients, i.e. the
module `LocallyConstant (Fin n → G) (Fin r → A)`, form a flat `A`-module for any compact
(e.g. profinite) `G`.

Manuscript lines 4393-4394 and 4412-4414.  Kind: `PROVED`. -/
theorem flat_continuousCochains (G : Type v) [TopologicalSpace G] [CompactSpace G]
    (n r : ℕ) : Module.Flat A (LocallyConstant (Fin n → G) (Fin r → A)) :=
  flat_locallyConstant A (Fin r → A)

/-- Over a local ring with nilpotent maximal ideal, the continuous cochains
`G ^ n → A ^ r` with discrete coefficients form a free `A`-module (in general of infinite
rank).

Manuscript lines 4393-4394 and 4409-4414.  Kind: `PROVED`. -/
theorem free_continuousCochains [IsLocalRing A] (hnil : IsNilpotent (maximalIdeal A))
    (G : Type v) [TopologicalSpace G] [CompactSpace G] (n r : ℕ) :
    Module.Free A (LocallyConstant (Fin n → G) (Fin r → A)) :=
  free_locallyConstant A (Fin r → A) hnil

/-- The finite-power form: `(LocallyConstant (G ^ n) A) ^ r` is free over a local ring with
nilpotent maximal ideal.

Manuscript lines 4393-4394 and 4409-4414.  Kind: `PROVED`. -/
theorem free_pi_continuousCochains [IsLocalRing A] (hnil : IsNilpotent (maximalIdeal A))
    (G : Type v) [TopologicalSpace G] [CompactSpace G] (n r : ℕ) :
    Module.Free A (Fin r → LocallyConstant (Fin n → G) A) :=
  have := free_locallyConstant A A hnil (X := Fin n → G)
  inferInstance

end Cochains

/-! ### Elliot's coefficient rings `A_i = (ℤ/2^i)[t]/(t^i)` -/

/-- Elliot's finite coefficient ring `A_i = (ℤ/2^i ℤ)[t]/t^i` (manuscript line 2725).
For `i ≠ 0` it is a local ring (`ElliotRing.isLocalRing`) with nilpotent maximal ideal
(`ElliotRing.isNilpotent_maximalIdeal`), so `flat_module_free` applies to it.
Kind: `PROVED` (definition). -/
abbrev ElliotRing (i : ℕ) : Type :=
  Polynomial (ZMod (2 ^ i)) ⧸ Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ i))) ^ i}

namespace ElliotRing

variable (i : ℕ)

/-- The class of the variable `t` in `A_i`. -/
noncomputable abbrev t : ElliotRing i := Ideal.Quotient.mk _ Polynomial.X

/-- `t ^ i = 0` in `A_i`.  Kind: `PROVED`. -/
theorem isNilpotent_t : IsNilpotent (t i) :=
  ⟨i, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl⟩

/-- Every element of `A_i` is `c + t q` with `c ∈ ℤ/2^i`.  Kind: `PROVED`. -/
theorem exists_eq_algebraMap_add_t_mul (b : ElliotRing i) :
    ∃ c : ZMod (2 ^ i), ∃ q : ElliotRing i,
      b = algebraMap (ZMod (2 ^ i)) (ElliotRing i) c + t i * q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨p.coeff 0, Ideal.Quotient.mk _ p.divX, ?_⟩
  conv_lhs => rw [← Polynomial.X_mul_divX_add p]
  rw [map_add, map_mul, add_comm, Polynomial.C_eq_algebraMap, Ideal.Quotient.mk_algebraMap]

/-- `c + t q` is a unit when `c` is a unit (`t q` is nilpotent).  Kind: `PROVED`. -/
theorem isUnit_algebraMap_add_t_mul {c : ZMod (2 ^ i)} (hc : IsUnit c) (q : ElliotRing i) :
    IsUnit (algebraMap (ZMod (2 ^ i)) (ElliotRing i) c + t i * q) :=
  IsNilpotent.isUnit_add_left_of_commute
    ((Commute.all _ _).isNilpotent_mul_right (isNilpotent_t i)) (hc.map _) (Commute.all _ _)

variable [NeZero i]

/-- `A_i` (`i ≠ 0`) is nontrivial: `t ^ i` is not a unit.  Kind: `PROVED`. -/
instance : Nontrivial (ElliotRing i) := by
  rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top,
    isUnit_pow_iff (NeZero.ne i)]
  exact Polynomial.not_isUnit_X

/-- Elliot's ring `A_i` (`i ≠ 0`) is a local ring: `c + t q` is a unit when `c` is, and
`ℤ/2^i` is local.  Kind: `PROVED`. -/
instance isLocalRing : IsLocalRing (ElliotRing i) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  obtain ⟨c, q, rfl⟩ := exists_eq_algebraMap_add_t_mul i b
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hc | hc
  · exact Or.inl (isUnit_algebraMap_add_t_mul i hc q)
  · right
    have h1 : 1 - (algebraMap (ZMod (2 ^ i)) (ElliotRing i) c + t i * q) =
        algebraMap (ZMod (2 ^ i)) (ElliotRing i) (1 - c) + t i * (-q) := by
      rw [map_sub, map_one]
      ring
    rw [h1]
    exact isUnit_algebraMap_add_t_mul i hc (-q)

/-- The maximal ideal of Elliot's ring `A_i` (`i ≠ 0`) is nilpotent: it is finitely generated
(`A_i` is Noetherian) and consists of nilpotent elements `c + t q` with `c ∈ 2 ℤ/2^i`.
Kind: `PROVED`. -/
theorem isNilpotent_maximalIdeal : IsNilpotent (maximalIdeal (ElliotRing i)) := by
  rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
  intro b hb
  rw [mem_nilradical]
  obtain ⟨c, q, rfl⟩ := exists_eq_algebraMap_add_t_mul i b
  have hc : c ∈ maximalIdeal (ZMod (2 ^ i)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hc
    exact (IsLocalRing.mem_maximalIdeal _).mp hb (isUnit_algebraMap_add_t_mul i hc q)
  obtain ⟨n, hn⟩ := isNilpotent_maximalIdeal_of_isArtinianRing (A := ZMod (2 ^ i))
  have hcn : IsNilpotent c := by
    refine ⟨n, ?_⟩
    have hpow := Ideal.pow_mem_pow hc n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hpow
  exact (Commute.all _ _).isNilpotent_add (hcn.map _)
    ((Commute.all _ _).isNilpotent_mul_right (isNilpotent_t i))

end ElliotRing

/-! ### The hypotheses are satisfiable -/

section Examples

/-- `ZMod 4 = ZMod (2 ^ 2)` is a local ring. -/
local instance : IsLocalRing (ZMod 4) := inferInstanceAs (IsLocalRing (ZMod (2 ^ 2)))

/-- The maximal ideal of `ZMod 4` is nilpotent. -/
example : IsNilpotent (maximalIdeal (ZMod 4)) := isNilpotent_maximalIdeal_of_isArtinianRing

/-- `flat_module_free` over `ZMod 4`. -/
example (M : Type) [AddCommGroup M] [Module (ZMod 4) M] [Module.Flat (ZMod 4) M] :
    Module.Free (ZMod 4) M :=
  flat_module_free isNilpotent_maximalIdeal_of_isArtinianRing

/-- `ZMod (2 ^ i)` (`i ≠ 0`) is local with nilpotent maximal ideal. -/
example (i : ℕ) [NeZero i] :
    IsLocalRing (ZMod (2 ^ i)) ∧ IsNilpotent (maximalIdeal (ZMod (2 ^ i))) :=
  ⟨inferInstance, isNilpotent_maximalIdeal_of_isArtinianRing⟩

/-- Elliot's ring `A_3 = (ℤ/8)[t]/(t^3)` is local with nilpotent maximal ideal. -/
example : IsLocalRing (ElliotRing 3) ∧ IsNilpotent (maximalIdeal (ElliotRing 3)) :=
  ⟨inferInstance, ElliotRing.isNilpotent_maximalIdeal 3⟩

/-- An infinite-rank instance over Elliot's ring `A_i`: the locally constant
`A_i ^ r`-valued functions on the Cantor space `ℕ → Bool` form a free `A_i`-module. -/
example (i r : ℕ) [NeZero i] :
    Module.Free (ElliotRing i) (LocallyConstant (ℕ → Bool) (Fin r → ElliotRing i)) :=
  free_locallyConstant _ _ (ElliotRing.isNilpotent_maximalIdeal i)

/-- Continuous cochains `G ^ n → A_i ^ r` (with `G` compact, e.g. profinite) form a free
`A_i`-module. -/
example (i : ℕ) [NeZero i] (G : Type) [TopologicalSpace G] [CompactSpace G] (n r : ℕ) :
    Module.Free (ElliotRing i) (LocallyConstant (Fin n → G) (Fin r → ElliotRing i)) :=
  free_continuousCochains _ (ElliotRing.isNilpotent_maximalIdeal i) G n r

end Examples

end ZInQ.Manuscript.RC.Limits
