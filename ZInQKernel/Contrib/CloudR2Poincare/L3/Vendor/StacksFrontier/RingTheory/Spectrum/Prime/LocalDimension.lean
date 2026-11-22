import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.Topology.Dimension.LocalKrullDim
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
Only upstream lines [(8, 392)] are retained.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory


universe u v

/-!
# Local dimension of an affine finite type scheme over a field: three descriptions

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, and let `x ∈ X` be
the point given by a prime ideal `𝔭 ⊆ S`. This file proves Stacks 00OT: the dimension `dim_x X` of
`X` at `x`, the largest dimension of an irreducible component of `X` through `x`, and the smallest
of the dimensions `dim S_𝔪 = height 𝔪` over the maximal ideals `𝔪 ⊇ 𝔭`, are all equal.

All three numbers are read in the poset `Spec S`, against the fourth quantity
`sup {coheight 𝔮 | 𝔮 a minimal prime, 𝔮 ⊆ 𝔭}`. That the second number is this supremum is the
correspondence between the components through `x` and the minimal primes below `𝔭`, together with
`dim V(𝔮) = coheight 𝔮`. The other two comparisons rest on two facts:

* *(00OS)* for `𝔮 ⊆ 𝔪` with `𝔪` maximal, `coheight 𝔮 = dim S/𝔮 ≤ height 𝔪`, because `S/𝔮` is a
  finite type domain over `k` and so has `dim S/𝔮 = height (𝔪/𝔮)`;
* *(Jacobson)* every nonempty locally closed subset of `Spec S` contains a closed point, so for
  every open `U ∋ x` there is a maximal ideal `𝔪 ⊇ 𝔭` with `𝔪 ∈ U`.

The elementary half of both comparisons is that a chain of primes contained in a set `V` all of
whose minimal primes below lie below `𝔭` has length at most that supremum: prepend a minimal prime
below the head. Applied to `V = U₀`, the complement of the union of the components *not* through
`x` — an open neighbourhood of `x`, as `Spec S` is Noetherian — this bounds `dim U₀`, and applied
to `V = ↓𝔪` for a maximal `𝔪 ∈ U₀` produced by Jacobson it bounds `height 𝔪`. In the other
direction, for an arbitrary open `U ∋ x` Jacobson produces a maximal `𝔪 ⊇ 𝔭` in `U`; then
`↓𝔪 ⊆ U`, since an open set contains every generalization of its points, so 00OS gives
`coheight 𝔮 ≤ height 𝔪 = dim ↓𝔪 ≤ dim U` for every minimal `𝔮 ⊆ 𝔭`.

## Main results

* `Stacks.Spectrum.LocalDimension.solution`: the statement of Stacks 00OT.

## Implementation notes

*The dimension of a subspace of `Spec R` is an order-theoretic Krull dimension.* A quasi-sober
subspace `U ⊆ Spec R` has `IrreducibleCloseds U ≃o Uᵒᵈ`, so `topologicalKrullDim U` is
`Order.krullDim U` computed in the poset of primes. Mathlib has this for `U` a zero locus
(`PrimeSpectrum.zeroLocusEquivIrreducibleCloseds`); the private lemmas
`subtypeEquivIrreducibleCloseds` and `topologicalKrullDim_eq_krullDim` are its verbatim
generalization to any quasi-sober subspace, which is what an open neighbourhood of `x` needs.

*Lemma 00ET is not used.* The source cites it for the minimal primes of `S_𝔪`; here the same step
is the order-theoretic observation that any chain of primes descending from `𝔪` extends to one
starting at a minimal prime, which is `Ideal.exists_minimalPrimes_le`. The formalized
correspondence (`PrimeSpectrum.irreducibleComponentsThroughEquiv`) is a bijection of sets, carrying
no dimension data, so it could not have been used for the inequality as stated.

## References

* [StacksProject 00OT](https://stacks.math.columbia.edu/tag/00OT)
-/



namespace Stacks.Spectrum.LocalDimension

open _root_.PrimeSpectrum _root_.TopologicalSpace
open Order PrimeSpectrum TopologicalSpace

section Spectrum

variable {R : Type*} [CommRing R]
#cloudR2Vendor subtypeEquivIrreducibleCloseds in

/-- The irreducible closed subsets of a quasi-sober subspace `U` of `Spec R`, ordered by
inclusion, are the points of `U` ordered by reverse inclusion of primes. This is
`PrimeSpectrum.zeroLocusEquivIrreducibleCloseds` with the zero locus replaced by any quasi-sober
subspace. -/

noncomputable def subtypeEquivIrreducibleCloseds (U : Set (PrimeSpectrum R))
    [QuasiSober U] : U ≃o (IrreducibleCloseds U)ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff p q).trans (le_iff_specializes p.1 q.1).symm)
#cloudR2Vendor topologicalKrullDim_eq_krullDim in

/-- The topological Krull dimension of a quasi-sober subspace of `Spec R` is the Krull dimension
of its poset of primes. -/

lemma topologicalKrullDim_eq_krullDim (U : Set (PrimeSpectrum R)) [QuasiSober U] :
    topologicalKrullDim U = krullDim U := by
  rw [topologicalKrullDim, ← krullDim_orderDual (α := IrreducibleCloseds U)]
  exact (krullDim_eq_of_orderIso (subtypeEquivIrreducibleCloseds U)).symm
#cloudR2Vendor zeroLocus_asIdeal in

/-- The zero locus of a prime ideal is the set of primes containing it. -/
lemma zeroLocus_asIdeal (q : PrimeSpectrum R) :
    zeroLocus (q.asIdeal : Set R) = Set.Ici q := by
  ext p
  simp [mem_zeroLocus, Set.mem_Ici, ← asIdeal_le_asIdeal, SetLike.coe_subset_coe]
#cloudR2Vendor topologicalKrullDim_zeroLocus in

/-- The dimension of the irreducible closed subset `V(𝔮)` is the coheight of `𝔮`. -/

lemma topologicalKrullDim_zeroLocus (q : PrimeSpectrum R) :
    topologicalKrullDim (zeroLocus (q.asIdeal : Set R)) = (coheight q : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_krullDim, zeroLocus_asIdeal, ← coheight_eq_krullDim_Ici]
#cloudR2Vendor mem_of_le_of_isOpen in

/-- An open subset of `Spec R` contains every generalization of each of its points. -/
lemma mem_of_le_of_isOpen {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {p p' : PrimeSpectrum R} (h : p ≤ p') (h' : p' ∈ U) : p ∈ U :=
  ((le_iff_specializes p p').mp h).mem_open hU h'
#cloudR2Vendor exists_isMaximal_mem in

/-- In a Jacobson ring, every open subset of `Spec R` containing a point `x` contains a closed
point of `Spec R` above `x`, because the locally closed set `V(x) ∩ U` is nonempty. -/
lemma exists_isMaximal_mem [IsJacobsonRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {x : PrimeSpectrum R} (hx : x ∈ U) :
    ∃ m : PrimeSpectrum R, m.asIdeal.IsMaximal ∧ x ≤ m ∧ m ∈ U := by
  obtain ⟨m, ⟨hm₁, hm₂⟩, hm₃⟩ := nonempty_inter_closedPoints
    (Z := zeroLocus (x.asIdeal : Set R) ∩ U) ⟨x, by simp [zeroLocus_asIdeal], hx⟩
    ((isClosed_zeroLocus _).isLocallyClosed.inter hU.isLocallyClosed)
  exact ⟨m, (isClosed_singleton_iff_isMaximal m).mp hm₃,
    by simpa [zeroLocus_asIdeal] using hm₁, hm₂⟩
#cloudR2Vendor exists_isMin_asIdeal_eq in

/-- A minimal prime ideal is the ideal of a minimal point of `Spec R`. -/
private lemma exists_isMin_asIdeal_eq {I : Ideal R} (hI : I ∈ minimalPrimes R) :
    ∃ q : PrimeSpectrum R, IsMin q ∧ q.asIdeal = I :=
  ⟨⟨I, hI.1.1⟩, isMin_iff.mpr hI, rfl⟩
#cloudR2Vendor iSup_irreducibleComponents_eq in

/-- The source's number (2), the largest dimension of an irreducible component of `Spec R` through
`x`, is the largest coheight of a minimal prime below `x`. -/
lemma iSup_irreducibleComponents_eq (x : PrimeSpectrum R) :
    (⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum R) | x ∈ Z}, topologicalKrullDim Z) =
      ⨆ q ∈ {q : PrimeSpectrum R | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  refine le_antisymm (iSup₂_le fun Z hZ => ?_) (iSup₂_le fun q hq => ?_)
  · obtain ⟨hZc, hxZ⟩ := hZ
    have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZc
    have hI : vanishingIdeal Z ∈ minimalPrimes R := by
      rwa [vanishingIdeal_mem_minimalPrimes, hZcl.closure_eq]
    obtain ⟨q, hmin, hq⟩ := exists_isMin_asIdeal_eq hI
    have hZq : Z = zeroLocus (q.asIdeal : Set R) := by
      rw [hq, zeroLocus_vanishingIdeal_eq_closure, hZcl.closure_eq]
    have hle : q ≤ x :=
      (asIdeal_le_asIdeal _ _).mp
        (SetLike.coe_subset_coe.mp ((mem_zeroLocus _ _).mp (hZq ▸ hxZ)))
    exact le_iSup₂_of_le q ⟨hmin, hle⟩ (by rw [hZq, topologicalKrullDim_zeroLocus])
  · obtain ⟨hmin, hle⟩ := hq
    have hZ : zeroLocus (q.asIdeal : Set R) ∈ irreducibleComponents (PrimeSpectrum R) := by
      rw [zeroLocus_ideal_mem_irreducibleComponents, q.isPrime.radical]
      exact isMin_iff.mp hmin
    have hmem : zeroLocus (q.asIdeal : Set R) ∈
        {Z ∈ irreducibleComponents (PrimeSpectrum R) | x ∈ Z} :=
      ⟨hZ, by rwa [zeroLocus_asIdeal]⟩
    exact (topologicalKrullDim_zeroLocus q).symm.trans_le
      (le_biSup (fun Z : Set (PrimeSpectrum R) => topologicalKrullDim Z) hmem)
#cloudR2Vendor krullDim_le_iSup_coheight in

/-- If every minimal prime below a point of `V` lies below `x`, then every chain of primes in `V`
is at most as long as the coheight of some minimal prime below `x`: pass to a minimal prime below
the head of the chain. -/
lemma krullDim_le_iSup_coheight {x : PrimeSpectrum R} (V : Set (PrimeSpectrum R))
    (hV : ∀ p ∈ V, ∀ q : PrimeSpectrum R, IsMin q → q ≤ p → q ≤ x) :
    krullDim V ≤ ⨆ q ∈ {q : PrimeSpectrum R | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  refine iSup_le fun p => ?_
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥)
    (J := (p.head : PrimeSpectrum R).asIdeal) bot_le
  obtain ⟨q, hmin, rfl⟩ := exists_isMin_asIdeal_eq hQ
  have hqhead : q ≤ (p.head : PrimeSpectrum R) := (asIdeal_le_asIdeal _ _).mp hQle
  have hlen : (p.length : ℕ∞) ≤ coheight q :=
    length_le_coheight_head.trans
      ((coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h => h) p.head).trans
        (coheight_anti hqhead))
  exact le_iSup₂_of_le q ⟨hmin, hV _ p.head.2 q hmin hqhead⟩ (by exact_mod_cast hlen)
#cloudR2Vendor isOpen_setOf_forall_isMin_le in

/-- The set of points of `Spec R` through which no irreducible component other than the ones
through `x` passes is open: its complement is the union of the finitely many other components. -/
lemma isOpen_setOf_forall_isMin_le [IsNoetherianRing R] (x : PrimeSpectrum R) :
    IsOpen {p : PrimeSpectrum R | ∀ q : PrimeSpectrum R, IsMin q → q ≤ p → q ≤ x} := by
  have hfin : {q : PrimeSpectrum R | IsMin q ∧ ¬ q ≤ x}.Finite :=
    ((minimalPrimes.finite_of_isNoetherianRing R).preimage
      fun _ _ _ _ h => PrimeSpectrum.ext h).subset fun q hq => isMin_iff.mp hq.1
  have hset : {p : PrimeSpectrum R | ∀ q : PrimeSpectrum R, IsMin q → q ≤ p → q ≤ x} =
      (⋃ q ∈ {q : PrimeSpectrum R | IsMin q ∧ ¬ q ≤ x}, Set.Ici q)ᶜ := by
    ext p
    refine ⟨fun h hp => ?_, fun h q hmin hqp => ?_⟩
    · obtain ⟨q, hqB, hqp⟩ := Set.mem_iUnion₂.mp hp
      exact hqB.2 (h q hqB.1 hqp)
    · by_contra hnle
      exact h (Set.mem_iUnion₂.mpr ⟨q, ⟨hmin, hnle⟩, hqp⟩)
  rw [hset, isOpen_compl_iff]
  refine hfin.isClosed_biUnion fun q _ => ?_
  rw [← zeroLocus_asIdeal]
  exact isClosed_zeroLocus _

end Spectrum

section FiniteType
#cloudR2Vendor coheight_le_height in

/-- **Stacks 00OS, read at `S/𝔮`.** For a prime `𝔮` below a maximal ideal `𝔪` of a finite type
`k`-algebra, `dim S/𝔮 = coheight 𝔮` is at most `height 𝔪`: the finite type domain `S/𝔮` has
`dim S/𝔮 = height (𝔪/𝔮)`, and a chain of primes of `S/𝔮` below `𝔪/𝔮` is one of `S` below `𝔪`. -/
lemma coheight_le_height (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] {q m : PrimeSpectrum S} (hm : IsMax m) (hqm : q ≤ m) :
    coheight q ≤ height m := by
  have hz : zeroLocus (q.asIdeal : Set S) = Set.Ici q := zeroLocus_asIdeal q
  set e := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (Ideal.Quotient.mk q.asIdeal)
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  set m' : ↥(zeroLocus (q.asIdeal : Set S)) := ⟨m, by rwa [hz]⟩
  have hm'' : IsMax m' := fun b hb => Subtype.coe_le_coe.mp (hm (Subtype.coe_le_coe.mpr hb))
  have hmax : IsMax (e.symm m') := by
    intro b hb
    have h₁ : m' ≤ e b := by simpa using e.monotone hb
    simpa using e.symm.monotone (hm'' h₁)
  have : (e.symm m').asIdeal.IsMaximal := isMax_iff.mp hmax
  -- Change notice: only the maximal-ideal dimension part of 00OS is used here;
  -- derive it directly from 00P0, avoiding maximal-chain/regular-ring machinery.
  have h00P0 := ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg
    k (S ⧸ q.asIdeal) (FractionRing (S ⧸ q.asIdeal))
  have h00OS : ringKrullDim (S ⧸ q.asIdeal) =
      ((e.symm m').asIdeal.height : WithBot ℕ∞) := by
    rw [h00P0.1, ← h00P0.2 (e.symm m').asIdeal (Localization.AtPrime (e.symm m').asIdeal),
      IsLocalization.AtPrime.ringKrullDim_eq_height (e.symm m').asIdeal
        (Localization.AtPrime (e.symm m').asIdeal)]
  have key : (coheight q : WithBot ℕ∞) = (height m' : WithBot ℕ∞) := by
    rw [coheight_eq_krullDim_Ici, ← hz, ← ringKrullDim_quotient, h00OS,
      PrimeSpectrum.height_eq_orderHeight, height_orderIso e.symm m']
  rw [show coheight q = height m' by exact_mod_cast key]
  exact height_le_height_apply_of_strictMono Subtype.val (fun _ _ h => h) m'
#cloudR2Vendor localKrullDim_eq_iSup_coheight in

/-- The source's number (1), the dimension of `Spec S` at `x`, is the largest coheight of a
minimal prime below `x`. -/
lemma localKrullDim_eq_iSup_coheight (k : Type u) [Field k] {S : Type v} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (x : PrimeSpectrum S) :
    localKrullDim (PrimeSpectrum S) x =
      ⨆ q ∈ {q : PrimeSpectrum S | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le {p : PrimeSpectrum S | ∀ q : PrimeSpectrum S, IsMin q → q ≤ p → q ≤ x}
      (iInf_le_of_le (isOpen_setOf_forall_isMin_le x) (iInf_le_of_le (fun _ _ h => h) ?_))
    have := (isOpen_setOf_forall_isMin_le x).isOpenEmbedding_subtypeVal.quasiSober
    rw [topologicalKrullDim_eq_krullDim]
    exact krullDim_le_iSup_coheight _ fun _ hp => hp
  · refine le_iInf fun U => le_iInf fun hU => le_iInf fun hxU => iSup₂_le fun q hq => ?_
    obtain ⟨m, hmax, hxm, hmU⟩ := exists_isMaximal_mem hU hxU
    have := hU.isOpenEmbedding_subtypeVal.quasiSober
    rw [topologicalKrullDim_eq_krullDim]
    calc (coheight q : WithBot ℕ∞) ≤ (height m : WithBot ℕ∞) := by
          exact_mod_cast coheight_le_height k (isMax_iff.mpr hmax) (hq.2.trans hxm)
      _ = krullDim (Set.Iic m) := height_eq_krullDim_Iic m
      _ ≤ krullDim U := krullDim_le_of_strictMono
          (fun p => (⟨p.1, mem_of_le_of_isOpen hU p.2 hmU⟩ : U)) fun _ _ h => h
#cloudR2Vendor iInf_height_eq_iSup_coheight in

/-- The source's number (3), the smallest height of a maximal ideal above `x`, is the largest
coheight of a minimal prime below `x`. -/
lemma iInf_height_eq_iSup_coheight (k : Type u) [Field k] {S : Type v} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (x : PrimeSpectrum S) :
    (⨅ 𝔪 ∈ {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪}, (𝔪.height : WithBot ℕ∞)) =
      ⨆ q ∈ {q : PrimeSpectrum S | IsMin q ∧ q ≤ x}, (coheight q : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  refine le_antisymm ?_ (le_iInf₂ fun 𝔪 h𝔪 => ?_)
  · obtain ⟨m, hmax, hxm, hmU⟩ :=
      exists_isMaximal_mem (isOpen_setOf_forall_isMin_le x) (fun _ _ h => h)
    refine (iInf₂_le m.asIdeal ⟨hmax, (asIdeal_le_asIdeal _ _).mpr hxm⟩).trans ?_
    rw [PrimeSpectrum.height_eq_orderHeight, height_eq_krullDim_Iic]
    exact krullDim_le_iSup_coheight _ fun p hp q hq hqp => hmU q hq (hqp.trans hp)
  · have h𝔪p : 𝔪.IsPrime := h𝔪.1.isPrime
    refine iSup₂_le fun q hq => ?_
    have hxm : x ≤ (⟨𝔪, h𝔪p⟩ : PrimeSpectrum S) := (asIdeal_le_asIdeal _ _).mp h𝔪.2
    rw [PrimeSpectrum.height_eq_orderHeight (⟨𝔪, h𝔪p⟩ : PrimeSpectrum S)]
    exact_mod_cast coheight_le_height k (isMax_iff.mpr h𝔪.1) (hq.2.trans hxm)

end FiniteType
#cloudR2Vendor solution in

/-- The statement of Stacks 00OT: for `S` of finite type over a field `k` and `x ∈ Spec S`, the
dimension of `Spec S` at `x` is both the largest dimension of an irreducible component through `x`
and the smallest height of a maximal ideal containing `x`. Both are identified with the largest
coheight of a minimal prime below `x`. -/
theorem solution
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | x ∈ Z}, topologicalKrullDim Z) ∧
      (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨅ 𝔪 ∈ {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪}, (𝔪.height : WithBot ℕ∞)) :=
  ⟨(localKrullDim_eq_iSup_coheight k x).trans (iSup_irreducibleComponents_eq x).symm,
    (localKrullDim_eq_iSup_coheight k x).trans (iInf_height_eq_iSup_coheight k x).symm⟩

end Stacks.Spectrum.LocalDimension

/-!
# Local dimension of an affine finite type scheme over a field: three descriptions

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, and let `x ∈ X`
be the point given by a prime ideal `𝔭 ⊆ S`. Three numbers attached to `x` agree:

1. the dimension `dim_x X` of `X` at `x`, the least dimension of an open neighbourhood of `x`;
2. the largest dimension of an irreducible component of `X` through `x`;
3. the smallest of the dimensions `dim S_𝔪` over the maximal ideals `𝔪 ⊇ 𝔭`.

Both extrema can be strictly smaller than `dim X`: on the union of a plane and a line meeting it,
all three numbers are `1` at the generic point of the line, while `dim X = 2`.

The source's proof: `X` has finitely many irreducible components, so removing those that miss `x`
leaves an open `U ∋ x` whose components are exactly the `Z ∩ U` for the components `Z` through
`x`; each is a nonempty open subset of `Z` containing a closed point, because `S` is Jacobson, and
so has the full dimension of `Z` by Lemma 00OS — this gives (1) = (2). For a maximal ideal
`𝔪 ⊇ 𝔭` the minimal primes of `S_𝔪` are the `𝔮_i S_𝔪` for the minimal primes `𝔮_i ⊆ 𝔪`
(Lemma 00ET), whence `dim S_𝔪` is the largest dimension of a component through the point of `𝔪`,
again by Lemma 00OS; choosing `𝔪` inside `V(𝔭)` minus the other components — possible since `S`
is Jacobson and `𝔭` itself lies there — realizes (2) as one such `dim S_𝔪`, and no `𝔪` gives less.

## Main results

* `PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height`: the three
  numbers agree.

## Implementation notes

*`dim_x X` is `TopologicalSpace.localKrullDim`.* That definition is Topology Definition 0055 (4) —
the infimum of `topologicalKrullDim U` over the open neighbourhoods `U` of `x` — and
`topologicalKrullDim` is the source's dimension of a space, the supremum of lengths of chains of
irreducible closed subsets. The point `x` and its prime ideal are one datum, `x : PrimeSpectrum S`
with `𝔭 = x.asIdeal`, rather than a prime together with the assertion that `x` corresponds to it;
Stacks 00P1 is stated the same way.

*`dim S_𝔪` is `𝔪.height`.* The Krull dimension of any model of the local ring of `S` at `𝔪` is
`𝔪.height`, by `IsLocalization.AtPrime.ringKrullDim_eq_height`, so the model-independent
`Ideal.height` says the source's `dim(S_𝔪)` with no localization data in the statement, as in
Stacks 00OS and 00P1. Reading the third number at a given `A` with `[IsLocalization.AtPrime A 𝔪]`
is that one rewrite.

*The components are Mathlib's `irreducibleComponents`, and their dimension is again
`topologicalKrullDim`.* "Passing through `x`" is `x ∈ Z`, so the family of the source's second
number is the set `{Z ∈ irreducibleComponents (PrimeSpectrum S) | x ∈ Z}`. Stating (2) inside the
topology of `X`, rather than as `⨆ 𝔮 ∈ minimalPrimes S, 𝔮 ≤ 𝔭 → ringKrullDim (S ⧸ 𝔮)`, keeps the
statement about the space the source's `dim_x` is about; the translation is the inclusion-reversing
order isomorphism `PrimeSpectrum.pointsEquivIrreducibleCloseds` together with
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.

*The source's `max` and `min` are `iSup` and `iInf` in `WithBot ℕ∞`.* This is no weakening: `X` is
a Noetherian space so it has finitely many components, at least one through `x`, and the maximal
ideals containing `𝔭` are nonempty, `WithBot ℕ∞` is a complete linear order, and a nonempty
finite family and a nonempty family of naturals both attain their extremum. The values live in
`WithBot ℕ∞ ≃ {-∞} ∪ ℤ≥0 ∪ {+∞}` because that is where `topologicalKrullDim` lives; the heights,
which are `ℕ∞`, are coerced.

Faithfulness to [StacksProject 00OT].

1. No hypothesis is dead. `Field k` cannot be relaxed to a commutative ring: for `k = S = ℤ_p`,
   a finite type `k`-algebra, at the generic point `x = ⊥` of the two-point space `Spec ℤ_p`, the
   open set `{⊥}` makes the first number `0` while the only component is all of `Spec ℤ_p` and the
   second number is `1`. `Algebra.FiniteType k S` cannot be dropped: for the non-finite-type
   `k`-algebra `S = k[t]_{(t)}` the same computation at `x = ⊥` gives `0 ≠ 1`. The point `x`
   occurs in all three numbers.
2. The base and the ring are the source's: `k` is a field, `S` is a `k`-algebra of finite type,
   and the topology, the components and the heights are all those of `S` itself — no base change,
   no polynomial ring presenting `S`, and no localization appearing as data.
3. The quantities the source names are pinned, not asserted to exist: the neighbourhoods are the
   open sets of `PrimeSpectrum S` containing `x`, the components are `irreducibleComponents`, the
   third family is indexed by the maximal ideals above `x.asIdeal`, and the conclusion is a pair
   of equations determining `dim_x X`, not bounds on it.
4. The instantiation is not degenerate: for `S = k[X, Y]` and `x = (X)` all three numbers are `2`;
   for `S = k[X, Y, Z] ⧸ (XY, XZ)` — the plane `X = 0` meeting the line `Y = Z = 0` — at the
   generic point `x = (Y, Z)` of the line all three are `1`, strictly less than `dim S = 2`, and
   there the infimum over `𝔪` is essential: the origin `(X, Y, Z)` contributes height `2`. At the
   point of `S = k` all three are `0`.

## References

* [StacksProject 00OT](https://stacks.math.columbia.edu/tag/00OT)

## Tags

dimension, local dimension, Krull dimension, height, irreducible component, finite type algebra,
Jacobson
-/




namespace PrimeSpectrum
#cloudR2Vendor localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height in

/-- **Stacks 00OT.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S`,
and let `x ∈ X` be a point, with prime ideal `𝔭 = x.asIdeal`. Then the dimension of `X` at `x` is
both the largest dimension of an irreducible component of `X` through `x` and the smallest of the
dimensions `dim S_𝔪 = height 𝔪` over the maximal ideals `𝔪 ⊇ 𝔭`. -/

theorem localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | x ∈ Z}, topologicalKrullDim Z) ∧
      (TopologicalSpace.localKrullDim (PrimeSpectrum S) x =
        ⨅ 𝔪 ∈ {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪}, (𝔪.height : WithBot ℕ∞)) :=
  Stacks.Spectrum.LocalDimension.solution k x

end PrimeSpectrum


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
