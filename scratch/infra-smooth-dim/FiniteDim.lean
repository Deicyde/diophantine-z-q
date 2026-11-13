import Mathlib

/-! # Integral morphisms do not raise dimension; finite surjective morphisms preserve it

Task infra-smooth-dim. Mathlib-only. §1 copies g0-dim's cover lemmas (`scratch/g0-dim/Dim.lean`,
lines 185-224) and §2 copies g0-reverseisog's `topologicalKrullDim_le_of_specializing`
(`scratch/g0-reverseisog/ReverseIsogeny.lean`, lines 228-287), both verbatim (in namespace
`InfraSmoothDim`).

**Main results.**
* `topologicalKrullDim_le_of_isIntegralHom`: for an integral morphism `f : X ⟶ Y` of schemes,
  `dim X ≤ dim Y` (incomparability, Stacks 00GT/0ECG-style, UNVERIFIED tags).
* `topologicalKrullDim_eq_of_finite_surjective`: a finite surjective morphism `f : X ⟶ Y` has
  `dim X = dim Y`.
-/

namespace InfraSmoothDim

open Order

/-! ## §1 Covers (copied from g0-dim) -/

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


/-! ## §2 Closed surjective maps do not lower dimension (copied from g0-reverseisog) -/

/-! ### Glue (proved): a closed surjective map does not lower the Krull dimension -/

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `closure {x}` as an irreducible closed set. -/
def closureIC (x : X) : TopologicalSpace.IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- Chains of irreducible closed sets lift along a continuous, specializing map, ending at the
closure of any point over the generic point of the last member. -/
theorem lift_series [QuasiSober Y] (f : X → Y) (hc : Continuous f) (hs : SpecializingMap f)
    (p : LTSeries (TopologicalSpace.IrreducibleCloseds Y)) :
    ∀ x : X, IsGenericPoint (f x) (p.last : Set Y) →
      ∃ q : LTSeries (TopologicalSpace.IrreducibleCloseds X), q.length = p.length ∧
        q.last = closureIC x := by
  induction p using RelSeries.inductionOn' with
  | singleton W =>
    intro x _
    exact ⟨RelSeries.singleton _ (closureIC x), rfl, rfl⟩
  | snoc p W hW ih =>
    intro x hx
    rw [RelSeries.last_snoc] at hx
    obtain ⟨w', hw'⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
    have hsub : (p.last : Set Y) ⊆ W := SetLike.coe_subset_coe.mpr hW.le
    have hspec : f x ⤳ w' := hx.specializes (hsub hw'.mem)
    obtain ⟨x', hxx', hfx'⟩ := hs hspec
    obtain ⟨q, hql, hqlast⟩ := ih x' (hfx' ▸ hw')
    have hlt : q.last < closureIC x := by
      rw [hqlast]
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {x}
        exact specializes_iff_closure_subset.mp hxx'
      · intro heq
        have h1 : closure ({x'} : Set X) = closure {x} := congrArg SetLike.coe heq
        have h2 : x' ⤳ x := specializes_iff_closure_subset.mpr h1.symm.le
        have h3 : w' ⤳ f x := hfx' ▸ h2.map hc
        have h4 : (W : Set Y) ⊆ p.last := by
          rw [← hx.def, ← hw'.def]
          exact specializes_iff_closure_subset.mp h3
        exact hW.ne (SetLike.coe_injective (subset_antisymm hsub h4))
    refine ⟨q.snoc (closureIC x) hlt, ?_, RelSeries.last_snoc _ _ _⟩
    simp [hql]

/-- **Glue (proved).** A continuous, specializing (e.g. closed), surjective map `f : X → Y` to a
quasi-sober space does not lower the Krull dimension: `dim Y ≤ dim X`. -/
theorem topologicalKrullDim_le_of_specializing [QuasiSober Y] (f : X → Y) (hc : Continuous f)
    (hs : SpecializingMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨q, hql, -⟩ := lift_series f hc hs p x hy
  rw [← hql]
  exact le_iSup (fun q : LTSeries (TopologicalSpace.IrreducibleCloseds X) =>
    ((q.length : ℕ∞) : WithBot ℕ∞)) q

end Topo

/-! ## §3 Integral morphisms do not raise dimension -/

/-- An integral ring map does not raise the Krull dimension: `dim B ≤ dim A` (incomparability). -/
theorem ringKrullDim_le_of_isIntegral {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.IsIntegral) : ringKrullDim B ≤ ringKrullDim A := by
  let _ := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
  intro P Q hPQ
  have h : P.asIdeal < Q.asIdeal := hPQ
  exact Ideal.IsIntegral.under_lt_under (R := A) h

/-- The affine case. -/
theorem topologicalKrullDim_le_of_isIntegralHom_of_isAffine {Z W : Scheme} [IsAffine Z]
    [IsAffine W] (g : Z ⟶ W) [IsIntegralHom g] :
    topologicalKrullDim Z ≤ topologicalKrullDim W := by
  have h : IsIntegralHom (Z.isoSpec.inv ≫ g ≫ W.isoSpec.hom) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Z.isoSpec.inv ≫ g ≫ W.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hφ, IsIntegralHom.SpecMap_iff] at h
  rw [scheme_dim_eq_of_iso Z.isoSpec, scheme_dim_eq_of_iso W.isoSpec, spec_dim, spec_dim]
  exact ringKrullDim_le_of_isIntegral _ h

/-- **An integral morphism does not raise the dimension.** -/
theorem topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme} (f : X ⟶ Y) [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [scheme_dim_eq_iSup_cover Y.affineCover, scheme_dim_eq_iSup_cover (Y.affineCover.pullback₁ f)]
  refine iSup_mono fun i => ?_
  show topologicalKrullDim (pullback (C := Scheme) f (Y.affineCover.f i)) ≤ _
  have : IsAffine (Y.affineCover.X i) := Scheme.isAffine_affineCover Y i
  have : IsAffine (pullback (C := Scheme) f (Y.affineCover.f i)) := inferInstance
  exact topologicalKrullDim_le_of_isIntegralHom_of_isAffine (pullback.snd f (Y.affineCover.f i))

/-- **A finite surjective morphism preserves the dimension** (e.g. an isogeny of abelian
varieties). -/
theorem topologicalKrullDim_eq_of_finite_surjective {X Y : Scheme} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_isIntegralHom f)
    (topologicalKrullDim_le_of_specializing f f.continuous f.isClosedMap.specializingMap
      f.surjective)

end InfraSmoothDim

#print axioms InfraSmoothDim.topologicalKrullDim_le_of_isIntegralHom
#print axioms InfraSmoothDim.topologicalKrullDim_eq_of_finite_surjective
