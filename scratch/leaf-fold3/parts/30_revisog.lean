-- (leaf-fold2: copied from scratch/g0-assemble2/parts/30_revisog.lean; 0 HDec name-resolution edits)

noncomputable section

namespace HSyn

/-! ## §3″. g0-reverseisog (2026-11-13): `ReverseIsogeny` proved (task g0-reverseisog)

Appended to a verbatim copy of `scratch/g0-split/Split.lean` (wip/g0-split c20fa62b). Route A: the
textbook leaf `IsogenyQuasiInverse`. Route B (no new leaf): the bundle's R19 (Gaudron-Rémond),
H5's finiteness (`r.h5.1`) and piece 1 `DimFinite`. -/

namespace G0RevIsog

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Topology

/-- **LEAF (Mumford; Milne).** An isogeny `φ : A → B` of abelian varieties over a field `K` (a
homomorphism of group schemes that is finite and surjective) has a quasi-inverse: an isogeny
`ψ : B → A` and an integer `n ≥ 1` (the degree of `φ`) with `ψ ∘ φ = [n]_A` and `φ ∘ ψ = [n]_B`.
Here `[n]_A` is `(𝟙 A)ⁿ` in Mathlib's group of morphisms into the group object `A`.
Sources (numbers UNVERIFIED, from memory, no network): Mumford, *Abelian Varieties*, §7 Remark after
Thm 4 / §8 (over an algebraically closed field); Milne, *Abelian Varieties* (in Cornell-Silverman,
*Arithmetic Geometry*, 1986), §8, Prop. 8.1/Remark 8.2? and Milne's course notes *Abelian
Varieties* (2008) I, Prop. 7.1 and Remark 7.2 (over an arbitrary field `k`). The proof there: `ker φ`
is a finite group scheme of order `n = deg φ`, hence killed by `n` (Deligne, commutative case), so
`[n]_A` factors through the quotient `A/ker φ ≅ B` (Mumford §7 Thm 4 / §12). -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ ZInQ.DefFaltings.IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n

/-- **Glue interface (the property `ReverseIsogeny` actually uses).** Over a number field, an
isogeny `A → B` of abelian varieties has an isogeny `B → A` in the other direction. It follows from
the textbook leaf `IsogenyQuasiInverse` (`isogenyReverseExists_of_quasiInverse`) and, in
`SplitRev.lean`, from the bundle's research leaf R19 (Gaudron-Rémond) with H5's finiteness and
`DimFinite` (`isogenyReverseExists_of_r19`). -/
def IsogenyReverseExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ → ∃ ψ : B.X ⟶ A.X, ZInQ.DefFaltings.IsIsogeny ψ

/-- **Proved.** The leaf gives the interface. -/
theorem isogenyReverseExists_of_quasiInverse (hQ : IsogenyQuasiInverse) : IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨ψ, -, -, hψ, -, -⟩ := hQ K A B φ hφ
  exact ⟨ψ, hψ⟩

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

/-- **Glue (proved).** A finite surjective morphism of schemes does not lower the dimension of the
target: `dim Y ≤ dim X` (finite ⇒ integral ⇒ universally closed ⇒ closed, Mathlib). -/
theorem dim_le_of_finite_surjective {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  topologicalKrullDim_le_of_specializing f f.continuous f.isClosedMap.specializingMap f.surjective

/-- **Glue (proved).** Two isogenies in opposite directions force equal dimensions. -/
theorem dim_eq_of_isogenies {K : Type} [Field K] {A B : ZInQ.DefFaltings.AbVar K}
    (φ : A.X ⟶ B.X) (ψ : B.X ⟶ A.X) (hφ : ZInQ.DefFaltings.IsIsogeny φ)
    (hψ : ZInQ.DefFaltings.IsIsogeny ψ) : B.dim = A.dim := by
  obtain ⟨-, hφf, hφs⟩ := hφ
  obtain ⟨-, hψf, hψs⟩ := hψ
  exact le_antisymm (dim_le_of_finite_surjective φ.left) (dim_le_of_finite_surjective ψ.left)

/-- **Glue (proved): the map `P → J`.** If `(p₁, p₂) : P → A × Z` is an isomorphism of group
schemes and `(f, g) : A × Z → J` is finite and surjective, then `h = f ∘ p₁ + g ∘ p₂ : P → J` is an
isogeny. -/
theorem isogeny_of_product {L : Type} [Field L] (A J Z : PkgI3.AbVar L)
    (P : ZInQ.DefFaltings.AbVar L) (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J)
    (hP : G0Split.IsProductOf P.X A.X Z.X)
    (hiso : PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)) :
    ∃ h : P.X ⟶ J.X, IsMonHom h ∧ IsFinite h.left ∧ Surjective h.left := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hlift⟩ := hP
  obtain ⟨hfin, hsurj⟩ := hiso
  have hm : lift p₁ p₂ ≫ (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) =
      p₁ ≫ f.hom * p₂ ≫ g.hom := by
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have hmon : IsMonHom (p₁ ≫ f.hom * p₂ ≫ g.hom) := by
    change IsMonHom (lift (p₁ ≫ f.hom) (p₂ ≫ g.hom) ≫ μ[J.X])
    infer_instance
  refine ⟨lift p₁ p₂ ≫ (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom), ?_, ?_, ?_⟩
  · rw [hm]; exact hmon
  · rw [Over.comp_left]
    infer_instance
  · rw [Over.comp_left]
    infer_instance

/-- **`ReverseIsogeny` (G17 after Poincaré), proved from the interface `IsogenyReverseExists`.**
The map `h = f ∘ p₁ + g ∘ p₂ : P → J` is an isogeny (`isogeny_of_product`); the interface gives an
isogeny `ψ : J → P`; `h` and `ψ` give `dim J = dim P` (`dim_eq_of_isogenies`). -/
theorem reverseIsogeny_of_exists (hE : IsogenyReverseExists) : G0Split.ReverseIsogeny := by
  intro L _ _ A J Z P f g hP hiso
  obtain ⟨h, hh⟩ := isogeny_of_product A J Z P f g hP hiso
  replace hh : ZInQ.DefFaltings.IsIsogeny (A := P) (B := (LeafAdopt.abVarEquiv L).symm J) h := hh
  obtain ⟨ψ, hψ⟩ := hE L P ((LeafAdopt.abVarEquiv L).symm J) h hh
  exact ⟨ψ, hψ, dim_eq_of_isogenies h ψ hh hψ⟩

/-- **`ReverseIsogeny`, proved from the textbook leaf `IsogenyQuasiInverse`.** -/
theorem reverseIsogeny (hQ : IsogenyQuasiInverse) : G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_quasiInverse hQ)


/-- **Proved (Route B, no new leaf).** Gaudron-Rémond (R19, already a field of `ResearchLeaves`)
gives isogenies in both directions between isogenous abelian varieties over a number field; its
inputs `dim A = g ∈ ℕ` and `h_F(A) = x ∈ ℝ` come from piece 1 `DimFinite` and H5's finiteness. -/
theorem isogenyReverseExists_of_r19 (r19 : ZInQ.DefFaltings.R19_GaudronRemond)
    (hfin : ZInQ.DefFaltings.StableHeightFinite) (hDimF : G0Split.DimFinite) :
    IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨g, hg⟩ := hDimF K (LeafAdopt.abVarEquiv K A)
  obtain ⟨-, ψ, hψ, -⟩ := r19 K A B g (ZInQ.DefFaltings.faltingsHeight A) hg
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm ⟨φ, hφ⟩
  exact ⟨ψ, hψ⟩

/-- **`ReverseIsogeny` from the leaf bundle and piece 1 (proved).** -/
theorem reverseIsogeny_of_leaves (r : ResearchLeaves) (hDimF : G0Split.DimFinite) :
    G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_r19 r.r19 r.h5.1 hDimF)

end G0RevIsog

end HSyn

end
