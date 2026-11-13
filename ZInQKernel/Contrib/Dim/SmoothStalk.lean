import ZInQKernel.Contrib.Dim.SubmersivePresentation

/-!
# Local rings and dimension of smooth schemes over a field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task infra-smooth-dim, `scratch/infra-smooth-dim/`). Mathlib only.

## Main results

Let `K` be a field and `f : X ⟶ Spec K`.

* `ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension`: if `f` is smooth of
  relative dimension `n` and `x` is a closed point, then `dim 𝒪_{X,x} = n` and `𝔪_x` is spanned by
  `n` elements.
* `ZInQ.Contrib.Dim.isRegularLocalRing_stalk_of_smooth`: if `f` is smooth, the local rings at closed
  points are regular.
* `ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension`: `dim_{κ(x)} 𝔪_x/𝔪_x² = n`
  at closed points.
* `ZInQ.Contrib.Dim.ringKrullDim_stalk_of_section`: the same two facts at a `K`-point.
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`: if `f` is smooth and `X`
  is irreducible, `dim X = dim 𝒪_{X,x} = edim 𝒪_{X,x}` for every closed point `x`.
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension`: if `f` is smooth of
  relative dimension `n` and `X` is nonempty, then `dim X = n`.
-/

namespace ZInQ.Contrib.Dim

open Ideal IsLocalRing CategoryTheory AlgebraicGeometry

/-- The algebraic theorem over a base ring that is a field (without a `Field` instance). -/
theorem ringKrullDim_and_spanFinrank_of_isField {R S : Type*} [CommRing R] [CommRing S]
    (hR : IsField R) (φ : R →+* S) (n : ℕ) (h : φ.IsStandardSmoothOfRelativeDimension n)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = n ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = n := by
  let _ := hR.toField
  let _ := φ.toAlgebra
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (h : @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ φ.toAlgebra).out
  rw [← hP]
  exact ringKrullDim_and_spanFinrank_localization P m

/-- Sections of `Spec K` over a nonempty open form a field. -/
theorem isField_sections_spec (K : Type*) [Field K] (U : (Spec (CommRingCat.of K)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of K))).Nonempty) :
    IsField Γ(Spec (CommRingCat.of K), U) := by
  have hUt : U = ⊤ := by
    obtain ⟨z, hz⟩ := hU
    refine eq_top_iff.mpr fun y _ => ?_
    have : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim y z]
  subst hUt
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

/-- **Local form.** If `f : X → Spec K` is standard smooth of relative dimension `n` on an affine
chart `V → U` containing a closed point `x`, then `dim 𝒪_{X,x} = n` and `𝔪_x` is spanned by `n`
elements (so `dim_{κ(x)} 𝔪_x/𝔪_x² = n`). -/
theorem ringKrullDim_stalk_of_chart {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K))
    {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom)
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  have hR := isField_sections_spec K U ⟨f.base x, e hxV⟩
  have hmax := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  obtain ⟨h1, h2⟩ := ringKrullDim_and_spanFinrank_of_isField hR _ n h
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let eq : Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _).toRingEquiv
  constructor
  · rw [← ringKrullDim_eq_of_ringEquiv eq, h1]
  · rw [← map_ringEquiv_maximalIdeal eq, Ideal.spanFinrank_map_eq_of_ringEquiv, h2]

/-- **Smooth of relative dimension `n` over a field.** At every closed point, the local ring has
Krull dimension `n` and embedding dimension `n` (it is a regular local ring of dimension `n`). -/
theorem ringKrullDim_stalk_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, -, V, hV, hxV, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ringKrullDim_stalk_of_chart f hV e n h x hxV hx

/-- **Smooth over a field.** At every closed point, the local ring is regular: its Krull dimension
equals its embedding dimension, and both equal the relative dimension of a standard smooth chart
around the point. -/
theorem exists_ringKrullDim_stalk_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ, ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, -, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  have := h'.out
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  exact ⟨P.dimension, ringKrullDim_stalk_of_chart f hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) x hxV hx⟩

/-- **Chart form.** Around every point of a smooth `K`-scheme there is an open set `V` and an
`n` such that every closed point of `V` has local ring of dimension and embedding dimension `n`. -/
theorem exists_nhds_ringKrullDim_stalk {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (n : ℕ), x ∈ V ∧ ∀ y ∈ V, IsClosed ({y} : Set X) →
      ringKrullDim (X.presheaf.stalk y) = n ∧
        (maximalIdeal (X.presheaf.stalk y)).spanFinrank = n := by
  obtain ⟨U, -, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  have := h'.out
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  exact ⟨V, P.dimension, hxV, fun y hy hyc => ringKrullDim_stalk_of_chart f hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) y hy hyc⟩

/-- On an irreducible smooth `K`-scheme all closed points have local rings of the same
dimension. -/
theorem ringKrullDim_stalk_eq_of_isClosed {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X]
    (z w : X) (hz : IsClosed ({z} : Set X)) (hw : IsClosed ({w} : Set X)) :
    ringKrullDim (X.presheaf.stalk z) = ringKrullDim (X.presheaf.stalk w) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨Vz, nz, hzV, hz'⟩ := exists_nhds_ringKrullDim_stalk f z
  obtain ⟨Vw, nw, hwV, hw'⟩ := exists_nhds_ringKrullDim_stalk f w
  have hne : ((Vz : Set X) ∩ Vw).Nonempty :=
    nonempty_preirreducible_inter Vz.2 Vw.2 ⟨z, hzV⟩ ⟨w, hwV⟩
  obtain ⟨u, ⟨huz, huw⟩, hu⟩ :=
    nonempty_inter_closedPoints hne (Vz.2.inter Vw.2).isLocallyClosed
  rw [(hz' z hzV hz).1, (hw' w hwV hw).1, ← (hz' u huz hu).1, (hw' u huw hu).1]

/-- **Dimension of an irreducible smooth `K`-scheme.** Its dimension equals the Krull dimension of
the local ring at any closed point, which equals the embedding dimension there. -/
theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk x) ∧
      ((maximalIdeal (X.presheaf.stalk x)).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨n, hn1, hn2⟩ := exists_ringKrullDim_stalk_of_smooth f x hx
  refine ⟨?_, by rw [hn1, hn2]⟩
  have hdim : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  rw [hdim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun y => ?_
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({y} : Set X))
      ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hyz : z ≤ y := specializes_iff_mem_closure.mpr hz
    calc (Order.coheight y : WithBot ℕ∞) ≤ Order.coheight z := by
          exact_mod_cast Order.coheight_anti hyz
      _ = ringKrullDim (X.presheaf.stalk z) := (ringKrullDim_stalk_eq_coheight z).symm
      _ = ringKrullDim (X.presheaf.stalk x) := ringKrullDim_stalk_eq_of_isClosed f z x hzc hx
      _ = ringKrullDim (X.presheaf.stalk x) := rfl
  · rw [ringKrullDim_stalk_eq_coheight]
    exact Order.coheight_le_krullDim x


/-! ### Corollaries: regularity, cotangent dimension, rational points, dimension of `X` -/

/-- **Smooth over a field ⇒ regular at closed points.** -/
theorem isRegularLocalRing_stalk_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨n, h1, h2⟩ := exists_ringKrullDim_stalk_of_smooth f x hx
  exact (isRegularLocalRing_iff _).mpr (by rw [h1, h2])

/-- **Cotangent space at a closed point.** If `X → Spec K` is smooth of relative dimension `n`
and `x` is a closed point, then `dim_{κ(x)} 𝔪_x/𝔪_x² = n`. -/
theorem finrank_cotangentSpace_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Module.finrank (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x)) =
      n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact (ringKrullDim_stalk_of_smoothOfRelativeDimension f n x hx).2

/-- The image of a `K`-point (a section of `X → Spec K`) is a closed point. -/
theorem isClosed_singleton_of_section {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (p : Spec (CommRingCat.of K)) : IsClosed ({s.base p} : Set X) := by
  have := isClosedImmersion_of_comp_eq_id (Y := Spec (CommRingCat.of K)) f s hs
  have hr : Set.range s.base = {s.base p} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      have : Subsingleton (PrimeSpectrum K) := inferInstance
      exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) a p)
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr]
  exact s.isClosedEmbedding.isClosed_range

/-- **Cotangent space at a rational point.** If `X → Spec K` is smooth of relative dimension `n`
and `s` is a `K`-point, then the local ring at `s` has dimension `n` and its cotangent space
`𝔪/𝔪²` has dimension `n` over the residue field. -/
theorem ringKrullDim_stalk_of_section {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (p : Spec (CommRingCat.of K)) :
    ringKrullDim (X.presheaf.stalk (s.base p)) = n ∧
      Module.finrank (ResidueField (X.presheaf.stalk (s.base p)))
        (CotangentSpace (X.presheaf.stalk (s.base p))) = n :=
  ⟨(ringKrullDim_stalk_of_smoothOfRelativeDimension f n _
      (isClosed_singleton_of_section f s hs p)).1,
    finrank_cotangentSpace_of_smoothOfRelativeDimension f n _
      (isClosed_singleton_of_section f s hs p)⟩


/-- **Dimension of a smooth `K`-scheme of relative dimension `n`.** If `X` is nonempty and
`X → Spec K` is smooth of relative dimension `n`, then `dim X = n`. (infra-smooth-dim assumed `X`
irreducible; nonempty suffices: every point specializes to a closed point, whose local ring has
dimension `n`.) -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] [Nonempty X] :
    topologicalKrullDim X = n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hdim : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  rw [hdim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun y => ?_
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({y} : Set X))
      ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hyz : z ≤ y := specializes_iff_mem_closure.mpr hz
    calc (Order.coheight y : WithBot ℕ∞) ≤ Order.coheight z := by
          exact_mod_cast Order.coheight_anti hyz
      _ = ringKrullDim (X.presheaf.stalk z) := (ringKrullDim_stalk_eq_coheight z).symm
      _ = n := (ringKrullDim_stalk_of_smoothOfRelativeDimension f n z hzc).1
  · obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X))
      Set.univ_nonempty isClosed_univ.isLocallyClosed
    rw [← (ringKrullDim_stalk_of_smoothOfRelativeDimension f n x hx).1,
      ringKrullDim_stalk_eq_coheight]
    exact Order.coheight_le_krullDim x

end ZInQ.Contrib.Dim
