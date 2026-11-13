
/-! ## g0-x1belyi: `X1BelyiOnModel` from `BelyiX1` (transport along `ℚ(X) ≅ K_N`)

`X1BelyiOnModel` and `ffStructMap`/`ffAlgebra` are copied verbatim from
`scratch/g0-split/Split.lean` (lines 19495-19543 there; `X1BelyiOnModel` is in namespace
`HSyn.G0Split` there). Every other declaration it mentions (`PkgI3.AbVar`, `LeafModCurves.IsJ1`,
`IsX1Model`, `IsCurve`, `IsJacobian`, `IsBelyiFunction`, `BelyiX1`, `fieldX1`, `EjBar`, `Qj`, ...)
is imported from `ZInQKernel.HDecomp.Objects` / `ZInQKernel.HDecomp.ModCurves`, whose text is
identical to the Split.lean copies (checked by `scratch/g0-x1belyi/defdiff.py`). -/

namespace HSyn.G0Split

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

/-- `K(X)` as a `K`-algebra: `K = Γ(Spec K) → Γ(X) → K(X)` (copied from scratch/leaf-push2). -/
noncomputable def ffStructMap {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    [IsIntegral X.left] : K →+* X.left.functionField :=
  haveI : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop ≫
    X.left.germToFunctionField ⊤).hom

/-- (copied from scratch/leaf-push2) -/
@[instance_reducible] noncomputable def ffAlgebra {K : Type} [Field K]
    (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] : Algebra K X.left.functionField :=
  (ffStructMap X).toAlgebra

/-- **Missing piece 3 (glue E2, Belyi half: `LeafModCurves.BelyiX1` on the model of `IsJ1`).**
Every `J₁(N)` over `ℚ` (`IsJ1 N J`) is the Jacobian of a pointed curve `X` whose function field
carries a Belyi function `t` (`j/1728`) of degree `[ℚ(X) : ℚ(t)] ≤ N²`. From `BelyiX1` (a glue
target of leaf-modcurves: good reduction of `E_j` away from `j = 0, 1728, ∞`, and
`[K_N : ℚ(j)] ≤ N²`) by transport along `ℚ(X) ≅ K_N` (`IsX1Model`); the transport is not done
here. -/
def X1BelyiOnModel : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (_ : LeafModCurves.IsCurve X) (_ : IsIntegral X.left)
      (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X) (aj : X ⟶ J.X),
      LeafModCurves.IsJacobian X P₀ J aj ∧ ∃ t : X.left.functionField,
        (letI := ffAlgebra X; LeafModCurves.IsBelyiFunction ℚ X.left.functionField t) ∧
        ∃ d : ℕ,
          (letI := ffAlgebra X
           Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField = d) ∧
          0 < d ∧ d ≤ N ^ 2

end HSyn.G0Split

namespace G0X1Belyi

open LeafModCurves

/-! ### Transport lemmas (glue, proved) -/

/-- Membership in the nonunits of `w.comap e.symm`, for a ring isomorphism `e : F ≃+* L`. -/
theorem mem_nonunits_comap {F L : Type*} [Field F] [Field L] (e : F ≃+* L)
    (w : ValuationSubring F) (y : L) :
    y ∈ (w.comap (e.symm : L →+* F)).nonunits ↔ e.symm y ∈ w.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  simp only [RingEquiv.coe_toRingHom, map_inv₀, EmbeddingLike.map_eq_zero_iff]

/-- **Belyi functions transport along `k`-algebra isomorphisms.** -/
theorem isBelyiFunction_of_algEquiv {k F L : Type} [Field k] [Field F] [Field L] [Algebra k F]
    [Algebra k L] (e : F ≃ₐ[k] L) (t : F) (h : IsBelyiFunction k L (e t)) :
    IsBelyiFunction k F t := by
  refine ⟨fun ha => h.1 (ha.algHom e.toAlgHom), ?_⟩
  intro w hk ht q hm hirr hX hX1 hq x hx
  let w' : ValuationSubring L := w.comap (e.toRingEquiv.symm : L →+* F)
  have hk' : ∀ c : k, algebraMap k L c ∈ w' := fun c => by
    rw [ValuationSubring.mem_comap]
    simpa using hk c
  have ht' : e t ∈ w' := by
    rw [ValuationSubring.mem_comap]
    simpa using ht
  have hq' : Polynomial.aeval (e t) q ∈ w'.nonunits := by
    rw [mem_nonunits_comap e.toRingEquiv]
    simpa [Polynomial.aeval_algHom_apply] using hq
  have hx' : e x ∈ w'.nonunits := by
    rw [mem_nonunits_comap e.toRingEquiv]
    simpa using hx
  obtain ⟨y, hy, hxy⟩ := h.2 w' hk' ht' q hm hirr hX hX1 hq' (e x) hx'
  refine ⟨e.symm y, ?_, ?_⟩
  · rw [ValuationSubring.mem_comap] at hy
    simpa using hy
  · apply e.injective
    rw [hxy, map_mul, Polynomial.aeval_algHom_apply, AlgEquiv.apply_symm_apply]

/-- **`[F : k(t)]` transports along `k`-algebra isomorphisms.** -/
theorem finrank_adjoin_of_algEquiv {k F L : Type} [Field k] [Field F] [Field L] [Algebra k F]
    [Algebra k L] (e : F ≃ₐ[k] L) (t : F) :
    Module.finrank (IntermediateField.adjoin k {t}) F =
      Module.finrank (IntermediateField.adjoin k {e t}) L := by
  have hmap : (IntermediateField.adjoin k {t}).map e.toAlgHom = IntermediateField.adjoin k {e t} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
  refine Algebra.finrank_eq_of_equiv_equiv
    (((IntermediateField.adjoin k {t}).equivMap e.toAlgHom).trans
      (IntermediateField.equivOfEq hmap)).toRingEquiv e.toRingEquiv ?_
  ext x
  rfl

/-- Every element of `ℚ(j)` maps into `ℚ(t) ⊆ L`, `t` the image of `j/1728`. -/
theorem mem_adjoin_image (L : Type) [Field L] [Algebra Qj L] [Algebra ℚ L] (x : Qj) :
    algebraMap Qj L x ∈ IntermediateField.adjoin ℚ {algebraMap Qj L (RatFunc.X / 1728)} := by
  set S := IntermediateField.adjoin ℚ {algebraMap Qj L (RatFunc.X / 1728)}
  have h1728 : (1728 : L) ∈ S := by exact_mod_cast natCast_mem S 1728
  have hX : algebraMap Qj L RatFunc.X ∈ S := by
    have h : (RatFunc.X : Qj) = 1728 * (RatFunc.X / 1728) := by field_simp
    rw [h, map_mul, map_ofNat]
    exact mul_mem h1728 (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hpoly : ∀ p : Polynomial ℚ, algebraMap Qj L (algebraMap (Polynomial ℚ) Qj p) ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      have := eq_ratCast (((algebraMap Qj L).comp (algebraMap (Polynomial ℚ) Qj)).comp
        Polynomial.C) a
      simp only [RingHom.comp_apply] at this
      rw [this]
      exact SubfieldClass.ratCast_mem S a
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, RatFunc.algebraMap_X]
      exact mul_mem h hX
  rw [← RatFunc.num_div_denom x, map_div₀]
  exact div_mem (hpoly _) (hpoly _)

/-- **`[L : ℚ(t)] = [L : ℚ(j)]`** for a field `L` over `ℚ(j)` and `t` the image of `j/1728`. -/
theorem finrank_adjoin_image_X_div (L : Type) [Field L] [Algebra Qj L] [Algebra ℚ L] :
    Module.finrank (IntermediateField.adjoin ℚ {algebraMap Qj L (RatFunc.X / 1728)}) L =
      Module.finrank Qj L := by
  set S := IntermediateField.adjoin ℚ {algebraMap Qj L (RatFunc.X / 1728)}
  let g : Qj →ₐ[ℚ] L := (algebraMap Qj L).toRatAlgHom
  have hle : S ≤ g.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨_, rfl⟩
  let i0 : Qj →+* S := (algebraMap Qj L).codRestrict S (mem_adjoin_image L)
  let i : Qj ≃+* S := RingEquiv.ofBijective i0 ⟨i0.injective, fun y => by
    obtain ⟨x, hx⟩ := hle y.2
    exact ⟨x, Subtype.ext hx⟩⟩
  symm
  refine Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl L) ?_
  ext x
  rfl

/-- `K_N` is finite over `ℚ(j)` (`x(P)` lies in an algebraic closure of `ℚ(j)`). -/
theorem finrank_fieldX1_pos (P : EjBar.toAffine.Point) : 0 < Module.finrank Qj (fieldX1 P) := by
  have : FiniteDimensional Qj (fieldX1 P) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  exact Module.finrank_pos

/-! ### The piece -/

open HSyn.G0Split in
/-- **`X1BelyiOnModel` from `BelyiX1`** (glue, proved): transport of the Belyi function `j/1728`
and of the degree `[K_N : ℚ(j)]` along the ring isomorphism `ℚ(X) ≅ K_N` of `IsX1Model`. -/
theorem x1BelyiOnModel_of_belyiX1 (hB : BelyiX1) : X1BelyiOnModel := by
  intro N hN J hJ
  obtain ⟨X, P₀, aj, ⟨hC, hI, P, hP, ⟨e⟩⟩, hJac⟩ := hJ
  obtain ⟨hBel, hdeg⟩ := hB N P hN hP
  let _ := ffAlgebra X
  let e' : X.left.functionField ≃ₐ[ℚ] fieldX1 P := e.toRatAlgEquiv
  let t : X.left.functionField := e'.symm (algebraMap Qj (fieldX1 P) (RatFunc.X / 1728))
  have het : e' t = algebraMap Qj (fieldX1 P) (RatFunc.X / 1728) := e'.apply_symm_apply _
  have hfin : Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField =
      Module.finrank Qj (fieldX1 P) := by
    rw [finrank_adjoin_of_algEquiv e' t, het, finrank_adjoin_image_X_div]
  refine ⟨X, hC, hI, P₀, aj, hJac, t, ?_, _, rfl, ?_, ?_⟩
  · exact isBelyiFunction_of_algEquiv e' t (het ▸ hBel)
  · rw [hfin]; exact finrank_fieldX1_pos P
  · rw [hfin]; exact hdeg

end G0X1Belyi
