import ZInQKernel.HDecomp.LeafPush2.T

/-! # conj-pieces §A: `ArtinTorsionSurj` (N1-surj) from the leaf `MulIsogeny`

Check with `lake env lean scratch/conj-pieces/Artin.lean` (after
`lake build ZInQKernel.HDecomp.LeafPush2.T`).

* `G0FibreSimple.MulIsogeny` is copied verbatim from `scratch/g0-assemble/parts/40_fibresimple.lean`
  (it is field 1, `mulIsogeny`, of g0-assemble's `GluePieces2`, status LEAF).
* `embHom`, `toC`, `ArtinTorsionSurj` are copied verbatim from `scratch/conj-twist/ConjTwist.lean`.
* `artinTorsionSurj_of_mulIsogeny : MulIsogeny → ArtinTorsionSurj` is proved.

Proof. Let `Q : Spec ℂ → A` (over `K` via `σ = ι ∘ alg`) with `Qⁿ = 1`, and `x` its image point.
`Q ≫ [n] = Qⁿ = 1`, so `[n](x) = e₀`, the image of the unit section. `{e₀}` is closed (a section of
`A → Spec K` is a closed immersion), `[n]` is finite (`MulIsogeny`), so `[n]⁻¹{e₀}` is closed and
discrete, hence `x` is a closed point. A closed point of a scheme of finite type over `K` has
residue field finite over `K` (Mathlib's `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`).
`Q` is `Spec(φ)` for `φ : κ(x) → ℂ` over `σ`; every `φ(a)` is integral over `σ(K) ⊆ ι(K̄)`, and
`ι(K̄)` is algebraically closed, so `φ = ι ∘ ψ` with `ψ : κ(x) → K̄`; `P = Spec(ψ) ≫ (κ(x) → A)`
is the required `K̄`-point. -/

noncomputable section

namespace G0FibreSimple

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end G0FibreSimple

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

open ZInQ.LeafPush2 (CPts cptObj IsUniformization)

/-- `Spec(ι) : Spec ℂ → Spec K̄` over `K`. -/
def embHom {K : Type} [Field K] (emb : AlgebraicClosure K →+* ℂ) :
    cptObj (emb.comp (algebraMap K (AlgebraicClosure K))) ⟶
      PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom emb)) (by
    simp only [cptObj, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- **Comparison of points through `ι` (proved to be a homomorphism):** `A(K̄) → A(ℂ)_{ι∘alg}`,
`P ↦ P ∘ Spec(ι)`. -/
def toC {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) :
    A.Pt (AlgebraicClosure K) →* CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) where
  toFun P := embHom emb ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- **N1-surj. Torsion comparison, surjectivity (GLUE, unproved; STANDARD).** Every `n`-torsion
point of `A(ℂ)_{ι∘alg}` (`n ≥ 1`) comes from `A(K̄)`. (`toC` is injective, `toC_injective`; both
`A(K̄)[n]` and `A(ℂ)[n]` have `n^{2g}` elements, by T5 over `K̄` and over `ℂ`; equivalently `A[n]`
is finite étale in characteristic `0`. Mumford §4, §6, UNVERIFIED numbers.) -/
def ArtinTorsionSurj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
      ∃ P, toC A emb P = Q

/-! ## Proof -/

/-- `[n]` as a morphism: `((n : ℤ) : End A).hom = (𝟙 A)ⁿ` (proved). -/
theorem intCast_end_hom {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℕ) :
    ((n : ℤ) : PkgI3.AbVar.End A).hom = (𝟙 A.X) ^ n := by
  rw [Int.cast_natCast, ← nsmul_one]
  change (Additive.toMul (n • (1 : PkgI3.AbVar.End A))).1 = _
  rw [toMul_nsmul, SubmonoidClass.coe_pow]
  rfl

/-- `Q ≫ [n] = Qⁿ` (proved). -/
theorem comp_mulN {K : Type} [Field K] (A : PkgI3.AbVar K) {Y : Over (Spec (CommRingCat.of K))}
    (Q : Y ⟶ A.X) (n : ℕ) : Q ≫ ((n : ℤ) : PkgI3.AbVar.End A).hom = Q ^ n := by
  rw [intCast_end_hom, MonObj.comp_pow, Category.comp_id]

/-- The image of the unit section is a closed point (proved): for every `K`-scheme `Y` and
`y ∈ Y`, `{(1 : Y ⟶ A)(y)}` is closed. -/
theorem isClosed_one_apply {K : Type} [Field K] (A : PkgI3.AbVar K)
    {Y : Over (Spec (CommRingCat.of K))} (y : Y.left) :
    IsClosed ({(1 : Y ⟶ A.X).left y} : Set A.X.left) := by
  have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of K)))).left := by
    change Subsingleton (Spec (CommRingCat.of K)); infer_instance
  have hη : IsClosedImmersion (η[A.X]).left :=
    isClosedImmersion_of_comp_eq_id A.X.hom _ (by simp)
  have hcl := (η[A.X]).left.isClosedEmbedding.isClosed_range
  convert hcl using 1
  ext z
  constructor
  · rintro rfl
    exact ⟨(toUnit Y).left y, by rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]⟩
  · rintro ⟨a, rfl⟩
    rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)

/-- A point of a scheme lying in a closed, discrete subset is closed (proved). -/
theorem isClosed_singleton_of_mem {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (hd : IsDiscrete S) {x : X} (hx : x ∈ S) : IsClosed ({x} : Set X) := by
  have := hd.to_subtype
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyS : y ∈ S := closure_minimal (by simpa using hx) hS hy
  have h1 : (⟨y, hyS⟩ : S) ∈ closure ({⟨x, hx⟩} : Set S) := by
    rw [closure_subtype]
    simp [hy]
  rw [(isClosed_discrete _).closure_eq] at h1
  simpa using congrArg Subtype.val h1

/-- A complex number integral over `σ(K)`, `σ = ι ∘ alg`, lies in `ι(K̄)` (proved). -/
theorem mem_range_emb {K : Type} [Field K] (emb : AlgebraicClosure K →+* ℂ) {R : Type} [CommRing R]
    (φ0 : K →+* R) (hint : φ0.IsIntegral) (φ : R →+* ℂ)
    (hσ : φ.comp φ0 = emb.comp (algebraMap K (AlgebraicClosure K))) (a : R) :
    ∃ b, emb b = φ a := by
  obtain ⟨p, hpm, hpa⟩ := hint a
  let F := emb.fieldRange
  have : IsAlgClosed F := IsAlgClosed.of_ringEquiv _ _ emb.rangeRestrictFieldEquiv
  let σF : K →+* F := emb.rangeRestrictField.comp (algebraMap K _)
  have hcomp : (algebraMap F ℂ).comp σF = φ.comp φ0 := by
    rw [hσ]; ext k; rfl
  have hint' : IsIntegral F (φ a) := ⟨p.map σF, hpm.map _, by
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hpa, map_zero]⟩
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint')
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one F _ h1
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.mp c.2
  exact ⟨b, by rw [hb]; exact hc⟩

/-- **`ArtinTorsionSurj` from the leaf `MulIsogeny` (proved).** -/
theorem artinTorsionSurj_of_mulIsogeny (hM : G0FibreSimple.MulIsogeny) : ArtinTorsionSurj := by
  intro K _ A emb n hn Q hQ
  have : CharZero K := (emb.comp (algebraMap K (AlgebraicClosure K))).charZero
  set N := ((n : ℤ) : PkgI3.AbVar.End A).hom with hNdef
  have hfin : IsFinite N.left := (hM K A n (by exact_mod_cast hn.ne')).1
  have hQN : Q ≫ N = 1 := by rw [hNdef, comp_mulN, hQ]
  set pr := Scheme.SpecToEquivOfField ℂ A.X.left Q.left with hpr
  have hQ' : Q.left = Spec.map pr.2 ≫ A.X.left.fromSpecResidueField pr.1 :=
    ((Scheme.SpecToEquivOfField ℂ A.X.left).left_inv Q.left).symm
  -- the image point is closed
  have hx : IsClosed ({pr.1} : Set A.X.left) := by
    have hpt : pr.1 = Q.left (IsLocalRing.closedPoint ℂ) := rfl
    have hS := (isClosed_one_apply A (Y := cptObj (emb.comp (algebraMap K (AlgebraicClosure K))))
      (IsLocalRing.closedPoint ℂ)).preimage
      N.left.continuous
    refine isClosed_singleton_of_mem hS
      (N.left.isDiscrete_preimage_singleton _) ?_
    rw [hpt, Set.mem_preimage, Set.mem_singleton_iff,
      show N.left (Q.left (IsLocalRing.closedPoint ℂ)) = (Q.left ≫ N.left) (IsLocalRing.closedPoint ℂ)
        from (Scheme.Hom.comp_apply _ _ _).symm, ← Over.comp_left, hQN]
  -- its residue field is finite over `K`
  have hci : IsClosedImmersion (A.X.left.fromSpecResidueField pr.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hF : IsFinite (A.X.left.fromSpecResidueField pr.1 ≫ A.X.hom) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ0, hφ0⟩ := Spec.map_surjective (A.X.left.fromSpecResidueField pr.1 ≫ A.X.hom)
  have hint : φ0.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ0]; infer_instance
  have hσ : φ0 ≫ pr.2 = CommRingCat.ofHom (emb.comp (algebraMap K (AlgebraicClosure K))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ0, ← Category.assoc, ← hQ']
    exact Over.w Q
  have hσ' : pr.2.hom.comp φ0.hom = emb.comp (algebraMap K (AlgebraicClosure K)) := congrArg CommRingCat.Hom.hom hσ
  -- the lift `ψ : κ(x) → K̄`
  have hrange : ∀ a, pr.2.hom a ∈ emb.fieldRange := fun a =>
    RingHom.mem_fieldRange.mpr (mem_range_emb emb φ0.hom hint pr.2.hom hσ' a)
  let ψ : A.X.left.residueField pr.1 →+* AlgebraicClosure K :=
    (emb.rangeRestrictFieldEquiv.symm : emb.fieldRange →+* AlgebraicClosure K).comp
      (pr.2.hom.codRestrict emb.fieldRange hrange)
  have hψ : ∀ a, emb (ψ a) = pr.2.hom a := fun a => by
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.X.left.fromSpecResidueField pr.1) ?_, ?_⟩
  · simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Category.assoc]
    rw [← hφ0, ← Spec.map_comp]
    congr 1
    ext k
    apply emb.injective
    change emb (ψ (φ0.hom k)) = emb (algebraMap K _ k)
    rw [hψ]
    exact congrArg (fun f : K →+* ℂ => f k) hσ'
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom emb) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
      A.X.left.fromSpecResidueField pr.1 = Q.left
    rw [hQ', ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact hψ a

#print axioms artinTorsionSurj_of_mulIsogeny

end G0Galois
