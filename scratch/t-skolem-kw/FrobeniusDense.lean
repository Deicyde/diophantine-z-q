import Mathlib

/-!
# t-skolem-kw: leaf T18 (Frobenius density) reduced to its finite form

`HSyn.FrobeniusDense` (verbatim below as `HS.FrobeniusDense`, over `HSyn`'s `Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, also verbatim) is proved from `PkgI6.ChebotarevExists`
(= `GlueC10.ChebotarevExists`, verbatim).  So T18 rests on the finite (existence) form of
Chebotarev's theorem alone.

Part C10 is copied verbatim from `scratch/h-decomposition/Leaves.lean`, section `GlueC10Sec`
(lines 11328-11333, 11375-11630, 11747-11750 at base 01267822): the lift of a finite-level
Frobenius to `G_ℚ` at a prime of `\bar ℤ`.  New here (`HS` section): the localization of `\bar ℤ`
at a prime `𝔓` is a valuation subring of `\bar ℚ` (`zbarLoc`, via the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}` of
each finite layer), an arithmetic Frobenius at `𝔓` is an `IsArithFrob` at this place, and the
Krull-topology step.
-/

open NumberField

namespace TSkolemKW.C10

/-- **Leaf I6.4 (Chebotarev, existence form)** — verbatim from pkg-I6. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q


/-! ## Part B. The absolute Galois group `G_ℚ` -/

/-- `\bar ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(\bar ℚ/ℚ)` with the Krull topology.  Definitionally Mathlib's
`GQ` (which is a non-reducible `def` of the same type). -/
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar

example : GQ = Field.absoluteGaloisGroup ℚ := rfl

/-- `\bar ℤ`, the integral closure of `ℤ` in `\bar ℚ`. -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `g ∈ G_ℚ` is an arithmetic Frobenius at the rational prime `p`: there is a prime `𝔓` of
`\bar ℤ` over `p` with `g x ≡ x^p (mod 𝔓)` for every `x ∈ \bar ℤ`. -/
def IsFrobAt (g : GQ) (p : ℕ) : Prop :=
  ∃ P : Ideal Zbar, P.IsPrime ∧ P.under ℤ = Ideal.span {(p : ℤ)} ∧
    ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- **Frobenius density (GLUE).** For every finite subextension `E/ℚ` of `\bar ℚ` and every
`g ∈ G_ℚ` there is a Frobenius `h` at a prime `p ∉ S` with `h = g` on `E`.  By
`krullTopology_mem_nhds_one_iff` this says that Frobenius elements at primes outside `S` are
dense in `G_ℚ`. -/
def FrobDense (S : Finset ℕ) : Prop :=
  ∀ (E : IntermediateField ℚ Qbar), FiniteDimensional ℚ E → ∀ g : GQ,
    ∃ h : GQ, ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ IsFrobAt h p ∧
      ∀ x ∈ E, h x = g x

/-- **The lift of a finite-level Frobenius to `G_ℚ` (GLUE, proved below: `frobLift`).**  For a finite
Galois `E ⊂ \bar ℚ` and `τ ∈ Gal(E/ℚ)` that is the Frobenius at a prime `Q` of `𝓞_E` over `p`
unramified in `E`, some `h ∈ G_ℚ` restricting to `τ` is a Frobenius at `p` in `G_ℚ`.
Proof sketch: choose `𝔓 | Q` in `\bar ℤ`; an arithmetic Frobenius `h ∈ D_𝔓` exists by
compactness of `G_ℚ` and `exists_isArithFrobAt` in every finite Galois layer; `h|_E` is a
Frobenius at `Q`, and Frobenius at an unramified prime is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`). -/
def FrobLift : Prop :=
  ∀ (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (τ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime], p.Prime →
    Q.under ℤ = Ideal.span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ Q → IsArithFrobAt ℤ τ Q →
      ∃ h : GQ, IsFrobAt h p ∧ AlgEquiv.restrictNormal h E = τ

/-! ### Proof of `FrobLift` (merged from `Lift.lean`) -/

/-- `𝓞_E → \bar ℤ`. -/
noncomputable def toZbar (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  RingHom.codRestrict ((algebraMap E Qbar).comp (algebraMap (𝓞 E) E)) (integralClosure ℤ Qbar)
    (fun x => (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Qbar))

@[simp] lemma toZbar_coe (E : IntermediateField ℚ Qbar) (x : 𝓞 E) :
    ((toZbar E x : Zbar) : Qbar) = ((x : E) : Qbar) := rfl

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- **Step (c) of `FrobLift` (GLUE, proved).** -/
theorem restrictNormal_eq_of_frob (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (τ : E ≃ₐ[ℚ] E) (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) [Algebra.IsUnramifiedAt ℤ Q]
    (hτ : IsArithFrobAt ℤ τ Q) (h : GQ) (P : Ideal Zbar) (hPQ : P.comap (toZbar E) = Q)
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    AlgEquiv.restrictNormal h E = τ := by
  have : NumberField E := ⟨⟩
  set σ := AlgEquiv.restrictNormal h E
  have hσ : IsArithFrobAt ℤ σ Q := by
    intro x
    rw [hQp, card_quot, ← hPQ, Ideal.mem_comap]
    apply hh (toZbar E x)
    rw [map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
      toZbar_coe]
    congr 1
    exact AlgEquiv.restrictNormal_commutes h E (x : E)
  have hQ : Q.primeCompl ≤ nonZeroDivisors (𝓞 E) := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hx Q.zero_mem
  have heq := hσ.eq_of_isUnramifiedAt hτ hQ
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := congrArg (fun f => ((f a : 𝓞 E) : E)) heq
  have hb := congrArg (fun f => ((f b : 𝓞 E) : E)) heq
  simp only [MulSemiringAction.toAlgHom_apply] at ha hb
  have key : ∀ (g : E ≃ₐ[ℚ] E) (c : 𝓞 E), g (algebraMap (𝓞 E) E c) = ((g • c : 𝓞 E) : E) :=
    fun g c => rfl
  have e1 := (key σ a).trans (ha.trans (key τ a).symm)
  have e2 := (key σ b).trans (hb.trans (key τ b).symm)
  rw [map_div₀, map_div₀, e1, e2]

/-- **Step (b) of `FrobLift` (GLUE).** Every prime `𝔓` of `\bar ℤ` over a rational prime
`p` has an arithmetic Frobenius in `G_ℚ`.  (Compactness of `G_ℚ` and Mathlib's
`exists_isArithFrobAt` in each finite Galois layer.) -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P


lemma toZbar_injective (E : IntermediateField ℚ Qbar) : Function.Injective (toZbar E) := by
  intro x y hxy
  have := congrArg (fun z : Zbar => (z : Qbar)) hxy
  simp only [toZbar_coe] at this
  exact RingOfIntegers.ext (Subtype.ext this)

/-- **`FrobLift` from step (b) (GLUE, proved): lying-over plus step (c).** -/
theorem frobLift_of_frobExistsAt (hb : FrobExistsAt) : FrobLift := by
  intro E _ _ τ p Q _ hp hQp hQu hτ
  have : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (𝓞 E) Zbar := (toZbar E).toAlgebra
  have : Algebra.IsIntegral (𝓞 E) Zbar := Algebra.IsIntegral.tower_top ℤ
  obtain ⟨P, -, hP, hPQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal Zbar)
    (by
      intro x hx
      have : toZbar E x = 0 := hx
      rw [toZbar_injective E (this.trans (map_zero _).symm)]
      exact Q.zero_mem)
  have hPQ' : P.comap (toZbar E) = Q := hPQ
  have hPp : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hQp, Ideal.under, Ideal.under, ← hPQ', Ideal.comap_comap]
    congr 1
  obtain ⟨h, hh⟩ := hb p P hPp
  exact ⟨h, ⟨P, hP, hPp, hh⟩, restrictNormal_eq_of_frob E τ p Q hQp hτ h P hPQ' hh⟩

/-- The Frobenius condition at `𝔓` on the elements of `\bar ℤ` lying in `F`. -/
def FrobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar) : Set GQ :=
  {h | ∀ x y : Zbar, (x : Qbar) ∈ F → (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P}

/-- **Step (b), finite layer (GLUE, proved: `frobExistsFinite`; a consequence of Mathlib's
`IsArithFrobAt.exists_of_isInvariant` for `Gal(F/ℚ)` acting on `𝓞_F`, and the surjectivity
`G_ℚ → Gal(F/ℚ)`).** -/
def FrobExistsFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F],
      (FrobOn p P F).Nonempty

lemma frobOn_anti {p : ℕ} {P : Ideal Zbar} {F F' : IntermediateField ℚ Qbar} (hF : F ≤ F') :
    FrobOn p P F' ⊆ FrobOn p P F :=
  fun _ hh x y hx hy => hh x y (hF hx) hy

lemma isClosed_frobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ F] : IsClosed (FrobOn p P F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  simp only [FrobOn, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hh
  obtain ⟨x, y, hx, hy, hyP⟩ := hh
  refine ⟨(fun k => h⁻¹ * k) ⁻¹' (F.fixingSubgroup : Set GQ), ?_, ?_, ?_⟩
  · intro k hk hk'
    have hfix := (IntermediateField.mem_fixingSubgroup_iff F _).mp hk (x : Qbar) hx
    change h⁻¹ (k (x : Qbar)) = (x : Qbar) at hfix
    have hkx : k (x : Qbar) = h (x : Qbar) := by
      have e := congrArg h hfix
      rwa [show h (h⁻¹ (k (x : Qbar))) = k (x : Qbar) from AlgEquiv.apply_symm_apply h _] at e
    exact hyP (hk' x y hx (by rw [hy, hkx]))
  · exact (IntermediateField.fixingSubgroup_isOpen F).preimage (continuous_const.mul continuous_id)
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact one_mem _

instance : IsGalois ℚ Qbar := ⟨⟩

/-- **Step (b) from its finite layer (GLUE, proved): compactness of `G_ℚ`.** -/
theorem frobExistsAt_of_finite (hf : FrobExistsFinite) : FrobExistsAt := by
  intro p _ P _ hP
  let ι := {F : IntermediateField ℚ Qbar // FiniteDimensional ℚ F}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  let t : ι → Set GQ := fun F => FrobOn p P F.1
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨F₁, h₁⟩ ⟨F₂, h₂⟩
    refine ⟨⟨F₁ ⊔ F₂, inferInstance⟩, frobOn_anti le_sup_left, frobOn_anti le_sup_right⟩
  have htn : ∀ F, (t F).Nonempty := by
    rintro ⟨F, hF⟩
    let N := IntermediateField.normalClosure ℚ F Qbar
    have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ F Qbar
    have : Normal ℚ N := normalClosure.normal ℚ F Qbar
    have : IsGalois ℚ N := ⟨⟩
    exact (hf p P hP N).mono (frobOn_anti F.le_normalClosure)
  have htcl : ∀ F, IsClosed (t F) := fun F => by
    have := F.2
    exact isClosed_frobOn p P F.1
  obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun F => (htcl F).isCompact) htcl
  refine ⟨h, fun x y hy => ?_⟩
  have hxi : IsIntegral ℚ (x : Qbar) := Algebra.IsIntegral.isIntegral _
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(x : Qbar)}) :=
    IntermediateField.adjoin.finiteDimensional hxi
  exact Set.mem_iInter.mp hh ⟨IntermediateField.adjoin ℚ {(x : Qbar)}, this⟩ x y
    (IntermediateField.mem_adjoin_simple_self ℚ _) hy

/-- **Step (b), finite layer (GLUE, proved from Mathlib).** -/
theorem frobExistsFinite : FrobExistsFinite := by
  intro p _ P _ hP F _ _
  have : NumberField F := ⟨⟩
  set QF := P.comap (toZbar F) with hQF
  have hQFp : QF.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hP, Ideal.under, Ideal.under, hQF, Ideal.comap_comap]
    congr 1
  have hQFprime : QF.IsPrime := Ideal.comap_isPrime _ _
  have hQFne : QF ≠ ⊥ := by
    intro h0
    have hp : ((p : ℤ) : 𝓞 F) ∈ QF := by
      change algebraMap ℤ (𝓞 F) (p : ℤ) ∈ QF
      rw [← Ideal.mem_comap]
      change (p : ℤ) ∈ QF.under ℤ
      rw [hQFp]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.mem_bot] at hp
    have : ((p : ℤ) : 𝓞 F) ≠ 0 := by
      have := (Fact.out : p.Prime).ne_zero
      exact_mod_cast this
    exact this hp
  have : QF.IsMaximal := hQFprime.isMaximal hQFne
  let _ := IsIntegralClosure.MulSemiringAction ℤ ℚ F (𝓞 F)
  have := Algebra.isInvariant_of_isGalois ℤ ℚ F (𝓞 F)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (F ≃ₐ[ℚ] F) QF
  obtain ⟨h, hres⟩ : ∃ h : GQ, AlgEquiv.restrictNormal h F = σ :=
    ⟨σ.liftNormal Qbar, σ.restrict_liftNormal Qbar⟩
  subst hres
  refine ⟨h, fun x y hx hy => ?_⟩
  have hxi : IsIntegral ℤ (⟨(x : Qbar), hx⟩ : F) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F Qbar) (algebraMap F Qbar).injective]
    exact x.2
  let x' : 𝓞 F := ⟨⟨(x : Qbar), hx⟩, hxi⟩
  have hmem := hσ x'
  rw [hQFp, card_quot, hQF, Ideal.mem_comap] at hmem
  convert hmem using 1
  apply Subtype.ext
  rw [hy, map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
    toZbar_coe]
  congr 1
  change h (x : Qbar) = ((algebraMap (𝓞 F) F (galRestrict ℤ ℚ F (𝓞 F) _ x')) : Qbar)
  rw [algebraMap_galRestrict_apply]
  exact (AlgEquiv.restrictNormal_commutes h F (algebraMap (𝓞 F) F x')).symm

/-- **`FrobLift` holds (GLUE, proved from Mathlib).** -/
theorem frobLift : FrobLift :=
  frobLift_of_frobExistsAt (frobExistsAt_of_finite frobExistsFinite)


/-- **Frobenius density from Chebotarev (GLUE, proved from I6.4 and `FrobLift`).** -/
theorem frobDense_of_chebotarev (hC : ChebotarevExists) (hL : FrobLift) (S : Finset ℕ) :
    FrobDense S := by
  intro E hE g
  set N := IntermediateField.normalClosure ℚ E Qbar
  have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ E Qbar
  have : Normal ℚ N := normalClosure.normal ℚ E Qbar
  have : IsGalois ℚ N := ⟨⟩
  have : NumberField N := ⟨⟩
  obtain ⟨p, hp, hpS, Q, hQ, hQp, hQu, hQf⟩ := hC N S (AlgEquiv.restrictNormal g N)
  obtain ⟨h, hh, hres⟩ := hL N _ p Q hp hQp hQu hQf
  refine ⟨h, p, hp, hpS, hh, fun x hx => ?_⟩
  have hxN : x ∈ N := E.le_normalClosure hx
  have e1 := AlgEquiv.restrictNormal_commutes h N ⟨x, hxN⟩
  have e2 := AlgEquiv.restrictNormal_commutes g N ⟨x, hxN⟩
  rw [hres] at e1
  simpa using e1.symm.trans e2


/-- Frobenius elements at primes outside `S` are dense in `G_ℚ` (from Chebotarev alone). -/
theorem frobDense (hC : ChebotarevExists) (S : Finset ℕ) : FrobDense S :=
  frobDense_of_chebotarev hC frobLift S


end TSkolemKW.C10

/-! ## `HSyn.FrobeniusDense` from the finite form -/

namespace TSkolemKW.HS

open scoped Pointwise
open TSkolemKW.C10 (ChebotarevExists FrobDense IsFrobAt Zbar toZbar toZbar_coe frobDense)

/-! ### Definitions (verbatim from `HSyn` §0-§1 of `scratch/h-decomposition/Leaves.lean`) -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-! ### The localization of `\bar ℤ` at a prime is a valuation subring of `\bar ℚ` -/

variable (P : Ideal Zbar) [hP : P.IsPrime]

/-- Membership in `\bar ℤ_𝔓`. -/
def LocMem (x : Qbar) : Prop := ∃ a s : Zbar, s ∉ P ∧ x * (s : Qbar) = a

theorem one_notMem : (1 : Zbar) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top

omit hP in
theorem natCast_mem (p : ℕ) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) : (p : Zbar) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ Zbar (p : ℤ) ∈ P := h1
  simpa using h2

omit hP in
/-- In a number field `K`, for a nonzero prime `Q` of `𝓞_K`, every `x ∈ K` or its inverse is a
fraction `r / s` with `s ∉ Q` (the localization `(𝓞_K)_Q` is a DVR, hence a valuation ring). -/
theorem exists_frac_or_inv (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hQ0 : Q ≠ ⊥) (x : K) (hx0 : x ≠ 0) :
    ∃ r s : 𝓞 K, s ∉ Q ∧ (x * (s : K) = r ∨ x⁻¹ * (s : K) = r) := by
  let Aₘ := Localization.AtPrime Q
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hQ0 Aₘ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : (b : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply hx0
    rw [← hab]
    change (a : K) / (b : K) = 0
    rw [h, zero_div]
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap (𝓞 K) Aₘ a) (algebraMap (𝓞 K) Aₘ b)
  obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
  have hinj := IsLocalization.injective Aₘ Q.primeCompl_le_nonZeroDivisors
  refine ⟨r, s, hs, ?_⟩
  rcases hc with hc | hc
  · right
    have e : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (a : K) * (r : K) = (b : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change ((a : K) / (b : K))⁻¹ * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm
  · left
    have e : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (b : K) * (r : K) = (a : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change (a : K) / (b : K) * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm

/-- Every `x ∈ \bar ℚ` or its inverse lies in `\bar ℤ_𝔓`: pass to the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}`
for `E = ℚ(x)`. -/
theorem locMem_or_inv (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (x : Qbar) : LocMem P x ∨ LocMem P x⁻¹ := by
  by_cases hx0 : x = 0
  · left
    exact ⟨0, 1, one_notMem P, by simp [hx0]⟩
  have hxi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  let E := IntermediateField.adjoin ℚ ({x} : Set Qbar)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxi
  have : NumberField E := ⟨⟩
  let Q := P.comap (toZbar E)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hpQ : ((p : ℤ) : 𝓞 E) ∈ Q := by
    change toZbar E ((p : ℤ) : 𝓞 E) ∈ P
    simpa using natCast_mem P p hPp
  have hQ0 : Q ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpQ
    exact (by exact_mod_cast hp.ne_zero : ((p : ℤ) : 𝓞 E) ≠ 0) hpQ
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨r, s, hs, h | h⟩ := exists_frac_or_inv E Q hQ0 x' hx'0
  · left
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this
  · right
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this

/-- `\bar ℤ_𝔓` as a valuation subring of `\bar ℚ`. -/
def zbarLoc (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    ValuationSubring Qbar where
  carrier := {x | LocMem P x}
  mul_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (y * (t : Qbar)) * ha + (a : Qbar) * hb
  one_mem' := ⟨1, 1, one_notMem P, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * t + b * s, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (t : Qbar) * ha + (s : Qbar) * hb
  zero_mem' := ⟨0, 1, one_notMem P, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, ha⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast
    linear_combination -ha
  mem_or_inv_mem' := locMem_or_inv P p hp hPp

theorem mem_zbarLoc {p : ℕ} {hp : p.Prime} {hPp : P.under ℤ = Ideal.span {(p : ℤ)}} {x : Qbar} :
    x ∈ zbarLoc P p hp hPp ↔ LocMem P x := Iff.rfl

/-! ### An arithmetic Frobenius at `𝔓` is an `IsArithFrob` at `\bar ℤ_𝔓` -/

/-- `g ∈ G_ℚ` maps `\bar ℤ` to itself. -/
def gZ (g : GQ) (z : Zbar) : Zbar :=
  ⟨g z, (z.2 : IsIntegral ℤ (z : Qbar)).map ((g : Qbar →ₐ[ℚ] Qbar).restrictScalars ℤ)⟩

@[simp] theorem gZ_coe (g : GQ) (z : Zbar) : ((gZ g z : Zbar) : Qbar) = g z := rfl

theorem liesOver_and_isArithFrob (h : GQ) (p : ℕ) (hp : p.Prime)
    (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    LiesOver (zbarLoc P p hp hPp) p ∧ IsArithFrob h (zbarLoc P p hp hPp) p := by
  have hcong : ∀ z : Zbar, gZ h z - z ^ p ∈ P := fun z => hh z _ (by push_cast; rfl)
  have hmemP : ∀ z : Zbar, gZ h z ∈ P ↔ z ∈ P := by
    intro z
    constructor
    · intro hz
      have : z ^ p ∈ P := by
        have := P.sub_mem hz (hcong z)
        rwa [sub_sub_cancel] at this
      exact hP.mem_of_pow_mem p this
    · intro hz
      have := P.add_mem (hcong z) (P.pow_mem_of_mem hz p hp.pos)
      rwa [sub_add_cancel] at this
  have hpP := natCast_mem P p hPp
  refine ⟨?_, ?_, ?_⟩
  · -- `p` is a nonunit
    rw [LiesOver, ValuationSubring.mem_nonunits_iff_or]
    right
    rintro ⟨a, s, hs, ha⟩
    apply hs
    have : s = (p : Zbar) * a := by
      apply Subtype.ext
      push_cast
      rw [← ha, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero), one_mul]
    rw [this]
    exact P.mul_mem_right _ hpP
  · -- `h` stabilizes the place
    refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · rintro ⟨a, s, hs, ha⟩
      refine ⟨gZ h a, gZ h s, fun h' => hs ((hmemP s).1 h'), ?_⟩
      have := congrArg h ha
      rw [map_mul] at this
      simpa [AlgEquiv.aut_inv] using this
    · rintro ⟨a, s, hs, ha⟩
      have hts : gZ h (gZ h⁻¹ s) = s := by
        apply Subtype.ext
        simp [AlgEquiv.aut_inv]
      refine ⟨gZ h⁻¹ a, gZ h⁻¹ s, fun h' => hs (hts ▸ (hmemP _).2 h'), ?_⟩
      have := congrArg (fun y => (h⁻¹ : GQ) y) ha
      simp only [map_mul] at this
      simpa using this
  · -- the Frobenius congruence on the place
    rintro x ⟨a, s, hs, ha⟩
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases hd : h x - x ^ p = 0
    · exact Or.inl hd
    right
    rintro ⟨a', s', hs', hd'⟩
    let n : Zbar := gZ h a * s ^ p - a ^ p * gZ h s
    have hn : n ∈ P := by
      have : n = (gZ h a - a ^ p) * s ^ p - a ^ p * (gZ h s - s ^ p) := by ring
      rw [this]
      exact P.sub_mem (P.mul_mem_right _ (hcong a)) (P.mul_mem_left _ (hcong s))
    have e1 : h x * h (s : Qbar) = h (a : Qbar) := by rw [← map_mul, ha]
    have e2 : x ^ p * (s : Qbar) ^ p = (a : Qbar) ^ p := by rw [← mul_pow, ha]
    have e3 : (h x - x ^ p) * (h (s : Qbar) * (s : Qbar) ^ p) = (n : Qbar) := by
      simp only [n]
      push_cast
      simp only [gZ_coe]
      linear_combination ((s : Qbar) ^ p) * e1 - (h (s : Qbar)) * e2
    have e4 : (s' : Qbar) = (h x - x ^ p) * (a' : Qbar) := by
      rw [← hd', ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    have e5 : s' * (gZ h s * s ^ p) = a' * n := by
      apply Subtype.ext
      push_cast
      simp only [gZ_coe]
      rw [e4, ← e3]
      ring
    have hmem : s' * (gZ h s * s ^ p) ∈ P := e5 ▸ P.mul_mem_left _ hn
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hs' h1
    rcases hP.mem_or_mem h1 with h2 | h2
    · exact hs ((hmemP s).1 h2)
    · exact hs (hP.mem_of_pow_mem p h2)

/-! ### The reduction -/

/-- **T18 from its finite form, via `FrobDense` (GLUE, proved).** -/
theorem frobeniusDense_of_frobDense (hD : ∀ S, FrobDense S) : FrobeniusDense := by
  intro U hU σ S
  obtain ⟨E, hE, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ Qbar (U : Set GQ)).1 (hU.mem_nhds U.one_mem)
  obtain ⟨h, p, hp, hpS, ⟨P, hP, hPp, hh⟩, hhE⟩ := hD S E hE σ
  obtain ⟨hL, hF⟩ := liesOver_and_isArithFrob P h p hp hPp hh
  refine ⟨p, hp, hpS, zbarLoc P p hp hPp, h, hL, hF, hEU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← hhE x hx, AlgEquiv.symm_apply_apply]

/-- **T18 (`HSyn.FrobeniusDense`) from the finite form `PkgI6.ChebotarevExists` (GLUE,
proved).** -/
theorem frobeniusDense_of_chebotarev (hC : ChebotarevExists) : FrobeniusDense :=
  frobeniusDense_of_frobDense fun S => frobDense hC S

end TSkolemKW.HS

#print axioms TSkolemKW.HS.frobeniusDense_of_chebotarev
