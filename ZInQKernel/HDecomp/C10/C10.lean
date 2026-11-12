import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-c10/C10.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-c10: C10 of h-trust (N5 L776-795), one compatible system at 3 and 5

Leaves copied verbatim from `scratch/pkg-I6/I6.lean` (`ChebotarevExists`, `BrauerNesbittChar0`).
-/

open NumberField

namespace GlueC10

/-! ## Leaves (copied from pkg-I6) -/

/-- **Leaf I6.4 (Chebotarev, existence form)** — verbatim from pkg-I6. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form)** — verbatim from pkg-I6. -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

/-! ## Part A. Finite level (the form recommended by glue-I6-rest)

A representation that factors through a finite Galois group `Gal(M/ℚ)`: traces that agree at
every unramified Frobenius outside `S` agree everywhere, hence the representations are
isomorphic. -/

/-- `σ ∈ Gal(M/ℚ)` is the Frobenius at some prime of `𝓞_M` over a rational prime `p ∉ S`
that is unramified in `M`. -/
def IsUnramFrob (M : Type) [Field M] [NumberField M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

/-- Chebotarev: every element of `Gal(M/ℚ)` is an unramified Frobenius outside `S`. -/
theorem isUnramFrob_all (hC : ChebotarevExists) (M : Type) [Field M] [NumberField M]
    [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : IsUnramFrob M S σ :=
  hC M S σ

/-- **C10 at finite level (GLUE, proved from I6.4 and I6.5).** Two semisimple
finite-dimensional representations of `Gal(M/ℚ)` over a field of characteristic `0` whose traces
agree at every unramified Frobenius outside a finite set `S` are isomorphic. -/
theorem iso_of_trace_eq_frob_finite (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ)
    (k V W : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k (M ≃ₐ[ℚ] M) V) (σ : Representation k (M ≃ₐ[ℚ] M) W)
    (hρ : IsSemisimpleModule (MonoidAlgebra k (M ≃ₐ[ℚ] M)) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k (M ≃ₐ[ℚ] M)) σ.asModule)
    (htr : ∀ g, IsUnramFrob M S g → LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (M ≃ₐ[ℚ] M)] σ.asModule) :=
  hBN k _ V W ρ σ hρ hσ fun g => htr g (isUnramFrob_all hC M S g)

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

/-- **The lift of a finite-level Frobenius to `G_ℚ` (GLUE, proved below: `frobLift`).**  For a
  finite
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

/-- **Passage from Frobenius classes to `G_ℚ` (GLUE, proved).**  Two continuous functions on
`G_ℚ` with values in a Hausdorff space that agree on the Frobenius elements at primes outside `S`
are equal, given `FrobDense S`. -/
theorem eq_of_eq_on_frob {X : Type*} [TopologicalSpace X] [T2Space X] (S : Finset ℕ)
    (hD : FrobDense S) (f₁ f₂ : GQ → X)
    (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → f₁ g = f₂ g) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  obtain ⟨h, p, hp, hpS, hh, hEq⟩ := hD E hE g
  have hfix : g⁻¹ * h ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change g⁻¹ (h x) = x
    rw [hEq x hx]
    exact AlgEquiv.symm_apply_apply g x
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
  exact this (hfr h p hp hpS hh)

/-- The trace of `ρ g` is the trace of its matrix in any basis. -/
lemma trace_eq_matrix {E V ι : Type*} [Field E] [AddCommGroup V] [Module E V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E V) (f : V →ₗ[E] V) :
    LinearMap.trace E V f = (LinearMap.toMatrix b b f).trace :=
  LinearMap.trace_eq_matrix_trace E b f

lemma continuous_trace {E V ι : Type*} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [AddCommGroup V] [Module E V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V)
    {G : Type*} [Monoid G] [TopologicalSpace G] (ρ : Representation E G V)
    (hρ : Continuous fun g => LinearMap.toMatrix b b (ρ g)) :
    Continuous fun g => LinearMap.trace E V (ρ g) := by
  simp_rw [trace_eq_matrix b]
  exact (continuous_finsetSum _ fun i _ => (continuous_apply_apply i i).comp hρ)

/-- **C10, the comparison in `G_ℚ` (GLUE, proved from I6.5 and `FrobDense`).**  Two continuous
semisimple finite-dimensional representations of `G_ℚ` over a Hausdorff topological field of
characteristic `0` (e.g. `ℚ_ℓ`, a finite extension, or `\bar ℚ_ℓ`) whose traces agree at the
Frobenius elements at all primes outside `S` are isomorphic.  Continuity is that of the matrix
coefficients in some basis. -/
theorem iso_of_trace_eq_on_frob (hBN : BrauerNesbittChar0) (S : Finset ℕ) (hD : FrobDense S)
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k (GQ) V)
    (σ : Representation k (GQ) W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k (GQ)) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k (GQ)) σ.asModule)
    (htr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (GQ)] σ.asModule) := by
  have heq := eq_of_eq_on_frob S hD _ _ (continuous_trace bV ρ hρc) (continuous_trace bW σ hσc)
    htr
  exact hBN k _ V W ρ σ hρ hσ fun g => congrFun heq g

/-! ## Part C. N5's transport from five to three -/

/-- **C10, the identification of `r₃` (GLUE, proved from I6.5 and `FrobDense`).**  N5 L776-795:
`C` is the coefficient field, `ι₃ : C → k₃`, `ι₅ : C → k₅` the chosen embeddings.  For a
Frobenius `g` at `p ∉ S`, the abelian-variety side gives one element `c p ∈ C` with
`tr r_ℓ(g) = ι_ℓ(c p)` for `ℓ = 3, 5` (Mumford §19 Thm 4, see `Trace.lean`), and the modular side
gives `a p ∈ C` with `tr ρ_ℓ(g) = ι_ℓ(a p)`.  If `r₅` and `ρ₅` have the same traces at
Frobenius (C9: `r₅ ≅ ρ_{f,ι₅}`), then `c p = a p` in `C`, so the traces of `r₃` and `ρ₃` agree at
every Frobenius outside `S`, and `r₃ ≅ ρ₃`. -/
theorem iso_three_of_five (hBN : BrauerNesbittChar0) (S : Finset ℕ) (hD : FrobDense S)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GQ V₅) (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) := by
  refine iso_of_trace_eq_on_frob hBN S hD k V W ι κ bV bW r₃ ρ₃ hrc hρc hr hρ ?_
  intro g p hp hpS hg
  have hca : c p = a p := ι₅.injective
    ((hr₅ g p hp hpS hg).symm.trans ((h₅ g p hp hpS hg).trans (hρ₅ g p hp hpS hg)))
  rw [hr₃ g p hp hpS hg, hρ₃ g p hp hpS hg, hca]

/-- **The semisimplification step.**  A subrepresentation (here: a `k[G]`-submodule) of a
semisimple representation is semisimple; so `r_ℓ ⊂ V_ℓ(A) ⊗ k` inherits semisimplicity from
Faltings' Satz 3 (pkg-I3 `FaltingsSemisimple`, after base change to `k`). -/
theorem semisimple_of_le {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hρ : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule)
    (N : Submodule (MonoidAlgebra k G) ρ.asModule) :
    IsSemisimpleModule (MonoidAlgebra k G) N := inferInstance

/-- **Step 3 of glue-assembly §2.2 (halving).**  If `ρ ≅ r ⊕ r` on traces, `tr ρ(g) = 2·tr r(g)`,
and `tr ρ(g) = ι(s)` for some `s ∈ C`, then `tr r(g) = ι(s/2)`: the element `c p = s/2 ∈ C` of
`iso_three_of_five`. -/
theorem trace_half {C k : Type} [Field C] [CharZero C] [Field k] [CharZero k] (ι : C →+* k)
    (tr tr' : k) (x : C) (h2 : tr = 2 * tr') (hs : tr = ι x) : tr' = ι (x / 2) := by
  rw [map_div₀, map_ofNat, ← hs, h2]
  field_simp


/-- Frobenius elements at primes outside `S` are dense in `G_ℚ` (from Chebotarev alone). -/
theorem frobDense (hC : ChebotarevExists) (S : Finset ℕ) : FrobDense S :=
  frobDense_of_chebotarev hC frobLift S

/-- **C10 (GLUE, proved from I6.4 Chebotarev and I6.5 Brauer–Nesbitt only).**  The statement of
`iso_three_of_five` with `FrobDense` discharged. -/
theorem c10 (hC : ChebotarevExists) (hBN : BrauerNesbittChar0) (S : Finset ℕ)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GQ V₅) (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  iso_three_of_five hBN S (frobDense hC S) C c a k₅ V₅ W₅ ι₅ r₅ ρ₅ h₅ hr₅ hρ₅ k V W ι κ ι₃ bV bW
    r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end GlueC10

