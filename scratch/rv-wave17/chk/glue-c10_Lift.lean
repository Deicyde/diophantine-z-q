import Mathlib

/-! glue-c10: step (c) of `FrobLift` — the restriction of a Frobenius of `G_ℚ` to a finite Galois
layer `E` is the Frobenius at the unramified prime below. -/

open NumberField

namespace GlueC10

abbrev Qbar : Type := AlgebraicClosure ℚ
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar
abbrev Zbar : Type := integralClosure ℤ Qbar

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

/-- `g ∈ G_ℚ` is a Frobenius at `p` (as in `C10.lean`). -/
def IsFrobAt (g : GQ) (p : ℕ) : Prop :=
  ∃ P : Ideal Zbar, P.IsPrime ∧ P.under ℤ = Ideal.span {(p : ℤ)} ∧
    ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- **Step (b) of `FrobLift` (GLUE, proved: `frobExistsAt_of_finite`).** Every prime `𝔓` of `\bar ℤ` over a rational prime
`p` has an arithmetic Frobenius in `G_ℚ`.  (Compactness of `G_ℚ` and Mathlib's
`exists_isArithFrobAt` in each finite Galois layer.) -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- `FrobLift` of `C10.lean`. -/
def FrobLift : Prop :=
  ∀ (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (τ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime], p.Prime →
    Q.under ℤ = Ideal.span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ Q → IsArithFrobAt ℤ τ Q →
      ∃ h : GQ, IsFrobAt h p ∧ AlgEquiv.restrictNormal h E = τ

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

end GlueC10

#print axioms GlueC10.restrictNormal_eq_of_frob
#print axioms GlueC10.frobLift_of_frobExistsAt
#print axioms GlueC10.frobExistsAt_of_finite
#print axioms GlueC10.frobExistsFinite
#print axioms GlueC10.frobLift

open Lean Elab Command in
elab "#rvw17_check_axioms" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut cnt : Nat := 0
  for (n, _) in env.constants.map₂.toList do
    if n.isInternal then continue
    cnt := cnt + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.any (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]) then
      bad := bad.push n
      logInfo m!"BAD {n}: {axs}"
  logInfo m!"rvw17: {cnt} declarations checked, {bad.size} with nonstandard axioms"

#rvw17_check_axioms
