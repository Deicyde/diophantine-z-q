import ShRG
import Top
import CA1

/-!
# sh-route, part C: the inertia field inside an algebraic closure

`K` of characteristic 0, `Ω` an algebraic closure, `w` a valuation ring of `Ω`. The inertia field
`inertiaField w` is the set of `x ∈ Ω` such that, for some finite Galois `M ∋ x`, every
`τ ∈ Aut(Ω/K)` acting trivially modulo `𝔪_w` on `w ∩ M` fixes `x` (the union of the inertia fields
of the finite Galois subextensions).
-/

open IsLocalRing Polynomial

set_option linter.style.haveILetI false

namespace ShRoute

section Omega

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- `τ` acts trivially modulo `𝔪_w` on `w ∩ M`. -/
def CondM (M : IntermediateField K Ω) (τ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ y ∈ M, y ∈ w → τ y - y ∈ w.nonunits

theorem CondM.mono {M M' : IntermediateField K Ω} (h : M ≤ M') {τ : Ω ≃ₐ[K] Ω}
    (hτ : CondM w M' τ) : CondM w M τ := fun y hy => hτ y (h hy)

/-- `x ∈ M` is fixed by every `τ` acting trivially modulo `𝔪_w` on `w ∩ M`. -/
def FixVia (M : IntermediateField K Ω) (x : Ω) : Prop :=
  x ∈ M ∧ ∀ τ : Ω ≃ₐ[K] Ω, CondM w M τ → τ x = x

theorem FixVia.mono {M M' : IntermediateField K Ω} (h : M ≤ M') {x : Ω} (hx : FixVia w M x) :
    FixVia w M' x := ⟨h hx.1, fun τ hτ => hx.2 τ (hτ.mono w h)⟩

/-- `M` is finite Galois over `K`. -/
def IsFG (M : IntermediateField K Ω) : Prop := FiniteDimensional K M ∧ IsGalois K M

/-- An inertia automorphism acts trivially modulo `𝔪_w` on all of `w`. -/
theorem condM_of_isInertia {σ : Ω ≃ₐ[K] Ω} (hσ : PkgI2.IsInertia w σ) (M : IntermediateField K Ω) :
    CondM w M σ := by
  intro y _ hy
  obtain ⟨h, hI⟩ := hσ
  have h1 : (⟨σ, h⟩ : w.decompositionSubgroup K) • residue w ⟨y, hy⟩ = residue w ⟨y, hy⟩ := by
    have := congrArg (fun f => f (residue w ⟨y, hy⟩)) (MonoidHom.mem_ker.mp hI)
    exact this
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  have h2 := (Ideal.Quotient.eq).mp h1
  rw [ValuationSubring.valuation_lt_one_iff] at h2
  rw [ValuationSubring.mem_nonunits_iff]
  exact h2

variable [CharZero K] [IsAlgClosure K Ω]

theorem isFG_of (s : IntermediateField K Ω) [FiniteDimensional K s] :
    ∃ M : IntermediateField K Ω, IsFG M ∧ s ≤ M := by
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  refine ⟨IntermediateField.normalClosure K s Ω, ⟨inferInstance, ?_⟩, IntermediateField.le_normalClosure s⟩
  haveI : Algebra.IsSeparable K (IntermediateField.normalClosure K s Ω) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨⟩

theorem exists_two {M₁ M₂ : IntermediateField K Ω} (h₁ : IsFG M₁) (h₂ : IsFG M₂) :
    ∃ M : IntermediateField K Ω, IsFG M ∧ M₁ ≤ M ∧ M₂ ≤ M := by
  haveI := h₁.1
  haveI := h₂.1
  obtain ⟨M, hM, hle⟩ := isFG_of (M₁ ⊔ M₂)
  exact ⟨M, hM, le_trans le_sup_left hle, le_trans le_sup_right hle⟩

/-- The inertia field of `w` (over `K`). -/
def inertiaField : IntermediateField K Ω where
  carrier := {x | ∃ M : IntermediateField K Ω, IsFG M ∧ FixVia w M x}
  mul_mem' := by
    rintro x y ⟨M₁, h₁, hx⟩ ⟨M₂, h₂, hy⟩
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    have hx := hx.mono w l₁
    have hy := hy.mono w l₂
    exact ⟨M, hM, M.mul_mem hx.1 hy.1, fun τ hτ => by rw [map_mul, hx.2 τ hτ, hy.2 τ hτ]⟩
  add_mem' := by
    rintro x y ⟨M₁, h₁, hx⟩ ⟨M₂, h₂, hy⟩
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    have hx := hx.mono w l₁
    have hy := hy.mono w l₂
    exact ⟨M, hM, M.add_mem hx.1 hy.1, fun τ hτ => by rw [map_add, hx.2 τ hτ, hy.2 τ hτ]⟩
  algebraMap_mem' c := by
    obtain ⟨M, hM, -⟩ := isFG_of (⊥ : IntermediateField K Ω)
    exact ⟨M, hM, M.algebraMap_mem c, fun τ _ => τ.commutes c⟩
  inv_mem' := by
    rintro x ⟨M, hM, hx⟩
    exact ⟨M, hM, M.inv_mem hx.1, fun τ hτ => by rw [map_inv₀, hx.2 τ hτ]⟩

theorem mem_inertiaField {x : Ω} :
    x ∈ inertiaField (K := K) w ↔ ∃ M : IntermediateField K Ω, IsFG M ∧ FixVia w M x := Iff.rfl

/-- **The inertia group fixes the inertia field.** -/
theorem inertia_fixes {σ : Ω ≃ₐ[K] Ω} (hσ : PkgI2.IsInertia w σ) {x : Ω}
    (hx : x ∈ inertiaField (K := K) w) : σ x = x := by
  obtain ⟨M, -, hM⟩ := hx
  exact hM.2 σ (condM_of_isInertia w hσ M)

/-- Finitely many elements of the inertia field are fixed via one finite Galois `M`. -/
theorem exists_common (s : Finset Ω) (hs : ∀ x ∈ s, x ∈ inertiaField (K := K) w) :
    ∃ M : IntermediateField K Ω, IsFG M ∧ ∀ x ∈ s, FixVia w M x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨M, hM, -⟩ := isFG_of (⊥ : IntermediateField K Ω)
    exact ⟨M, hM, by simp⟩
  | insert a s _ ih =>
    obtain ⟨M₁, h₁, hM₁⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨M₂, h₂, hM₂⟩ := hs a (Finset.mem_insert_self a s)
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    refine ⟨M, hM, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hM₂.mono w l₂
    · exact (hM₁ x hx).mono w l₁

end Omega

section Ring

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

theorem mem_max_iff (b : w) : b ∈ maximalIdeal w ↔ (b : Ω) ∈ w.nonunits := by
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]

theorem mem_max_comap_iff {E : Type} [Field E] (f : E →+* Ω) (a : w.comap f) :
    a ∈ maximalIdeal (w.comap f) ↔ f (a : E) ∈ w.nonunits := by
  rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff,
    nonunits_comap]

/-- **Roots near a point.** A monic `q ∈ w[X]` with `q(c) ∈ 𝔪_w` has a root `α ∈ w` with
`α ≡ c mod 𝔪_w` (`Ω` algebraically closed, `w` integrally closed). -/
theorem exists_root_near [IsAlgClosed Ω] (q : w[X]) (hq : q.Monic) (c : w)
    (hc : q.eval c ∈ maximalIdeal w) : ∃ α : w, q.IsRoot α ∧ α - c ∈ maximalIdeal w := by
  induction h : q.natDegree generalizing q with
  | zero =>
    exfalso
    rw [hq.natDegree_eq_zero] at h
    rw [h, eval_one] at hc
    exact (maximalIdeal.isMaximal w).ne_top ((Ideal.eq_top_iff_one _).mpr hc)
  | succ n ih =>
    have hdeg : (q.map (algebraMap w Ω)).degree ≠ 0 := by
      rw [hq.degree_map, degree_eq_natDegree hq.ne_zero, h]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (q.map (algebraMap w Ω)) hdeg
    have hβw : β ∈ w := mem_of_isIntegral w (A := w) (fun a => a.2)
      ⟨q, hq, by rwa [IsRoot, Polynomial.eval_map] at hβ⟩
    let β' : w := ⟨β, hβw⟩
    have hr : q.IsRoot β' := by
      apply Subtype.ext
      rw [IsRoot, Polynomial.eval_map] at hβ
      have : algebraMap w Ω (q.eval β') = q.eval₂ (algebraMap w Ω) β := by
        rw [← eval₂_at_apply]; rfl
      exact this.trans hβ
    have hfac := (mul_divByMonic_eq_iff_isRoot).mpr hr
    have hq2 : (q /ₘ (X - C β')).Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C β') (by rw [hfac]; exact hq)
    have hdeg2 : (q /ₘ (X - C β')).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C β'), h, natDegree_X_sub_C]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at hc
    rcases (maximalIdeal.isMaximal w).isPrime.mem_or_mem hc with h1 | h1
    · exact ⟨β', hr, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨α, hα, hαc⟩ := ih (q /ₘ (X - C β')) hq2 h1 hdeg2
      refine ⟨α, ?_, hαc⟩
      rw [IsRoot, ← hfac, eval_mul, hα.eq_zero, mul_zero]

/-- **Two distinct roots with the same residue give a double root modulo `𝔪_w`.** -/
theorem derivative_eval_eq_zero_of_two_roots (q : w[X]) {α β : w} (hα : q.IsRoot α)
    (hβ : q.IsRoot β) (hne : α ≠ β) (hres : residue w α = residue w β) :
    ((q.map (residue w)).derivative).eval (residue w α) = 0 := by
  have hfac := (mul_divByMonic_eq_iff_isRoot).mpr hα
  set q1 := q /ₘ (X - C α)
  have hβ1 : q1.IsRoot β := by
    have := hβ
    rw [IsRoot, ← hfac, eval_mul, eval_sub, eval_X, eval_C] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hfac1 := (mul_divByMonic_eq_iff_isRoot).mpr hβ1
  rw [← hfac, ← hfac1]
  simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, derivative_mul,
    derivative_sub, derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    hres, sub_self, zero_mul, mul_zero, add_zero]

variable [CharZero K] [IsAlgClosure K Ω]

/-- The valuation ring of the inertia field. -/
abbrev wE : ValuationSubring (inertiaField (K := K) w) :=
  w.comap (algebraMap (inertiaField (K := K) w) Ω)

/-- `wE → Ω`. -/
def ιΩ : wE (K := K) w →+* Ω :=
  (algebraMap (inertiaField (K := K) w) Ω).comp (wE (K := K) w).subtype

/-- `wE → w`. -/
def ιw : wE (K := K) w →+* w :=
  (ιΩ (K := K) w).codRestrict w.toSubring (fun a => a.2)

theorem ιw_coe (a : wE (K := K) w) : ((ιw w a : w) : Ω) = ιΩ w a := rfl

/-- **Core lemma.** A root `α` of a monic `g` over the valuation ring of the inertia field whose
residue is a simple root of `g mod 𝔪_w` lies in the inertia field. -/
theorem mem_inertiaField_of_simple_root (g : (wE (K := K) w)[X]) (α : Ω)
    (hα : (g.map (ιΩ w)).eval α = 0) (hαw : α ∈ w)
    (hs : ((g.map ((residue w).comp (ιw w))).derivative).eval (residue w ⟨α, hαw⟩) ≠ 0) :
    α ∈ inertiaField (K := K) w := by
  classical
  -- the coefficients are fixed via one `M₀`
  obtain ⟨M₀, h₀, hM₀⟩ := exists_common w (g.support.image fun i => ιΩ w (g.coeff i))
    (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (g.coeff i : inertiaField (K := K) w).2)
  haveI := h₀.1
  have hαint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hαint
  obtain ⟨M, hM, hle⟩ := isFG_of (M₀ ⊔ IntermediateField.adjoin K {α})
  have hαM : α ∈ M := hle (le_sup_right (a := M₀) (IntermediateField.mem_adjoin_simple_self K α))
  refine ⟨M, hM, hαM, fun τ hτ => ?_⟩
  have hτ₀ : CondM w M₀ τ := hτ.mono w (le_trans le_sup_left hle)
  -- `τ α` is a root of `g`
  have hcoef : (g.map (ιΩ w)).map (τ : Ω →+* Ω) = g.map (ιΩ w) := by
    ext i
    rw [coeff_map, coeff_map]
    by_cases hi : i ∈ g.support
    · exact (hM₀ _ (Finset.mem_image_of_mem _ hi)).2 τ hτ₀
    · rw [notMem_support_iff.mp hi, map_zero, map_zero]
  have hτα : (g.map (ιΩ w)).eval (τ α) = 0 := by
    rw [← hcoef, Polynomial.eval_map]
    change eval₂ (τ : Ω →+* Ω) ((τ : Ω →+* Ω) α) _ = 0
    rw [eval₂_at_apply, hα, map_zero]
  have hτw : τ α - α ∈ w.nonunits := hτ α hαM hαw
  by_contra hne
  have hταw : τ α ∈ w := by
    have : τ α = α + (τ α - α) := by ring
    rw [this]
    exact add_mem hαw (ValuationSubring.nonunits_le hτw)
  let gw := g.map (ιw w)
  have root_of : ∀ (x : Ω) (hx : x ∈ w), (g.map (ιΩ w)).eval x = 0 → gw.IsRoot ⟨x, hx⟩ := by
    intro x hx h
    apply Subtype.ext
    have e : g.map (ιΩ w) = gw.map (algebraMap w Ω) := by
      rw [Polynomial.map_map]; rfl
    rw [e, Polynomial.eval_map] at h
    change algebraMap w Ω (gw.eval ⟨x, hx⟩) = algebraMap w Ω 0
    rw [← eval₂_at_apply, map_zero]
    exact h
  have h2 := derivative_eval_eq_zero_of_two_roots w gw (root_of α hαw hα)
    (root_of (τ α) hταw hτα) (fun h => hne (congrArg Subtype.val h).symm)
    (by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_max_iff]
      exact hτw)
  apply hs
  rw [← h2, Polynomial.map_map]


theorem map_ιΩ_eq (g : (wE (K := K) w)[X]) : g.map (ιΩ w) = (g.map (ιw w)).map (algebraMap w Ω) := by
  rw [Polynomial.map_map]; rfl

instance isLocalHom_ιw : IsLocalHom (ιw (K := K) w) := by
  constructor
  intro a ha
  by_contra h
  have h1 : a ∈ maximalIdeal (wE (K := K) w) := h
  rw [mem_max_comap_iff] at h1
  have h2 : ιw w a ∈ maximalIdeal w := by rw [mem_max_iff]; exact h1
  exact h2 ha

/-- **The valuation ring of the inertia field is henselian.** -/
theorem henselian_wE : HenselianLocalRing (wE (K := K) w) where
  is_henselian f hf a₀ h₁ h₂ := by
    let q := f.map (ιw w)
    have hq : q.Monic := hf.map _
    have hc : q.eval (ιw w a₀) ∈ maximalIdeal w := by
      rw [Polynomial.eval_map, eval₂_at_apply, mem_max_iff, ιw_coe]
      exact (mem_max_comap_iff w _ _).mp h₁
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
    obtain ⟨α, hα, hαc⟩ := exists_root_near w q hq _ hc
    have hroot : (f.map (ιΩ w)).eval (α : Ω) = 0 := by
      rw [map_ιΩ_eq, Polynomial.eval_map]
      change eval₂ (algebraMap w Ω) (algebraMap w Ω α) q = 0
      rw [eval₂_at_apply, hα.eq_zero, map_zero]
    have hres : residue w α = residue w (ιw w a₀) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hαc
    have hsimple : ((f.map ((residue w).comp (ιw w))).derivative).eval
        (residue w ⟨(α : Ω), α.2⟩) ≠ 0 := by
      have e : (⟨(α : Ω), α.2⟩ : w) = α := rfl
      rw [e, hres, derivative_map, Polynomial.eval_map]
      change eval₂ ((residue w).comp (ιw w)) (((residue w).comp (ιw w)) a₀) _ ≠ 0
      rw [eval₂_at_apply, RingHom.comp_apply, residue_ne_zero_iff_isUnit]
      exact h₂.map _
    have hαE := mem_inertiaField_of_simple_root w f (α : Ω) hroot α.2 hsimple
    let a : wE (K := K) w := ⟨⟨α, hαE⟩, by exact α.2⟩
    refine ⟨a, ?_, ?_⟩
    · have h0 : ιΩ w (f.eval a) = 0 := by
        rw [← eval₂_at_apply, ← Polynomial.eval_map]; exact hroot
      apply Subtype.ext
      apply (algebraMap (inertiaField (K := K) w) Ω).injective
      change ιΩ w _ = algebraMap _ Ω 0
      rw [map_zero]
      exact h0
    · rw [mem_max_comap_iff]
      have := (mem_max_iff w _).mp hαc
      exact this

/-- **The residue field of the inertia field is separably closed.** -/
theorem isSepClosed_wE : IsSepClosed (ResidueField (wE (K := K) w)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  apply IsSepClosed.of_exists_root
  intro p hpm hpirr hpsep
  obtain ⟨g, hgp, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (residue _) residue_surjective p) hpm
  have hdeg : (g.map (ιΩ w)).degree ≠ 0 := by
    rw [hgm.degree_map, degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast (Irreducible.natDegree_pos hpirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (g.map (ιΩ w)) hdeg
  have hαw : α ∈ w := by
    letI : Algebra (wE (K := K) w) Ω := (ιΩ w).toAlgebra
    exact mem_of_isIntegral w (A := wE (K := K) w) (fun a => a.2)
      ⟨g, hgm, by rwa [IsRoot, Polynomial.eval_map] at hα⟩
  -- the residue polynomial
  let κm := ResidueField.map (ιw (K := K) w)
  have hgw : g.map ((residue w).comp (ιw w)) = p.map κm := by
    rw [← hgp, Polynomial.map_map, ResidueField.map_comp_residue]
  have hgw0 : (g.map (ιw w)).eval ⟨α, hαw⟩ = 0 := by
    apply Subtype.ext
    change algebraMap w Ω _ = algebraMap w Ω 0
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← map_ιΩ_eq]
    exact hα
  have hroot' : (p.map κm).eval (residue w ⟨α, hαw⟩) = 0 := by
    rw [← hgw, ← Polynomial.map_map, Polynomial.eval_map, eval₂_at_apply, hgw0, map_zero]
  have hsimple : ((g.map ((residue w).comp (ιw w))).derivative).eval
      (residue w ⟨α, hαw⟩) ≠ 0 := by
    rw [hgw]
    have := (hpsep.map (f := κm)).eval₂_derivative_ne_zero (RingHom.id _) (x := residue w ⟨α, hαw⟩)
      (by rw [← Polynomial.eval]; exact hroot')
    exact this
  have hαE := mem_inertiaField_of_simple_root w g α hα hαw hsimple
  let a : wE (K := K) w := ⟨⟨α, hαE⟩, by exact hαw⟩
  refine ⟨residue _ a, ?_⟩
  have h0 : ιΩ w (g.eval a) = 0 := by
    rw [← eval₂_at_apply, ← Polynomial.eval_map]; exact hα
  have h1 : g.eval a = 0 := by
    apply Subtype.ext
    apply (algebraMap (inertiaField (K := K) w) Ω).injective
    change ιΩ w _ = algebraMap _ Ω 0
    rw [map_zero]
    exact h0
  rw [← hgp, Polynomial.eval_map, eval₂_at_apply, h1, map_zero]

end Ring

section DVR

open ReductSplit ReductGlue

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
  [CharZero K] [IsAlgClosure K Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [PerfectField (ResidueField O)]

theorem mem_w_of_mem (hw : w.comap (algebraMap K Ω) = O) (a : O) : algebraMap K Ω a ∈ w := by
  have : (a : K) ∈ w.comap (algebraMap K Ω) := hw ▸ a.2
  exact this

theorem nonunits_iff_of (hw : w.comap (algebraMap K Ω) = O) (a : O) :
    algebraMap K Ω a ∈ w.nonunits ↔ a ∈ maximalIdeal O := by
  rw [← nonunits_comap (algebraMap K Ω) w (a : K), hw, ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.valuation_lt_one_iff]

/-- **Elements of the inertia field are uniformizer powers times units** (from `key_finite`). -/
theorem unit_pow (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ) (x : Ω)
    (hxE : x ∈ inertiaField (K := K) w) (hxw : x ∈ w) (hx0 : x ≠ 0) :
    ∃ n : ℕ, x / algebraMap K Ω ϖ ^ n ∈ w ∧ (x / algebraMap K Ω ϖ ^ n)⁻¹ ∈ w := by
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hxE
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := w.comap (algebraMap M Ω)
  have hAW : ∀ a : O, algebraMap O M a ∈ W := fun a => mem_w_of_mem w hw a
  have hctr : ∀ a : O, algebraMap O M a ∈ W.nonunits ↔ a ∈ maximalIdeal O := by
    intro a
    rw [nonunits_comap]
    exact nonunits_iff_of w hw a
  have hfix' : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
    intro σ hσ
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hcond : CondM w M τ := by
      intro y hyM hyw
      have h1 := hσ ⟨y, hyM⟩ hyw
      rw [nonunits_comap, map_sub, ← hτ] at h1
      exact h1
    have := hfix τ hcond
    apply (algebraMap M Ω).injective
    rw [← hτ]
    exact this
  have hx0' : (⟨x, hxM⟩ : M) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨n, h1, h2⟩ := key_finite (K := K) O W hAW hctr ϖ hϖ ⟨x, hxM⟩ hfix' hxw hx0'
  have e : ((algebraMap O M ϖ : M) : Ω) = algebraMap K Ω ϖ := rfl
  refine ⟨n, ?_, ?_⟩
  · have := h1; simpa [W, ValuationSubring.mem_comap, e] using this
  · have := h2; simpa [W, ValuationSubring.mem_comap, e] using this

theorem hE_eq (hw : w.comap (algebraMap K Ω) = O) :
    (wE (K := K) w).comap (algebraMap K (inertiaField (K := K) w)) = O := by
  rw [ValuationSubring.comap_comap]
  exact hw

theorem ιΩ_injective : Function.Injective (ιΩ (K := K) w) := fun a b h =>
  Subtype.ext (Subtype.ext h)

theorem ιΩ_comapHom (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) :
    ιΩ w (comapHom (hE_eq w hw) ϖ) = algebraMap K Ω ϖ := rfl

theorem assoc_pow (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ)
    {a : wE (K := K) w} (ha : a ≠ 0) : ∃ n : ℕ, Associated (comapHom (hE_eq w hw) ϖ ^ n) a := by
  have hx0 : ιΩ w a ≠ 0 := fun h => ha (ιΩ_injective w (by rw [h, map_zero]))
  obtain ⟨n, h1, h2⟩ := unit_pow w hw ϖ hϖ (ιΩ w a) a.1.2 a.2 hx0
  have hϖ0 : algebraMap K Ω ϖ ≠ 0 := by
    rw [_root_.map_ne_zero]; exact fun h => hϖ.ne_zero (Subtype.ext h)
  have hyE : ιΩ w a / algebraMap K Ω ϖ ^ n ∈ inertiaField (K := K) w :=
    (inertiaField w).div_mem a.1.2 (pow_mem ((inertiaField w).algebraMap_mem _) n)
  have hyE' : (ιΩ w a / algebraMap K Ω ϖ ^ n)⁻¹ ∈ inertiaField (K := K) w :=
    (inertiaField w).inv_mem hyE
  let u : wE (K := K) w := ⟨⟨_, hyE⟩, by exact h1⟩
  let v : wE (K := K) w := ⟨⟨_, hyE'⟩, by exact h2⟩
  have hy0 : ιΩ w a / algebraMap K Ω ϖ ^ n ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hϖ0)
  have huv : u * v = 1 := ιΩ_injective w (by
    rw [map_mul, map_one]; exact mul_inv_cancel₀ hy0)
  refine ⟨n, Units.mk u v huv (by rw [mul_comm]; exact huv), ιΩ_injective w ?_⟩
  rw [map_mul, map_pow, ιΩ_comapHom w hw]
  change algebraMap K Ω ϖ ^ n * (ιΩ w a / algebraMap K Ω ϖ ^ n) = ιΩ w a
  field_simp

theorem irreducible_comapHom (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ) :
    Irreducible (comapHom (hE_eq w hw) ϖ) := by
  set π := comapHom (hE_eq w hw) ϖ
  have hπ0 : π ≠ 0 := fun h => by
    have := congrArg (ιΩ w) h
    rw [ιΩ_comapHom w hw, map_zero, map_eq_zero] at this
    exact hϖ.ne_zero (Subtype.ext this)
  have hπnu : ¬ IsUnit π := by
    intro h
    have h1 : π ∉ maximalIdeal (wE (K := K) w) := fun hm => hm h
    apply h1
    rw [mem_max_comap_iff]
    exact (nonunits_iff_of w hw ϖ).mpr ((mem_maximalIdeal _).mpr hϖ.not_isUnit)
  refine ⟨hπnu, fun a b hab => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hau, hbu⟩ := hcon
  have ha0 : a ≠ 0 := fun h => hπ0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hπ0 (by rw [hab, h, mul_zero])
  obtain ⟨n, u, hu⟩ := assoc_pow w hw ϖ hϖ ha0
  obtain ⟨m, u', hu'⟩ := assoc_pow w hw ϖ hϖ hb0
  rcases n with _ | n
  · exact hau (by rw [← hu, pow_zero, _root_.one_mul]; exact u.isUnit)
  rcases m with _ | m
  · exact hbu (by rw [← hu', pow_zero, _root_.one_mul]; exact u'.isUnit)
  have key : π * 1 = π * (π * (π ^ (n + m) * ((u : wE (K := K) w) * u'))) := by
    rw [_root_.mul_one]
    conv_lhs => rw [hab, ← hu, ← hu']
    ring
  have := mul_left_cancel₀ hπ0 key
  exact hπnu (isUnit_iff_exists_inv.mpr ⟨_, this.symm⟩)

theorem isDVR_wE (hw : w.comap (algebraMap K Ω) = O) :
    IsDiscreteValuationRing (wE (K := K) w) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_comapHom w hw ϖ hϖ, fun hx => assoc_pow w hw ϖ hϖ hx⟩

end DVR

section ResAlg

open ReductSplit ReductGlue

/-- **The residue extension of an algebraic extension of valued fields is algebraic.** -/
theorem res_isAlgebraic {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
    {O : ValuationSubring K} {A : ValuationSubring E} (hA : A.comap (algebraMap K E) = O) :
    letI := (resMap hA).toAlgebra
    Algebra.IsAlgebraic (ResidueField O) (ResidueField A) := by
  letI := (resMap hA).toAlgebra
  constructor
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  set p := minpoly K (a : E)
  have hp0 : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  obtain ⟨i0, hi0, hmax⟩ := p.support.exists_max_image (fun i => O.valuation (p.coeff i))
    (nonempty_support_iff.mpr hp0)
  set c := p.coeff i0
  have hc0 : c ≠ 0 := mem_support_iff.mp hi0
  have hvc0 : O.valuation c ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  let q := C c⁻¹ * p
  have hq : ∀ i, q.coeff i ∈ Set.range (algebraMap O K) := by
    intro i
    rw [coeff_C_mul]
    by_cases hi : i ∈ p.support
    · refine ⟨⟨_, O.mem_of_valuation_le_one _ ?_⟩, rfl⟩
      show O.valuation (c⁻¹ * p.coeff i) ≤ 1
      rw [map_mul, map_inv₀]
      rw [inv_mul_le_iff₀ (zero_lt_iff.mpr hvc0), _root_.mul_one]
      exact hmax i hi
    · rw [notMem_support_iff.mp hi, mul_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨qO, hqO⟩ := (mem_lifts q).mp ((lifts_iff_coeff_lifts q).mpr hq)
  have hqO1 : qO.coeff i0 = 1 := by
    apply IsFractionRing.injective O K
    rw [← coeff_map, hqO, map_one, coeff_C_mul, inv_mul_cancel₀ hc0]
  refine ⟨qO.map (residue O), ?_, ?_⟩
  · intro h
    have := congrArg (fun r => r.coeff i0) h
    simp only [coeff_map, hqO1, map_one, coeff_zero] at this
    exact one_ne_zero this
  · rw [aeval_def, eval₂_map]
    have e1 : (algebraMap (ResidueField O) (ResidueField A)).comp (residue O) =
        (residue A).comp (comapHom hA) := by
      ext b; exact resMap_residue hA b
    rw [e1, ← hom_eval₂]
    have h0 : qO.eval₂ (comapHom hA) a = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero]
      change A.subtype (qO.eval₂ (comapHom hA) a) = 0
      rw [hom_eval₂]
      have e2 : A.subtype.comp (comapHom hA) = (algebraMap K E).comp (algebraMap O K) := rfl
      rw [e2, ← eval₂_map, hqO]
      change aeval (a : E) q = 0
      rw [map_mul, aeval_C, minpoly.aeval, mul_zero]
    rw [h0, map_zero]

end ResAlg

section Assemble

open ReductSplit ReductGlue

/-- **Extension of a valuation ring to an extension field** (Chevalley; via Mathlib's
`IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_comap_eq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (O : ValuationSubring K) :
    ∃ w : ValuationSubring Ω, w.comap (algebraMap K Ω) = O := by
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K Ω).comp O.subtype)
  refine ⟨B, le_antisymm ?_ (fun x hx => hB ⟨x, hx⟩)⟩
  intro x hx
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  have hunit : IsUnit (((algebraMap K Ω).comp O.subtype).codRestrict B.toSubring hB ⟨x⁻¹, hinv⟩) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K Ω x, hx⟩, Subtype.ext ?_⟩
    change algebraMap K Ω x⁻¹ * algebraMap K Ω x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
  apply hxO
  have h1 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 :=
    congrArg (fun z : O => (z : K)) (Units.mul_inv u)
  rw [hu] at h1
  change x⁻¹ * _ = 1 at h1
  have : (((u⁻¹ : Oˣ) : O) : K) = x := by
    rw [← inv_inv x]; exact (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact (u⁻¹ : Oˣ).1.2

/-- **`SHInside0` is a theorem.** -/
theorem shInside0 : SHInside0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw
  haveI : Algebra.IsAlgebraic K (inertiaField (K := K) w) := inferInstance
  refine ⟨inertiaField (K := K) w, hE_eq w hw,
    ⟨⟨isDVR_wE w hw, henselian_wE w, isSepClosed_wE w⟩, inferInstance,
      fun ϖ hϖ => irreducible_comapHom w hw ϖ hϖ, ?_⟩,
    fun σ hσ x hx => inertia_fixes w hσ hx⟩
  letI := (resMap (hE_eq w hw)).toAlgebra
  haveI := res_isAlgebraic (hE_eq w hw)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **`SHExists0` is a theorem.** -/
theorem shExists0 : SHExists0 := by
  intro K _ _ O _ _
  obtain ⟨w, hw⟩ := exists_comap_eq (Ω := AlgebraicClosure K) O
  obtain ⟨E, hE, h, -⟩ := shInside0 K O (AlgebraicClosure K) w hw
  exact ⟨E, inferInstance, inferInstance, _, hE, h⟩

end Assemble

end ShRoute
