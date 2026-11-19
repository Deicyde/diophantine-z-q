import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual tame-inertia quotient of the Galois group of an algebraic extension

Let `Ω/K` be a Galois extension (for example an algebraic closure of a field of characteristic
zero) and `w` a valuation subring of `Ω`. Inside `Gal(Ω/K)` with its Krull topology:

* `inertiaGroup w`: automorphisms moving every element of `w` inside its residue class;
* `wildGroup w`: automorphisms with strict displacement `v(σ x - x) < v(x)` for every `x ≠ 0`;
* both are closed, `wildGroup w ≤ inertiaGroup w`, inertia preserves the valuation, and the wild
  group is normal in the inertia group;
* the tame quotient `TameQuotient w = inertiaGroup w ⧸ wildGroup w` (quotient topology of the
  Krull subspace topology) is a compact topological group whose open normal subgroups form a
  basis of neighbourhoods of `1` (`tame_hbasis`);
* every quotient of `TameQuotient w` by an open normal subgroup is cyclic as soon as the finite
  Galois layers have cyclic tame quotients (`tame_hcyc`). The finite layer is located by a
  compactness argument from the literal strict-displacement conditions on finitely many
  elements; no surjectivity of restriction on inertia or on wild inertia is used;
* a dense cyclic subgroup of `TameQuotient w` gives, on every finite Galois layer, agreement of
  any inertia element with a power of the generator times an actual wild element
  (`layer_agreement_of_dense`).
-/

noncomputable section
set_option autoImplicit false

namespace ActualTameInertia

open Topology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-! ### Finite orbits, the inertia subgroup and the wild subgroup -/

/-- Every element has a finite orbit under a `K`-automorphism of an algebraic extension. -/
theorem exists_pow_apply_eq [Algebra.IsAlgebraic K Ω] (σ : Ω ≃ₐ[K] Ω) (x : Ω) :
    ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hint : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hp : minpoly K x ≠ 0 := minpoly.ne_zero hint
  have hmem : ∀ k : ℕ, (σ ^ k) x ∈ (minpoly K x).rootSet Ω := by
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  have hfin : Finite ((minpoly K x).rootSet Ω) := (Polynomial.rootSet_finite _ _).to_subtype
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨(σ ^ k) x, hmem k⟩ : (minpoly K x).rootSet Ω))
  have heq' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨b - a, by omega, ?_⟩
    have e : (σ ^ b) x = (σ ^ a) ((σ ^ (b - a)) x) := by
      rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [e] at heq'
    exact ((σ ^ a).injective heq').symm
  · refine ⟨a - b, by omega, ?_⟩
    have e : (σ ^ a) x = (σ ^ b) ((σ ^ (a - b)) x) := by
      rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [e] at heq'
    exact (σ ^ b).injective heq'

theorem mem_of_residue {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (h : ∀ x ∈ w, w.valuation (σ x - x) < 1) {x : Ω} (hx : x ∈ w) : σ x ∈ w := by
  have h1 : σ x - x ∈ w := (w.valuation_le_one_iff _).1 (h x hx).le
  have h2 := w.add_mem _ _ h1 hx
  rwa [sub_add_cancel] at h2

theorem pow_mem_of_residue {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (h : ∀ x ∈ w, w.valuation (σ x - x) < 1) {x : Ω} (hx : x ∈ w) (n : ℕ) :
    (σ ^ n) x ∈ w := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply]
    exact mem_of_residue h ih

theorem inv_mem_of_residue [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (h : ∀ x ∈ w, w.valuation (σ x - x) < 1) {x : Ω} (hx : x ∈ w) : σ⁻¹ x ∈ w := by
  obtain ⟨N, hN, hfix⟩ := exists_pow_apply_eq σ x
  have hN1 : N - 1 + 1 = N := by omega
  have e : σ⁻¹ x = (σ ^ (N - 1)) x := by
    apply σ.injective
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, ← AlgEquiv.mul_apply,
      ← pow_succ', hN1, hfix]
  rw [e]
  exact pow_mem_of_residue h hx (N - 1)

/-- **The inertia subgroup** of `w`: automorphisms acting trivially on residues of `w`. -/
def inertiaGroup [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∀ x ∈ w, w.valuation (σ x - x) < 1}
  one_mem' := by
    intro x _
    simp
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx : τ x ∈ w := mem_of_residue hτ hx
    have e : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]
      ring
    rw [e]
    exact w.valuation.map_add_lt (hσ _ hτx) (hτ x hx)
  inv_mem' := by
    intro σ hσ x hx
    have hy : σ⁻¹ x ∈ w := inv_mem_of_residue hσ hx
    have hc : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have h1 := hσ _ hy
    rw [hc, Valuation.map_sub_swap] at h1
    exact h1

theorem mem_inertiaGroup_iff [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω}
    {σ : Ω ≃ₐ[K] Ω} : σ ∈ inertiaGroup w ↔ ∀ x ∈ w, w.valuation (σ x - x) < 1 :=
  Iff.rfl

/-- Strict displacement forces valuation preservation. -/
theorem val_apply_of_strict {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (h : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x) (x : Ω) :
    w.valuation (σ x) = w.valuation x := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  · calc w.valuation (σ x) = w.valuation ((σ x - x) + x) := by rw [sub_add_cancel]
      _ = w.valuation x := w.valuation.map_add_eq_of_lt_right (h x hx)

/-- **The wild subgroup** of `w`, defined by the literal strict displacement condition. -/
def wildGroup (w : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x}
  one_mem' := by
    intro x hx
    simpa using (w.valuation.pos_iff.mpr hx)
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
    have hsmall := hσ (τ x) hτx
    rw [val_apply_of_strict hτ x] at hsmall
    have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]
      ring
    rw [he]
    exact w.valuation.map_add_lt hsmall (hτ x hx)
  inv_mem' := by
    intro σ hσ x hx
    have hy : σ⁻¹ x ≠ 0 := (map_ne_zero σ⁻¹).mpr hx
    have hcancel : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have hval : w.valuation (σ⁻¹ x) = w.valuation x := by
      have h := val_apply_of_strict hσ (σ⁻¹ x)
      rw [hcancel] at h
      exact h.symm
    have h := hσ (σ⁻¹ x) hy
    rw [hcancel, hval, w.valuation.map_sub_swap] at h
    exact h

theorem mem_wildGroup_iff {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ wildGroup w ↔ ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x :=
  Iff.rfl

theorem wildGroup_le_inertiaGroup [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω) :
    wildGroup (K := K) w ≤ inertiaGroup w := by
  intro σ hσ
  rw [mem_inertiaGroup_iff]
  intro x hx
  by_cases h0 : x = 0
  · simp [h0]
  · exact lt_of_lt_of_le (mem_wildGroup_iff.1 hσ x h0) ((w.valuation_le_one_iff x).2 hx)

/-! ### Inertia elements preserve the valuation -/

theorem apply_mem_iff [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ inertiaGroup w) (y : Ω) : σ y ∈ w ↔ y ∈ w := by
  refine ⟨fun h => ?_, fun h => mem_of_residue (mem_inertiaGroup_iff.1 hσ) h⟩
  have h2 := inv_mem_of_residue (mem_inertiaGroup_iff.1 hσ) h
  rwa [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h2

theorem val_le_iff [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ inertiaGroup w) {a b : Ω} (hb : b ≠ 0) :
    w.valuation (σ a) ≤ w.valuation (σ b) ↔ w.valuation a ≤ w.valuation b := by
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have hpos : 0 < w.valuation b := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hb)
  have hpos' : 0 < w.valuation (σ b) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hσb)
  rw [← div_le_one₀ hpos', ← div_le_one₀ hpos, ← Valuation.map_div, ← Valuation.map_div,
    ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, ← map_div₀,
    apply_mem_iff hσ]

/-- **Inertia elements preserve the valuation** (finite orbits forbid a strict monotone run). -/
theorem preserves [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ inertiaGroup w) (x : Ω) : w.valuation (σ x) = w.valuation x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  obtain ⟨N, hN, hfix⟩ := exists_pow_apply_eq σ x
  have hσk : ∀ k : ℕ, σ ^ k ∈ inertiaGroup w := fun k => Subgroup.pow_mem _ hσ k
  set f : ℕ → w.ValueGroup := fun k => w.valuation ((σ ^ k) x) with hf
  have hshift : ∀ k : ℕ, (σ ^ k) (σ x) = (σ ^ (k + 1)) x := by
    intro k
    rw [← AlgEquiv.mul_apply, ← pow_succ]
  have hstep : ∀ k : ℕ, (f (k + 1) ≤ f k ↔ w.valuation (σ x) ≤ w.valuation x) := by
    intro k
    have h := val_le_iff (hσk k) (a := σ x) (b := x) hx
    rw [hshift] at h
    exact h
  have hstep' : ∀ k : ℕ, (f k ≤ f (k + 1) ↔ w.valuation x ≤ w.valuation (σ x)) := by
    intro k
    have h := val_le_iff (hσk k) (a := x) (b := σ x) hσx
    rw [hshift] at h
    exact h
  have hf0 : f 0 = w.valuation x := by simp [hf]
  have hfN : f N = w.valuation x := by simp only [hf, hfix]
  rcases lt_trichotomy (w.valuation (σ x)) (w.valuation x) with hlt | heq | hgt
  · exfalso
    have hanti : StrictAnti f := strictAnti_nat_of_succ_lt fun k =>
      not_le.mp fun h => (not_le.mpr hlt) ((hstep' k).1 h)
    have := hanti hN
    rw [hfN, hf0] at this
    exact lt_irrefl _ this
  · exact heq
  · exfalso
    have hmono : StrictMono f := strictMono_nat_of_lt_succ fun k =>
      not_le.mp fun h => (not_le.mpr hgt) ((hstep k).1 h)
    have := hmono hN
    rw [hfN, hf0] at this
    exact lt_irrefl _ this

/-- Conjugating a wild element by an inertia element stays wild. -/
theorem wild_conj_mem [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω} {g π : Ω ≃ₐ[K] Ω}
    (hg : g ∈ inertiaGroup w) (hπ : π ∈ wildGroup w) : g * π * g⁻¹ ∈ wildGroup w := by
  rw [mem_wildGroup_iff]
  intro x hx
  have hy0 : g⁻¹ x ≠ 0 := (map_ne_zero g⁻¹).mpr hx
  have hgy : g (g⁻¹ x) = x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have e : (g * π * g⁻¹) x - x = g (π (g⁻¹ x) - g⁻¹ x) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, map_sub, hgy]
  have hv : w.valuation (g⁻¹ x) = w.valuation x := by
    have h := preserves hg (g⁻¹ x)
    rw [hgy] at h
    exact h.symm
  rw [e, preserves hg, ← hv]
  exact mem_wildGroup_iff.1 hπ _ hy0

/-- The wild subgroup, inside the inertia subgroup. -/
abbrev wildInInertia [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω) :
    Subgroup (inertiaGroup (K := K) w) :=
  (wildGroup (K := K) w).subgroupOf (inertiaGroup w)

instance wildInInertia_normal [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω) :
    (wildInInertia (K := K) w).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using wild_conj_mem g.2 hn

/-- **The tame quotient** of inertia by wild inertia. -/
abbrev TameQuotient [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω) :=
  inertiaGroup (K := K) w ⧸ wildInInertia (K := K) w

/-! ### Cyclic quotients from a generator modulo a normal subgroup -/

theorem isCyclic_quotient_of_gen {G : Type*} [Group G] (W : Subgroup G) [W.Normal] (g : G)
    (hg : ∀ σ : G, ∃ k : ℤ, σ⁻¹ * g ^ k ∈ W) : IsCyclic (G ⧸ W) := by
  refine ⟨⟨QuotientGroup.mk g, fun y => ?_⟩⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := hg σ
  refine ⟨k, ?_⟩
  show (QuotientGroup.mk g : G ⧸ W) ^ k = QuotientGroup.mk σ
  rw [← QuotientGroup.mk_zpow]
  exact (QuotientGroup.eq.mpr hk).symm

/-! ### Valuations on finite layers -/

theorem comap_valuation_isEquiv {L : Type*} [Field L] (f : L →+* Ω) (w : ValuationSubring Ω) :
    (w.comap f).valuation.IsEquiv (w.valuation.comap f) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff, Valuation.comap_apply,
    ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]

/-! ### The Krull topology -/

section Topology

variable [IsGalois K Ω]

/-- Conditions on the value at one element are locally constant in the Krull topology. -/
theorem isOpen_setOf_apply (x : Ω) (p : Ω → Prop) : IsOpen {σ : Ω ≃ₐ[K] Ω | p (σ x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)),
    ?_, ?_, ?_⟩
  · intro τ hτ
    have h1 : (σ⁻¹ * τ) x = x := hτ
    have h2 : τ x = σ x := by
      have h3 := congrArg σ h1
      rwa [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ σ⁻¹, mul_inv_cancel,
        AlgEquiv.one_apply] at h3
    show p (τ x)
    rw [h2]
    exact hσ
  · exact (stabilizer_isOpen_of_isIntegral x).preimage (continuous_const.mul continuous_id)
  · show (σ⁻¹ * σ) • x = x
    rw [inv_mul_cancel, one_smul]

theorem isClosed_setOf_apply (x : Ω) (p : Ω → Prop) :
    IsClosed {σ : Ω ≃ₐ[K] Ω | p (σ x)} := by
  apply isOpen_compl_iff.mp
  simpa only [Set.compl_ofPred] using isOpen_setOf_apply (K := K) x (fun y => ¬ p y)

theorem isClosed_setOf_forall (p : Ω → Ω → Prop) :
    IsClosed {σ : Ω ≃ₐ[K] Ω | ∀ x, p x (σ x)} := by
  have e : {σ : Ω ≃ₐ[K] Ω | ∀ x, p x (σ x)} = ⋂ x, {σ | p x (σ x)} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [e]
  exact isClosed_iInter fun x => isClosed_setOf_apply x (p x)

theorem isClosed_inertiaGroup (w : ValuationSubring Ω) :
    IsClosed (inertiaGroup (K := K) w : Set (Ω ≃ₐ[K] Ω)) :=
  isClosed_setOf_forall (fun x y => x ∈ w → w.valuation (y - x) < 1)

theorem isClosed_wildGroup (w : ValuationSubring Ω) :
    IsClosed (wildGroup (K := K) w : Set (Ω ≃ₐ[K] Ω)) :=
  isClosed_setOf_forall (fun x y => x ≠ 0 → w.valuation (y - x) < w.valuation x)

instance compactSpace_inertiaGroup (w : ValuationSubring Ω) :
    CompactSpace (inertiaGroup (K := K) w) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaGroup w).isCompact

instance compactSpace_tameQuotient (w : ValuationSubring Ω) :
    CompactSpace (TameQuotient (K := K) w) :=
  Function.Surjective.compactSpace (f := (QuotientGroup.mk : inertiaGroup (K := K) w → _))
    QuotientGroup.continuous_mk QuotientGroup.mk_surjective

example (w : ValuationSubring Ω) : IsTopologicalGroup (TameQuotient (K := K) w) := inferInstance

/-! ### Restriction to finite Galois layers -/

/-- Restriction of an inertia element to a finite Galois layer. -/
def layerRestrict (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    inertiaGroup (K := K) w →* (L.toIntermediateField ≃ₐ[K] L.toIntermediateField) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L.toIntermediateField).comp
    (inertiaGroup (K := K) w).subtype

theorem layerRestrict_apply (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)
    (σ : inertiaGroup (K := K) w) (x : L.toIntermediateField) :
    ((layerRestrict w L σ x : L.toIntermediateField) : Ω) = (σ : Ω ≃ₐ[K] Ω) (x : Ω) :=
  AlgEquiv.restrictNormal_commutes (σ : Ω ≃ₐ[K] Ω) L.toIntermediateField x

theorem mem_ker_layerRestrict (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)
    (σ : inertiaGroup (K := K) w) :
    σ ∈ (layerRestrict w L).ker ↔ (σ : Ω ≃ₐ[K] Ω) ∈ L.toIntermediateField.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker L.toIntermediateField]
  rfl

theorem isOpen_ker_layerRestrict (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    IsOpen ((layerRestrict w L).ker : Set (inertiaGroup (K := K) w)) := by
  have e : ((layerRestrict w L).ker : Set (inertiaGroup (K := K) w)) =
      Subtype.val ⁻¹' (L.toIntermediateField.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) := by
    ext σ
    exact mem_ker_layerRestrict w L σ
  rw [e]
  exact L.toIntermediateField.fixingSubgroup_isOpen.preimage continuous_subtype_val

/-! ### Open normal subgroups form a basis -/

/-- **Open normal subgroups of the actual tame quotient form a basis at `1`**: each one is the
image of the inertia elements trivial on a finite Galois layer. -/
theorem tame_hbasis (w : ValuationSubring Ω) :
    ∀ U ∈ 𝓝 (1 : TameQuotient (K := K) w), ∃ N : Subgroup (TameQuotient (K := K) w),
      N.Normal ∧ IsOpen (N : Set (TameQuotient (K := K) w)) ∧
        (N : Set (TameQuotient (K := K) w)) ⊆ U := by
  intro U hU
  have h1 : (QuotientGroup.mk : inertiaGroup (K := K) w → TameQuotient (K := K) w) ⁻¹' U ∈
      𝓝 (1 : inertiaGroup (K := K) w) :=
    QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds (by simpa using hU)
  rw [mem_nhds_subtype] at h1
  obtain ⟨V, hV, hVU⟩ := h1
  have hV' : V ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) := by simpa using hV
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := K) (K := Ω) V).1 hV'
  refine ⟨(layerRestrict w L).ker.map (QuotientGroup.mk' (wildInInertia (K := K) w)),
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · rw [Subgroup.coe_map, QuotientGroup.coe_mk']
    exact QuotientGroup.isOpenMap_coe _ (isOpen_ker_layerRestrict w L)
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hVU (hL ((mem_ker_layerRestrict w L σ).1 hσ))

/-! ### Finite quotients are cyclic -/

variable (K Ω) in
/-- **Finite-layer tame cyclicity** (the input shape provided by the finite tame-character
theorem): on every finite Galois layer `L`, for every valuation subring of `L` over `O` and
every group of automorphisms satisfying the inertia conditions, the wild elements form a normal
subgroup modulo which some element generates. -/
def FiniteLayerTameCyclic (O : ValuationSubring K) : Prop :=
  ∀ (L : FiniteGaloisIntermediateField K Ω) (wL : ValuationSubring L.toIntermediateField),
    wL.comap (algebraMap K L.toIntermediateField) = O →
    ∀ G : Subgroup (L.toIntermediateField ≃ₐ[K] L.toIntermediateField),
      (∀ σ ∈ G, (∀ x, wL.valuation (σ x) = wL.valuation x) ∧
        ∀ u, wL.valuation u = 1 → wL.valuation (σ u - u) < 1) →
      ∃ W : Subgroup G, W.Normal ∧ (∃ g : G, ∀ σ : G, ∃ k : ℤ, σ⁻¹ * g ^ k ∈ W) ∧
        ∀ σ : G, σ ∈ W ↔ ∀ x, x ≠ 0 →
          wL.valuation ((σ : L.toIntermediateField ≃ₐ[K] L.toIntermediateField) x - x) <
            wL.valuation x

/-- **Every quotient of the actual tame quotient by an open normal subgroup is cyclic.** The
open normal subgroup pulls back to an open subgroup of inertia containing the wild group; by
compactness, strict displacement on finitely many elements already forces membership; the
finite Galois layer generated by them carries a cyclic tame quotient through which the given
quotient factors. -/
theorem tame_hcyc (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (hfin : FiniteLayerTameCyclic K Ω O) :
    ∀ (N : Subgroup (TameQuotient (K := K) w)) [N.Normal],
      IsOpen (N : Set (TameQuotient (K := K) w)) → IsCyclic (TameQuotient (K := K) w ⧸ N) := by
  intro N _ hN
  classical
  set q := QuotientGroup.mk' (wildInInertia (K := K) w) with hq
  let NI : Subgroup (inertiaGroup (K := K) w) := N.comap q
  have hNIo : IsOpen (NI : Set (inertiaGroup (K := K) w)) :=
    hN.preimage QuotientGroup.continuous_mk
  let t : Finset Ω → Set (inertiaGroup (K := K) w) := fun S =>
    {σ | ∀ x ∈ S, x ≠ 0 → w.valuation ((σ : Ω ≃ₐ[K] Ω) x - x) < w.valuation x}
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    have e : t S = Subtype.val ⁻¹' {g : Ω ≃ₐ[K] Ω | ∀ x, (fun x y =>
        x ∈ S → x ≠ 0 → w.valuation (y - x) < w.valuation x) x (g x)} := rfl
    rw [e]
    exact (isClosed_setOf_forall (K := K) (Ω := Ω) (fun x y =>
      x ∈ S → x ≠ 0 → w.valuation (y - x) < w.valuation x)).preimage continuous_subtype_val
  have hdir : Directed (· ⊇ ·) t := by
    intro S T
    exact ⟨S ∪ T, fun σ hσ x hx => hσ x (Finset.mem_union_left T hx),
      fun σ hσ x hx => hσ x (Finset.mem_union_right S hx)⟩
  have hdisj : (NI : Set (inertiaGroup (K := K) w))ᶜ ∩ ⋂ S, t S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun σ hσ => hσ.1 ?_
    have hall : ∀ S, σ ∈ t S := Set.mem_iInter.mp hσ.2
    have hwild : (σ : Ω ≃ₐ[K] Ω) ∈ wildGroup w := by
      rw [mem_wildGroup_iff]
      intro x hx
      exact hall {x} x (Finset.mem_singleton_self x) hx
    have h1 : q σ = 1 := (QuotientGroup.eq_one_iff σ).2 ((Subgroup.mem_subgroupOf).2 hwild)
    show q σ ∈ N
    rw [h1]
    exact N.one_mem
  have hcpt : IsCompact (NI : Set (inertiaGroup (K := K) w))ᶜ := hNIo.isClosed_compl.isCompact
  obtain ⟨S, hS⟩ := hcpt.elim_directed_family_closed t htc
    (Set.disjoint_iff_inter_eq_empty.mpr hdisj) hdir
  have htS : ∀ σ, σ ∈ t S → σ ∈ NI := by
    intro σ hσ
    by_contra hn
    exact Set.disjoint_left.mp hS hn hσ
  -- the finite Galois layer generated by `S`
  let L : FiniteGaloisIntermediateField K Ω := FiniteGaloisIntermediateField.adjoin K (S : Set Ω)
  have hSL : (S : Set Ω) ⊆ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K (S : Set Ω)
  let wL : ValuationSubring L.toIntermediateField := w.comap (algebraMap L.toIntermediateField Ω)
  have hwL : wL.comap (algebraMap K L.toIntermediateField) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  let ρ := layerRestrict w L
  have hequiv := comap_valuation_isEquiv (algebraMap L.toIntermediateField Ω) w
  have hG : ∀ τ ∈ ρ.range, (∀ x, wL.valuation (τ x) = wL.valuation x) ∧
      ∀ u, wL.valuation u = 1 → wL.valuation (τ u - u) < 1 := by
    intro τ hτ
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.1 hτ
    refine ⟨fun x => ?_, fun u hu => ?_⟩
    · rw [hequiv.eq_iff, Valuation.comap_apply, Valuation.comap_apply]
      change w.valuation (((ρ σ x : L.toIntermediateField) : Ω)) = w.valuation (x : Ω)
      rw [layerRestrict_apply]
      exact preserves σ.2 (x : Ω)
    · rw [hequiv.eq_one_iff_eq_one, Valuation.comap_apply] at hu
      rw [hequiv.lt_one_iff_lt_one, Valuation.comap_apply, map_sub]
      change w.valuation (((ρ σ u : L.toIntermediateField) : Ω) - (u : Ω)) < 1
      rw [layerRestrict_apply]
      exact (mem_inertiaGroup_iff.1 σ.2) (u : Ω) ((w.valuation_le_one_iff _).1 hu.le)
  obtain ⟨W, hWn, ⟨g, hg⟩, hWiff⟩ := hfin L wL hwL ρ.range hG
  let Ψ : inertiaGroup (K := K) w →* ρ.range ⧸ W := (QuotientGroup.mk' W).comp ρ.rangeRestrict
  have hker : ∀ σ ∈ Ψ.ker, σ ∈ NI := by
    intro σ hσ
    have h1 : ρ.rangeRestrict σ ∈ W := (QuotientGroup.eq_one_iff _).1 hσ
    have h2 := (hWiff _).1 h1
    apply htS
    intro x hxS hx0
    have hxL : x ∈ L.toIntermediateField := hSL hxS
    have h3 := h2 ⟨x, hxL⟩ (fun h => hx0 (congrArg Subtype.val h))
    have h4 : (((ρ.rangeRestrict σ : L.toIntermediateField ≃ₐ[K] L.toIntermediateField)
        ⟨x, hxL⟩ : L.toIntermediateField) : Ω) = (σ : Ω ≃ₐ[K] Ω) x :=
      layerRestrict_apply w L σ ⟨x, hxL⟩
    have h5 : (w.valuation.comap (algebraMap L.toIntermediateField Ω))
        ((ρ.rangeRestrict σ : L.toIntermediateField ≃ₐ[K] L.toIntermediateField) ⟨x, hxL⟩ -
          ⟨x, hxL⟩) = w.valuation ((σ : Ω ≃ₐ[K] Ω) x - x) := by
      rw [Valuation.comap_apply, map_sub]
      exact congrArg (fun y => w.valuation (y - x)) h4
    have h6 := hequiv.lt_iff_lt.1 h3
    rw [h5] at h6
    exact h6
  let Φ : inertiaGroup (K := K) w →* TameQuotient (K := K) w ⧸ N := (QuotientGroup.mk' N).comp q
  have hΦ : Function.Surjective Φ :=
    (QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective _)
  have hle : Ψ.ker ≤ Φ.ker := by
    intro σ hσ
    have h1 : q σ ∈ N := hker σ hσ
    exact (QuotientGroup.eq_one_iff (q σ)).2 h1
  have : IsCyclic (ρ.range ⧸ W) := isCyclic_quotient_of_gen W g hg
  have hc1 : IsCyclic (inertiaGroup (K := K) w ⧸ Ψ.ker) := by
    let e := QuotientGroup.quotientKerEquivRange Ψ
    exact isCyclic_of_surjective e.symm e.symm.surjective
  let Φ' := QuotientGroup.lift Ψ.ker Φ hle
  have hΦ' : Function.Surjective Φ' := by
    intro y
    obtain ⟨σ, rfl⟩ := hΦ y
    exact ⟨QuotientGroup.mk σ, QuotientGroup.lift_mk _ hle σ⟩
  exact isCyclic_of_surjective Φ' hΦ'

/-! ### Density in finite layers -/

/-- **A topological generator in finite layers**: if the class of `τ` generates a dense subgroup
of the actual tame quotient, then on every finite Galois layer every inertia element agrees with
a power of `τ` times an actual wild element. -/
theorem layer_agreement_of_dense (w : ValuationSubring Ω) (τ : inertiaGroup (K := K) w)
    (hτ : Dense ((Subgroup.zpowers (QuotientGroup.mk τ : TameQuotient (K := K) w)) :
      Set (TameQuotient (K := K) w)))
    (σ : inertiaGroup (K := K) w) (L : FiniteGaloisIntermediateField K Ω) :
    ∃ k : ℤ, ∃ π ∈ wildGroup (K := K) w,
      layerRestrict w L (τ ^ k) * AlgEquiv.restrictNormalHom L.toIntermediateField π =
        layerRestrict w L σ := by
  let F := (layerRestrict w L).ker
  let Uset : Set (inertiaGroup (K := K) w) := (fun ρ => σ⁻¹ * ρ) ⁻¹' (F : Set _)
  have hUo : IsOpen Uset :=
    (isOpen_ker_layerRestrict w L).preimage (continuous_const.mul continuous_id)
  have hV : IsOpen ((QuotientGroup.mk : inertiaGroup (K := K) w → TameQuotient (K := K) w) ''
      Uset) := QuotientGroup.isOpenMap_coe _ hUo
  have hσU : σ ∈ Uset := by
    show σ⁻¹ * σ ∈ F
    rw [inv_mul_cancel]
    exact F.one_mem
  obtain ⟨y, hy, hyV⟩ := hτ.exists_mem_open hV ⟨_, σ, hσU, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨ρ, hρU, hρ⟩ := hyV
  rw [← QuotientGroup.mk_zpow] at hρ
  have hw' : (τ ^ k)⁻¹ * ρ ∈ wildInInertia (K := K) w := QuotientGroup.eq.1 hρ.symm
  refine ⟨k, (((τ ^ k)⁻¹ * ρ : inertiaGroup (K := K) w) : Ω ≃ₐ[K] Ω),
    (Subgroup.mem_subgroupOf).1 hw', ?_⟩
  have h1 : layerRestrict w L ((τ ^ k)⁻¹ * ρ) = AlgEquiv.restrictNormalHom
      L.toIntermediateField (((τ ^ k)⁻¹ * ρ : inertiaGroup (K := K) w) : Ω ≃ₐ[K] Ω) := rfl
  rw [← h1, ← map_mul, mul_inv_cancel_left]
  have h3 : layerRestrict w L (σ⁻¹ * ρ) = 1 := hρU
  rw [map_mul, map_inv, inv_mul_eq_one] at h3
  exact h3.symm

end Topology

end ActualTameInertia

#print axioms ActualTameInertia.tame_hbasis
#print axioms ActualTameInertia.tame_hcyc
#print axioms ActualTameInertia.layer_agreement_of_dense
#print axioms ActualTameInertia.isClosed_wildGroup
#print axioms ActualTameInertia.wildInInertia_normal
#print axioms ActualTameInertia.compactSpace_tameQuotient
