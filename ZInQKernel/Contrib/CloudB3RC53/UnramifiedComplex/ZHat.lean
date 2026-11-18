import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Complex
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

/-!
# UnramifiedComplex: `H⁰` and `H¹` of `U^ur` are continuous `H⁰` and `H¹` of `ℤ̂`

Manuscript `diophantine_zq.tex`, tex 3478–3481 and 4551–4573 (unramified row: `h⁰ + h¹` of
`[W --(Φ−1)--> W]`).

Let `G` be a topological group with a continuous isomorphism `e : G ≃ₜ* ℤ̂` (for
`G = Gal(K_w^ur/K_w)` this is Tau Ceti's `maximalUnramifiedGaloisGroupEquivZHat`), `Frob = e⁻¹(1)`
(`frobElt`), and `X` a continuous representation of `G` over `k` on a discrete module `W`
(`TopRep k G` with `DiscreteTopology X.V` and `ContinuousSMul G X.V`), with `Φ = ρ(Frob)` (`frob`).

* `h0Equiv : H⁰(U^ur) ≃ₗ[k] continuousCohomology 0 X` — via `ker(Φ − 1) = W^G`, since the powers of
  `Frob` are dense (`invariant_iff`).
* `h1ToCoinv : H¹(G, W) → W ⧸ (Φ − 1)W`, `[f] ↦ f(Frob)`, on Tau Ceti's explicit continuous `H¹`;
  injective (cocycles are determined on a topological generator) and, for finite `W`, surjective:
  the cocycle `g ↦ Σ_{j < χ(g)} Frob^j • w` built from the continuous character `χ : G → ℤ/P` with
  `P = 2N|W|`, `Frob^N = 1` on `W` (`cocycleOf`).
* `h1Equiv : H¹(U^ur) ≃+ continuousCohomology 1 X` for finite `W`, through Tau Ceti's comparison
  `TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete`.

Kinds: everything PROVED.
-/

open CategoryTheory TauCeti.ContCohomology
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : G ≃ₜ* TauCeti.zHat.{0})

/-- The arithmetic Frobenius: the element of `G` corresponding to the generator `1 ∈ ℤ̂`. -/
def frobElt : G := e.symm TauCeti.zHat.gen

/-- The powers of the Frobenius are dense in `G`. -/
theorem denseRange_zpow : DenseRange (fun n : ℤ => frobElt e ^ n) := by
  have h1 : DenseRange (fun n : ℤ => (TauCeti.zHat.gen : TauCeti.zHat.{0}) ^ n) := by
    have := TauCeti.zHat.denseRange_ofInt.{0}
    rw [DenseRange] at this ⊢
    convert this using 1
    ext x
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨Multiplicative.ofAdd n, by simp⟩
    · rintro ⟨n, rfl⟩; exact ⟨n.toAdd, by beta_reduce; rw [← TauCeti.zHat.ofInt_ofAdd, ofAdd_toAdd]⟩
  have h2 := e.symm.surjective.denseRange.comp h1 e.symm.continuous
  convert h2 using 1
  ext n
  simp [frobElt, map_zpow]

/-- Continuous maps agreeing on the powers of the Frobenius agree. -/
theorem eq_of_eq_zpow {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f₁ f₂ : G → Y}
    (h1 : Continuous f₁) (h2 : Continuous f₂) (h : ∀ n : ℤ, f₁ (frobElt e ^ n) = f₂ (frobElt e ^ n)) :
    f₁ = f₂ :=
  (denseRange_zpow e).equalizer h1 h2 (funext h)

/-- The continuous character `G → ℤ/P` sending the Frobenius to `1`. -/
def chi (P : ℕ) [NeZero P] : G →ₜ* Multiplicative (ZMod P) :=
  (TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ZMod P))).comp
    ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩

/-- `χ(Frob) = 1`. -/
theorem chi_frob (P : ℕ) [NeZero P] :
    chi e P (frobElt e) = Multiplicative.ofAdd (1 : ZMod P) := by
  simp [chi, frobElt]

/-- `χ(Frob^n) = n mod P`. -/
theorem chi_zpow (P : ℕ) [NeZero P] (n : ℤ) :
    chi e P (frobElt e ^ n) = Multiplicative.ofAdd (n : ZMod P) := by
  rw [map_zpow, chi_frob, ← ofAdd_zsmul, zsmul_one]


/-- The Frobenius topologically generates `G`. -/
theorem closure_frob_eq_top : (Subgroup.closure {frobElt e}).topologicalClosure = ⊤ := by
  rw [← Subgroup.zpowers_eq_closure]
  apply SetLike.coe_injective
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_zpowers, Subgroup.coe_top]
  exact (denseRange_zpow e).closure_range

section Rep

variable {k : Type} [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G)

attribute [local instance] TopRep.distribMulAction

/-- The Frobenius operator `Φ = ρ(Frob)` on the coefficient module. -/
def frob : X.V →ₗ[k] X.V := (X.ρ (frobElt e)).toLinearMap

theorem frob_apply (x : X.V) : frob e X x = frobElt e • x := rfl

theorem zpow_smul_eq_of {u : X.V} (h : frobElt e • u = u) (n : ℤ) : frobElt e ^ n • u = u :=
  MulAction.mem_stabilizer_iff.mp (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr h) n)

variable [ContinuousSMul G X.V] [DiscreteTopology X.V]

/-- A vector is `G`-invariant iff it is fixed by the Frobenius. -/
theorem invariant_iff (u : X.V) : (∀ g : G, X.ρ g u = u) ↔ frob e X u = u := by
  refine ⟨fun h => h _, fun h g => ?_⟩
  have := eq_of_eq_zpow e (f₁ := fun g : G => g • u) (f₂ := fun _ => u)
    (continuous_id.smul continuous_const) continuous_const (fun n => zpow_smul_eq_of e X h n)
  exact congrFun this g

/-- `ker (Φ − 1) = W^G`. -/
theorem ker_frob_sub_one : LinearMap.ker (frob e X - 1) = X.ρ.invariants := by
  ext u
  rw [LinearMap.mem_ker, ContRepresentation.mem_invariants, invariant_iff, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

/-- Evaluation of a continuous `1`-cocycle at the Frobenius, modulo `(Φ − 1) W`. -/
def evalFrob : Z1 G X.V →+ X.V ⧸ LinearMap.range (frob e X - 1) :=
  (LinearMap.range (frob e X - 1)).mkQ.toAddMonoidHom.comp
    { toFun := fun f => f.1 (frobElt e), map_zero' := rfl, map_add' := fun _ _ => rfl }

theorem evalFrob_apply (f : Z1 G X.V) :
    evalFrob e X f = Submodule.Quotient.mk (f.1 (frobElt e)) := rfl

theorem B1_le_ker_evalFrob : (B1 G X.V).addSubgroupOf (Z1 G X.V) ≤ (evalFrob e X).ker := by
  intro f hf
  rw [AddSubgroup.mem_addSubgroupOf] at hf
  obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 hf
  rw [AddMonoidHom.mem_ker, evalFrob_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨m, ?_⟩
  rw [← hm, d0_apply, LinearMap.sub_apply, Module.End.one_apply, frob_apply]

/-- **The comparison map `H¹(G, W) → W/(Φ − 1)W`**, the class of a cocycle `f` going to
`f(Frob)`. -/
def h1ToCoinv : H1 G X.V →+ X.V ⧸ LinearMap.range (frob e X - 1) :=
  QuotientAddGroup.lift _ (evalFrob e X) (B1_le_ker_evalFrob e X)

theorem h1ToCoinv_mk (f : Z1 G X.V) :
    h1ToCoinv e X (QuotientAddGroup.mk f) = Submodule.Quotient.mk (f.1 (frobElt e)) := rfl

/-- `h1ToCoinv` is injective. PROVED. -/
theorem h1ToCoinv_injective : Function.Injective (h1ToCoinv e X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H f =>
    rw [h1ToCoinv_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have hd : d0 G X.V m ∈ Z1 G X.V := B1_le_Z1 G X.V (d0_mem_B1 m)
    have : f.1 = d0 G X.V m := by
      refine eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top f.2 hd
        (closure_frob_eq_top e) ?_
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [d0_apply, ← hm, LinearMap.sub_apply, Module.End.one_apply, frob_apply]
    rw [this]
    exact d0_mem_B1 m

section Periodic

variable [Finite X.V]

/-- The Frobenius acts on the finite module `W` with finite order. -/
theorem exists_period : ∃ N : ℕ, 0 < N ∧ ∀ x : X.V, frobElt e ^ N • x = x := by
  let p : Equiv.Perm X.V := MulAction.toPermHom G X.V (frobElt e)
  refine ⟨orderOf p, (isOfFinOrder_of_finite p).orderOf_pos, fun x => ?_⟩
  have h : MulAction.toPermHom G X.V (frobElt e ^ orderOf p) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  exact congrArg (fun q : Equiv.Perm X.V => q x) h

/-- The partial sums `S(m) = Σ_{j<m} Frob^j • w`, the values of the cocycle on `Frob^m`. -/
def psum (w : X.V) (m : ℕ) : X.V := ∑ j ∈ Finset.range m, frobElt e ^ j • w

theorem psum_add (w : X.V) (m n : ℕ) :
    psum e X w (m + n) = psum e X w m + frobElt e ^ m • psum e X w n := by
  simp only [psum, Finset.sum_range_add, Finset.smul_sum, ← mul_smul, ← pow_add]

theorem psum_one (w : X.V) : psum e X w 1 = w := by simp [psum]

/-- The period used for the cocycle construction: `2 N |W|`. -/
def period (N : ℕ) : ℕ := N * (Nat.card X.V * 2)

theorem psum_mul (w : X.V) {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) (t : ℕ) :
    psum e X w (N * t) = t • psum e X w N := by
  induction t with
  | zero => simp [psum]
  | succ t ih =>
    have hNt : ∀ x : X.V, frobElt e ^ (N * t) • x = x := fun x => by
      rw [pow_mul]
      exact MulAction.mem_stabilizer_iff.mp
        (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr (hN x)) t)
    rw [Nat.mul_succ, psum_add, ih, hNt, succ_nsmul]

theorem psum_period (w : X.V) {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) :
    psum e X w (period X N) = 0 := by
  rw [period, psum_mul e X w hN, mul_comm, mul_nsmul, card_nsmul_eq_zero']

theorem pow_period_smul {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) (q : ℕ) (x : X.V) :
    frobElt e ^ (period X N * q) • x = x := by
  rw [period, mul_assoc, pow_mul]
  exact MulAction.mem_stabilizer_iff.mp
    (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr (hN x)) _)

theorem psum_mod (w : X.V) {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) (m : ℕ) :
    psum e X w (m % period X N) = psum e X w m := by
  conv_rhs => rw [← Nat.mod_add_div m (period X N)]
  have hP : ∀ x : X.V, frobElt e ^ period X N • x = x := fun x => by
    simpa using pow_period_smul e X hN 1 x
  rw [psum_add, psum_mul e X w hP, psum_period e X w hN, smul_zero, smul_zero, add_zero]

theorem one_lt_period {N : ℕ} (hN : 0 < N) : 1 < period X N := by
  have : 0 < Nat.card X.V := Nat.card_pos
  unfold period
  nlinarith

theorem zpow_period_smul {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) (q : ℤ) (x : X.V) :
    frobElt e ^ ((period X N : ℤ) * q) • x = x := by
  have hP : frobElt e ^ period X N • x = x := by simpa using pow_period_smul e X hN 1 x
  rw [zpow_mul, zpow_natCast]
  exact MulAction.mem_stabilizer_iff.mp
    (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr hP) q)

theorem zpow_smul_eq_val {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) [NeZero (period X N)]
    (n : ℤ) (x : X.V) :
    frobElt e ^ n • x = frobElt e ^ ((n : ZMod (period X N)).val) • x := by
  have h1 : (((n : ZMod (period X N)).val : ℕ) : ℤ) = n % (period X N : ℤ) := ZMod.val_intCast n
  conv_lhs => rw [← Int.emod_add_mul_ediv n (period X N)]
  rw [zpow_add, mul_smul, zpow_period_smul e X hN, ← h1, zpow_natCast]

theorem smul_eq_chi {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) [NeZero (period X N)]
    (g : G) (x : X.V) :
    g • x = frobElt e ^ ((chi e (period X N) g).toAdd.val) • x := by
  have := eq_of_eq_zpow e (f₁ := fun g : G => g • x)
    (f₂ := fun g => frobElt e ^ ((chi e (period X N) g).toAdd.val) • x)
    (continuous_id.smul continuous_const)
    ((continuous_of_discreteTopology (f := fun a : Multiplicative (ZMod (period X N)) =>
      frobElt e ^ a.toAdd.val • x)).comp (map_continuous (chi e (period X N)))) (fun n => by
      simp only [chi_zpow, toAdd_ofAdd]
      exact zpow_smul_eq_val e X hN n x)
  exact congrFun this g

/-- **The cocycle attached to `w`**: `g ↦ S(χ(g))` with `χ : G → ℤ/P` the character sending the
Frobenius to `1` and `S(m) = Σ_{j<m} Frob^j • w`. -/
def cocycleOf (N : ℕ) [NeZero (period X N)] (w : X.V) : G → X.V :=
  fun g => psum e X w ((chi e (period X N) g).toAdd.val)

theorem cocycleOf_mem {N : ℕ} (hN : ∀ x : X.V, frobElt e ^ N • x = x) [NeZero (period X N)]
    (w : X.V) : cocycleOf e X N w ∈ Z1 G X.V := by
  rw [mem_Z1_iff]
  refine ⟨(continuous_of_discreteTopology (f := fun a : Multiplicative (ZMod (period X N)) =>
    psum e X w a.toAdd.val)).comp (map_continuous (chi e (period X N))), fun g h => ?_⟩
  simp only [cocycleOf, map_mul, toAdd_mul, ZMod.val_add, psum_mod e X w hN, psum_add]
  rw [← smul_eq_chi e X hN, add_comm]

theorem cocycleOf_frob {N : ℕ} (hN0 : 0 < N) [NeZero (period X N)] (w : X.V) :
    cocycleOf e X N w (frobElt e) = w := by
  have : Fact (1 < period X N) := ⟨one_lt_period X hN0⟩
  simp only [cocycleOf, chi_frob, toAdd_ofAdd, ZMod.val_one, psum_one]

end Periodic

/-- `h1ToCoinv` is surjective for finite `W`. PROVED. -/
theorem h1ToCoinv_surjective [Finite X.V] : Function.Surjective (h1ToCoinv e X) := by
  obtain ⟨N, hN0, hN⟩ := exists_period e X
  have : NeZero (period X N) := ⟨(Nat.lt_trans Nat.zero_lt_one (one_lt_period X hN0)).ne'⟩
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H w =>
    refine ⟨QuotientAddGroup.mk ⟨cocycleOf e X N w, cocycleOf_mem e X hN w⟩, ?_⟩
    rw [h1ToCoinv_mk]
    exact congrArg _ (cocycleOf_frob e X hN0 w)

/-- **`H⁰(U^ur) ≅ H⁰_cont(G, W)`** (tex 3478–3481, 4699–4700): `H⁰` of `[W --(Φ−1)--> W]` is
`ker(Φ − 1) = W^G`, which is Mathlib's `continuousCohomology 0 X` (`ContinuousCohomology.zeroIso`).
PROVED. -/
def h0Equiv : (frobCx (frob e X)).homology 0 ≃ₗ[k] continuousCohomology 0 X :=
  (h0Iso (frob e X)).toLinearEquiv ≪≫ₗ LinearEquiv.ofEq _ _ (ker_frob_sub_one e X) ≪≫ₗ
    (ContinuousCohomology.zeroIso X).toContinuousLinearEquiv.symm.toLinearEquiv

/-- **The comparison `H¹_cont(G, W) ≃ W ⧸ (Φ − 1)W`** for finite `W` (`[f] ↦ f(Frob)`). -/
def h1CoinvEquiv [Finite X.V] : H1 G X.V ≃+ X.V ⧸ LinearMap.range (frob e X - 1) :=
  AddEquiv.ofBijective (h1ToCoinv e X) ⟨h1ToCoinv_injective e X, h1ToCoinv_surjective e X⟩

/-- **`H¹(U^ur) ≅ H¹_cont(G, W)`** for finite `W` (tex 3478–3481): `H¹` of `[W --(Φ−1)--> W]` is
`W ⧸ (Φ − 1)W`, which is the explicit continuous `H¹(G, W)` (`h1CoinvEquiv`), which is Mathlib's
`continuousCohomology 1 X` (Tau Ceti's comparison). PROVED. -/
def h1Equiv [Finite X.V] : (frobCx (frob e X)).homology 1 ≃+ continuousCohomology 1 X :=
  (h1Iso (frob e X)).toLinearEquiv.toAddEquiv.trans
    ((h1CoinvEquiv e X).symm.trans X.explicitH1AddEquivContinuousCohomologyOfDiscrete)

end Rep

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
