import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.ZHat
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent

/-!
# UnramifiedComplex: `H²(ℤ̂, W) = 0` for finite discrete `W`

Manuscript `diophantine_zq.tex`, tex 3478–3481: the unramified complex `[Φ−1]` lives in degrees
zero and one, so its comparison with the continuous cohomology of `Gal(K_w^ur/K_w) ≃ ℤ̂` needs
`H²(ℤ̂, W) = 0` (cohomological dimension one of `ℤ̂` on finite modules).

`mem_B2_of_mem_Z2`: for `G ≃ₜ* ℤ̂` (compact, totally disconnected) and a finite discrete continuous
`G`-module `W`, every continuous `2`-cocycle `c` is the coboundary of a continuous cochain. Proof:
`c` descends to a finite quotient `G ⧸ U` (Tau Ceti `exists_openNormalSubgroup_descendZ2`), so it is
periodic along the powers of the Frobenius; the primitive `Ψ` on `ℕ`
(`Ψ(0) = c(1,1)`, `Ψ(n+1) = Ψ(n) + Frob^n • c(1,1) − c(Frob^n, Frob)`, `prim`) satisfies
`dΨ = c` on powers of the Frobenius (`prim_spec`) and is periodic (`prim_add_period`), so
`φ(g) = Ψ(χ(g))` with the character `χ : G → ℤ/P` is continuous and `dφ = c` on a dense set, hence
everywhere.

`h2_eq_zero` (explicit `H²`) and `subsingleton_continuousCohomology_two` (Mathlib's
`continuousCohomology 2 X`, through Tau Ceti's degree-two comparison).

Kinds: everything PROVED.
-/

open CategoryTheory TauCeti.ContCohomology
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : G ≃ₜ* TauCeti.zHat.{0})
  {k : Type} [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G)

attribute [local instance] TopRep.distribMulAction

section Recursion

variable (c : G × G → X.V)

/-- The primitive on powers of the Frobenius: `Ψ(0) = c(1,1)`,
`Ψ(n+1) = Ψ(n) + Frob^n • c(1,1) − c(Frob^n, Frob)`. -/
def prim : ℕ → X.V
  | 0 => c (1, 1)
  | n + 1 => prim n + frobElt e ^ n • c (1, 1) - c (frobElt e ^ n, frobElt e)

/-- `dΨ = c` on pairs of powers of the Frobenius. -/
theorem prim_spec (hc : groupCohomology.IsCocycle₂ c) (a b : ℕ) :
    frobElt e ^ a • prim e X c b - prim e X c (a + b) + prim e X c a =
      c (frobElt e ^ a, frobElt e ^ b) := by
  induction b with
  | zero =>
    simp only [prim, pow_zero, add_zero, sub_add_cancel]
    exact (groupCohomology.map_one_snd_of_isCocycle₂ hc _).symm
  | succ b ih =>
    have hcoc := hc (frobElt e ^ a) (frobElt e ^ b) (frobElt e)
    rw [← pow_add, ← pow_succ] at hcoc
    rw [← add_assoc, prim, prim]
    have h2 : c (frobElt e ^ a, frobElt e ^ (b + 1)) = c (frobElt e ^ (a + b), frobElt e) +
        c (frobElt e ^ a, frobElt e ^ b) - frobElt e ^ a • c (frobElt e ^ b, frobElt e) := by
      rw [hcoc]; abel
    rw [h2, ← ih, smul_sub, smul_add, ← mul_smul, ← pow_add]
    abel

/-- One step of the period. -/
theorem prim_add (hc : groupCohomology.IsCocycle₂ c) (m R : ℕ) :
    prim e X c (m + R) = prim e X c m + (frobElt e ^ m • prim e X c R -
      c (frobElt e ^ m, frobElt e ^ R)) := by
  have := prim_spec e X c hc m R
  rw [← this]; abel

/-- Powers `Frob^{Rt}` act trivially when `Frob^R` does. -/
theorem smul_pow_mul_eq {R : ℕ} (hR : ∀ x : X.V, frobElt e ^ R • x = x) (n t : ℕ) (x : X.V) :
    frobElt e ^ (n + R * t) • x = frobElt e ^ n • x := by
  rw [pow_add, mul_smul, pow_mul]
  congr 1
  exact MulAction.mem_stabilizer_iff.mp
    (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr (hR x)) t)

/-- `Ψ(n + Rt) = Ψ(n) + t • D(n)` with `D` the `R`-periodic increment. -/
theorem prim_add_mul (hc : groupCohomology.IsCocycle₂ c) {R : ℕ}
    (hR : ∀ x : X.V, frobElt e ^ R • x = x)
    (hRc : ∀ a b : ℕ, c (frobElt e ^ (a + R), frobElt e ^ b) = c (frobElt e ^ a, frobElt e ^ b))
    (n t : ℕ) :
    prim e X c (n + R * t) = prim e X c n + t • (frobElt e ^ n • prim e X c R -
      c (frobElt e ^ n, frobElt e ^ R)) := by
  have hc' : ∀ t b : ℕ, c (frobElt e ^ (n + R * t), frobElt e ^ b) =
      c (frobElt e ^ n, frobElt e ^ b) := by
    intro t b
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← add_assoc, hRc, ih]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, ← add_assoc, prim_add e X c hc, ih, smul_pow_mul_eq e X hR, hc', succ_nsmul]
    abel

/-- `Ψ` is periodic with period `R |W|`. -/
theorem prim_add_period [Finite X.V] (hc : groupCohomology.IsCocycle₂ c) {R : ℕ}
    (hR : ∀ x : X.V, frobElt e ^ R • x = x)
    (hRc : ∀ a b : ℕ, c (frobElt e ^ (a + R), frobElt e ^ b) = c (frobElt e ^ a, frobElt e ^ b))
    (n q : ℕ) : prim e X c (n + R * Nat.card X.V * q) = prim e X c n := by
  have h1 : ∀ m, prim e X c (m + R * Nat.card X.V) = prim e X c m := fun m => by
    rw [prim_add_mul e X c hc hR hRc, card_nsmul_eq_zero', add_zero]
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, h1, ih]

end Recursion

/-- `Frob^n` acts as `Frob^{n mod P}` when `Frob^P` acts trivially. -/
theorem zpow_smul_eq_val' {P : ℕ} [NeZero P] (hP : ∀ x : X.V, frobElt e ^ P • x = x)
    (n : ℤ) (x : X.V) : frobElt e ^ n • x = frobElt e ^ ((n : ZMod P).val) • x := by
  have h1 : (((n : ZMod P).val : ℕ) : ℤ) = n % (P : ℤ) := ZMod.val_intCast n
  have hq : ∀ q : ℤ, frobElt e ^ ((P : ℤ) * q) • x = x := fun q => by
    rw [zpow_mul, zpow_natCast]
    exact MulAction.mem_stabilizer_iff.mp
      (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr (hP x)) q)
  conv_lhs => rw [← Int.emod_add_mul_ediv n P]
  rw [zpow_add, mul_smul, hq, ← h1, zpow_natCast]

/-- `Frob^n ≡ Frob^{n mod P}` modulo `U` when `Frob^P ∈ U`. -/
theorem coset_zpow_eq_val {U : Subgroup G} {P : ℕ} [NeZero P] (hP : frobElt e ^ P ∈ U) (n : ℤ) :
    ((frobElt e ^ n : G) : G ⧸ U) = ((frobElt e ^ ((n : ZMod P).val) : G) : G ⧸ U) := by
  have h1 : (((n : ZMod P).val : ℕ) : ℤ) = n % (P : ℤ) := ZMod.val_intCast n
  conv_lhs => rw [← Int.emod_add_mul_ediv n P]
  rw [zpow_add, ← h1, zpow_natCast, QuotientGroup.mk_mul_of_mem]
  rw [zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem _ hP _

include e in
/-- **Every continuous `2`-cocycle of `G ≃ ℤ̂` with values in a finite discrete module is a
continuous coboundary.** PROVED. -/
theorem mem_B2_of_mem_Z2 [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology X.V]
    [ContinuousSMul G X.V] [Finite X.V] (c : Z2 G X.V) : (c : G × G → X.V) ∈ B2 G X.V := by
  obtain ⟨hcont, hcoc⟩ := mem_Z2_iff.1 c.2
  obtain ⟨U, cbar, hcbar⟩ := exists_openNormalSubgroup_descendZ2 c
  have hfin : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  set Q := orderOf ((frobElt e : G) : G ⧸ U.toSubgroup) with hQdef
  have hQ0 : 0 < Q := (isOfFinOrder_of_finite _).orderOf_pos
  have hσQ : frobElt e ^ Q ∈ U.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hQdef, pow_orderOf_eq_one]
  obtain ⟨N, hN0, hN⟩ := exists_period e X
  set R := Q * N with hRdef
  have hRU : ∀ t : ℕ, frobElt e ^ (R * t) ∈ U.toSubgroup := fun t => by
    rw [hRdef, mul_assoc, pow_mul]; exact Subgroup.pow_mem _ hσQ _
  have hR : ∀ x : X.V, frobElt e ^ R • x = x := fun x => by
    rw [hRdef, mul_comm, pow_mul]
    exact MulAction.mem_stabilizer_iff.mp
      (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr (hN x)) Q)
  have hcoset : ∀ g g' h h' : G, (g : G ⧸ U.toSubgroup) = g' → (h : G ⧸ U.toSubgroup) = h' →
      (c : G × G → X.V) (g, h) = (c : G × G → X.V) (g', h') := by
    intro g g' h h' hg hh
    rw [← hcbar, ← hcbar, hg, hh]
  have hRc : ∀ a b : ℕ, (c : G × G → X.V) (frobElt e ^ (a + R), frobElt e ^ b) =
      (c : G × G → X.V) (frobElt e ^ a, frobElt e ^ b) := fun a b => by
    refine hcoset _ _ _ _ ?_ rfl
    rw [pow_add, QuotientGroup.mk_mul_of_mem]
    simpa using hRU 1
  set P := R * Nat.card X.V with hPdef
  have hP0 : 0 < P := Nat.mul_pos (Nat.mul_pos hQ0 hN0) Nat.card_pos
  have : NeZero P := ⟨hP0.ne'⟩
  have hPU : frobElt e ^ P ∈ U.toSubgroup := by rw [hPdef]; exact hRU _
  have hPact : ∀ x : X.V, frobElt e ^ P • x = x := fun x => by
    rw [hPdef, pow_mul]
    exact MulAction.mem_stabilizer_iff.mp
      (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr (hR x)) _)
  have hprim_mod : ∀ m : ℕ, prim e X c (m % P) = prim e X c m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m P]
    rw [hPdef, prim_add_period e X c hcoc hR hRc]
  set φ : G → X.V := fun g => prim e X c ((chi e P g).toAdd.val) with hφdef
  have hφ : Continuous φ := (continuous_of_discreteTopology (f := fun a : Multiplicative (ZMod P) =>
    prim e X c a.toAdd.val)).comp (map_continuous (chi e P))
  rw [mem_B2_iff]
  refine ⟨φ, hφ, ?_⟩
  refine ((denseRange_zpow e).prodMap (denseRange_zpow e)).equalizer (continuous_d1_apply hφ)
    hcont (funext fun p => ?_)
  obtain ⟨a, b⟩ := p
  simp only [Function.comp_apply, Prod.map_apply, d1_apply, hφdef, ← zpow_add, chi_zpow,
    toAdd_ofAdd, Int.cast_add, ZMod.val_add, hprim_mod]
  rw [zpow_smul_eq_val' e X hPact a,
    hcoset (frobElt e ^ a) (frobElt e ^ ((a : ZMod P).val)) (frobElt e ^ b)
      (frobElt e ^ ((b : ZMod P).val)) (coset_zpow_eq_val e hPU a) (coset_zpow_eq_val e hPU b)]
  exact prim_spec e X c hcoc _ _

include e in
/-- **`H²(G, W) = 0`** on Tau Ceti's explicit continuous model, for `G ≃ₜ* ℤ̂` and finite discrete
`W`. PROVED. -/
theorem h2_eq_zero [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology X.V]
    [ContinuousSMul G X.V] [Finite X.V] (x : H2 G X.V) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact mem_B2_of_mem_Z2 e X c

include e in
/-- **`H²_cont(G, W) = 0`** for Mathlib's `continuousCohomology 2 X`, `G ≃ₜ* ℤ̂` and finite
discrete `W` (cohomological dimension one, tex 3478–3481). PROVED. -/
theorem subsingleton_continuousCohomology_two [CompactSpace G] [TotallyDisconnectedSpace G]
    [LocallyCompactSpace G] [DiscreteTopology X.V] [ContinuousSMul G X.V] [Finite X.V] :
    Subsingleton (continuousCohomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := X.explicitH2AddEquivContinuousCohomologyOfDiscrete.surjective a
  obtain ⟨y, rfl⟩ := X.explicitH2AddEquivContinuousCohomologyOfDiscrete.surjective b
  rw [h2_eq_zero e X x, h2_eq_zero e X y]

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
