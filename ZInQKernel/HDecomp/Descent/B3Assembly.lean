import ZInQKernel.HDecomp.Descent.Cochain
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.HDecomp.Descent.B2Assembly

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/B3Assembly.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: B3 over `G_ℚ` (N5 L701-716), from the leaves of B2

`b3_of_leaves`: with the hypotheses of `b2_of_leaves` and `ε` normalized (`ε(1,1) = 1`), there
are `χ`, `β` as in B2 and an intermediate field `L' ⊇ L` of `ℚ̄/ℚ` (the kernel field of
`β|_{G_L}`), Galois over `ℚ`, with `G_{L'} = ker(β|_{G_L})`, `β` constant on the cosets of
`G_{L'}`, and `[L' : ℚ] ≤ 2 · ord(χ) · [L : ℚ]`.

`b3_degree_le_QM`: if moreover `[L:ℚ] ≤ D` and `T = S ∪ supp M_S(u)` for an admissible `(S, R)`,
then `[L' : ℚ] ≤ Q_R · M_S(u)` (the repository's `heightQ`, `contactSupport`).

Not here: that `L'` is unramified outside `T` after the twist of N5 L702-709. Its group theory is
`twist_kills_inertia` and `inertia_le_kernel` (Cochain.lean); it needs inertia subgroups of
`G_ℚ` (absent from Mathlib) and leaves L-B3a, L-B3b.

Compile out of tree as in B2Assembly.lean (oleans for Cochain, Constants, Chi, B2Glue,
B2Assembly in `scratch/glue-descent/.lake/out/GlueDescent/`).
-/

namespace GlueDescent.B3Q

open GlueDescent GlueDescent.B2 GlueDescent.B2Q

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- `G_L ≤ G_ℚ`. -/
noncomputable def GQL (L : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subgroup GQ :=
    L.fixingSubgroup

theorem mem_GQL {L : IntermediateField ℚ (AlgebraicClosure ℚ)} {σ : GQ} :
    σ ∈ GQL L ↔ ∀ x ∈ L, act σ x = x :=
  IntermediateField.mem_fixingSubgroup_iff L σ

/-- A normalized cocycle inflated from `Gal(L/ℚ)` is `1` as soon as one argument is in `G_L`. -/
theorem inflatedNormalized_of (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1) :
    InflatedNormalized (GQL L) ε := by
  have hc := hε.2.2
  intro σ τ h
  rcases h with h | h
  · have e1 : ε σ τ = ε 1 τ :=
      hinf σ 1 τ τ (fun x hx => (mem_GQL.mp h x hx)) (fun _ _ => rfl)
    have e2 : ε 1 τ = ε 1 1 := by
      have := hc 1 1 τ
      simp only [one_mul] at this
      exact (mul_left_cancel this).symm
    rw [e1, e2, h11]
  · have e1 : ε σ τ = ε σ 1 :=
      hinf σ σ τ 1 (fun _ _ => rfl) (fun x hx => (mem_GQL.mp h x hx))
    have e2 : ε σ 1 = ε 1 1 := by
      have := hc σ 1 1
      simp only [mul_one] at this
      exact mul_right_cancel this
    rw [e1, e2, h11]

theorem orderOf_pos_dirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 < orderOf χ := by
  have h := orderOf_dvd_totient χ
  have hφ : 0 < Nat.totient N := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rcases Nat.eq_zero_or_pos (orderOf χ) with h0 | h0
  · rw [h0, zero_dvd_iff] at h; omega
  · exact h0

/-- **B3 over `G_ℚ`** (N5 L701-716). `η` is any continuous quadratic character (N5's twist
killing inertia outside `T`; take `η = 1` for the untwisted cochain): `β = β_{B2} · η`. -/
theorem b3_of_leaves (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
      (∀ σ k : GQ, k ∈ GQL L' → β (σ * k) = β σ) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  obtain ⟨N, hN, χ, β₁, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves hHasse hTwo hSq hUnr L ε hε hinf T hT hram
  -- the twist `β = β₁ η` (N5 L707-709; `η = 1` gives the untwisted cochain)
  let β : GQ → ℂˣ := fun x => β₁ x * η x
  have hβl : IsLocallyConstant β := hβl₁.mul hηl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ η hη
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ η
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  -- K' is open, hence closed
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  -- degree
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index
      (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨N, hN, χ, β, L', hsupp, hord, hβl, hβs, hβe, hle, hfd, hgal, hGL', ?_, ?_⟩
  · intro σ k hk
    exact cochain_mul_kernel hβ hεN σ (show k ∈ K' from (hGL' k).mp hk |> (mem_kernelSubgroup hβ
        hεN).mpr)
  · rw [hL', hL]; exact hidx

/-- **B3 with the constants** (N5 L713-716): `[L' : ℚ] ≤ Q_R · M_S(u)` when `[L:ℚ] ≤ D`,
`T = S ∪ supp M_S(u)` and `(S, R)` is admissible. -/
theorem b3_degree_le_QM (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ ramSet S u → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u := by
  have hT : ∀ p ∈ ramSet S u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β, L', _, hord, hβl, hβs, hβe, hle, hfd, hgal, hGL', _, hdeg⟩ :=
    b3_of_leaves hHasse hTwo hSq hUnr L ε hε hinf h11 (ramSet S u) hT hram η hη hηl
  refine ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd, hgal, hGL', ?_⟩
  have h := degree_le_QM S hS R hRD hRS hR12 u (Module.finrank ℚ L) (orderOf χ) hLD hord
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := h

end GlueDescent.B3Q

