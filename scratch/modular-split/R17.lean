import ZInQKernel.OneProof.H.TailT
import ZInQKernel.HDecomp.Conductor.LadicCond

/-! # modular-split, row r17: `LadicCond.CarayolR17'` reduced to Carayol's theorem at one realization

The row (bundle field `r17 : _root_.LadicCond.CarayolR17'`, `ZInQKernel/HDecomp/Conductor/LadicCond.lean`) is
imported, not copied. It quantifies over **every** semisimple `ρ` attached to the newform `f` (trace form of
`PkgI4.GaloisRep.AttachedTo`). Carayol's Théorème (A) is about one representation, his `σ_λ(π_f)` (the
realization in the étale cohomology of a Shimura curve). The transport from that realization to every
semisimple attached `ρ` is proved here: two semisimple attached representations are conjugate
(`attachedConj_proof`: Chebotarev T18 + Brauer–Nesbitt T19, kernel), and the Serre–Tate conductor exponent
`condExp` is invariant under conjugation (`condExp_conj`, new, proved). What is left is the leaf
`CarayolRealization` below. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace ModularSplit.R17

open LadicCond

section Conj

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] {n : ℕ}

/-- `v ↦ P v` as a linear automorphism of `kⁿ`. -/
def glEquiv (P : GL (Fin n) k) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinear (Matrix.toLin' (P : Matrix (Fin n) (Fin n) k))
    (Matrix.toLin' ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem glEquiv_apply (P : GL (Fin n) k) (v : Fin n → k) :
    glEquiv P v = (P : Matrix (Fin n) (Fin n) k).mulVec v := rfl

/-- Invariants of a conjugate: `V^S(PρP⁻¹) = P · V^S(ρ)`. -/
theorem invariants_conj (ρ ρ' : PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) (S : Set (PkgI4.GQp p)) :
    invariants ρ' S = (invariants ρ S).map (glEquiv P : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  have hPinv : ∀ w : Fin n → k, (P : Matrix (Fin n) (Fin n) k).mulVec
      (((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPinv' : ∀ w : Fin n → k, ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec
      ((P : Matrix (Fin n) (Fin n) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hval : ∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) k) = (P : Matrix (Fin n) (Fin n) k) *
      (ρ σ : Matrix (Fin n) (Fin n) k) * ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    intro σ; rw [h σ]; rfl
  ext v
  constructor
  · intro hv
    refine ⟨((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, ?_, ?_⟩
    · intro σ hσ
      have := hv σ hσ
      rw [hval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this
      have h2 := congrArg (((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec) this
      rwa [hPinv'] at h2
    · exact hPinv v
  · rintro ⟨w, hw, rfl⟩ σ hσ
    change (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec w) =
      (P : Matrix (Fin n) (Fin n) k).mulVec w
    rw [hval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPinv', hw σ hσ]

theorem codimInv_conj (ρ ρ' : PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) (S : Set (PkgI4.GQp p)) : codimInv ρ' S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_conj ρ ρ' P h S, LinearEquiv.finrank_map_eq]

theorem isAdapted_conj (ρ ρ' : PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) (L : Fld p) : IsAdapted L ρ' ↔ IsAdapted L ρ := by
  unfold IsAdapted
  have : ∀ σ, ρ' σ = 1 ↔ ρ σ = 1 := by
    intro σ; rw [h σ]
    constructor
    · intro h1
      have : ρ σ = P⁻¹ * (P * ρ σ * P⁻¹) * P := by group
      rw [this, h1]; group
    · intro h1; rw [h1]; group
  simp only [this]

theorem choose_congr {α : Sort*} {q r : α → Prop} (hqr : q = r) (hq : ∃ x, q x) (hr : ∃ x, r x) :
    hq.choose = hr.choose := by
  subst hqr; rfl

theorem swan_conj (ρ ρ' : PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) : swan ρ' = swan ρ := by
  have hsw : ∀ L, swanAt L ρ' = swanAt L ρ := by
    intro L; unfold swanAt; simp only [codimInv_conj ρ ρ' P h]
  have hpred : (fun L => IsAdapted L ρ') = (fun L => IsAdapted L ρ) :=
    funext fun L => propext (isAdapted_conj ρ ρ' P h L)
  unfold swan
  by_cases hex : ∃ L, IsAdapted L ρ
  · have hex' : ∃ L, IsAdapted L ρ' := by
      obtain ⟨L, hL⟩ := hex; exact ⟨L, (isAdapted_conj ρ ρ' P h L).mpr hL⟩
    rw [dif_pos hex, dif_pos hex', hsw, choose_congr hpred hex' hex]
  · have hex' : ¬ ∃ L, IsAdapted L ρ' := by
      rintro ⟨L, hL⟩; exact hex ⟨L, (isAdapted_conj ρ ρ' P h L).mp hL⟩
    rw [dif_neg hex, dif_neg hex']

/-- **GLUE, proved: the conductor exponent is invariant under conjugation.** -/
theorem condExp_conj (ρ ρ' : PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) : condExp ρ' = condExp ρ := by
  unfold condExp
  rw [codimInv_conj ρ ρ' P h, swan_conj ρ ρ' P h]

end Conj

/-- **LEAF candidate (consequence, see the report): Carayol's Théorème (A) at his realization.**
For a newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ`, a prime `ℓ` and embeddings `ιC : ℚ̄ → ℂ`,
`ιL : ℚ̄ → ℚ̄_ℓ`, **there is** a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `f` (arithmetic
Frobenius at `p ∤ Nℓ` has trace `ιL ιC⁻¹ a_p(f)`) whose conductor exponent at every prime `p ≠ ℓ` is
`v_p(N)`.

Source: Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert*,
Ann. Sci. ÉNS (4) 19 (1986), Théorème (A), pp. 409–411, and §0.8 p. 411 (read by the locator audit,
`docs/research/locators.md` row R17: every finite `p` and every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`), at
`F = ℚ`, weight 2: `σ_λ(π_f)|_{G_{ℚ_p}}` corresponds to `π_{f,p}` under the local Langlands
correspondence, so its conductor is `a(π_{f,p})`; with Casselman 1973 (`a(π_{f,p}) = v_p(N)` for a
newform; UNVERIFIED locator) this gives `v_p(N)`. The witness is `σ_λ(π_f)` with coefficients extended to
`ℚ̄_ℓ` along `ιL ιC⁻¹` (or its contragredient, if Carayol's normalization uses geometric Frobenius: the
conductor is unchanged by duals, audit row R17), which is irreducible (Ribet 1977, UNVERIFIED locator), hence
semisimple. Not stronger than the published statements: it asserts the conclusion for one realization only. -/
def CarayolRealization : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2), 0 < N → PkgI4.IsNewform f χ →
    ∃ ρ : PkgI4.GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ → condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- **Row r17 (`LadicCond.CarayolR17'`) from `CarayolRealization`.** -/
theorem carayolR17'_of_realization (hC : CarayolRealization) : CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hss hatt hpl
  obtain ⟨ρ0, hss0, hatt0, hcond0⟩ := hC ℓ ιC ιL N χ f hN hf
  let r0 : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2 := ⟨ρ0.toHom, ρ0.continuous_toHom⟩
  let r : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2 := ⟨ρ.toHom, ρ.continuous_toHom⟩
  have hconj : ZInQ.Contrib.HodgeSplit.IsConj r0 r := by
    refine ZInQ.Contrib.HodgeSplit.attachedConj_proof ℓ r0 r (N * ℓ).primeFactors hss0 hss
      fun q hq hqS => ?_
    have hqN : ¬ q ∣ N * ℓ := by
      intro h
      exact hqS (Nat.mem_primeFactors.mpr ⟨hq, h, Nat.mul_ne_zero (by omega)
        (Fact.out : ℓ.Prime).ne_zero⟩)
    obtain ⟨hu0, α0, hα0, htr0⟩ := hatt0 q hq hqN
    obtain ⟨hu, α, hα, htr⟩ := hatt q hq hqN
    have heq : α0 = α := by
      apply ιC.toRingHom.injective
      change ιC α0 = ιC α
      rw [hα0, hα]
    refine ⟨hu0, hu, fun v σ hv hσ => ?_⟩
    rw [show (r0.mat σ).trace = (ρ0.mat σ).trace from rfl, htr0 v σ hv hσ,
      show (r.mat σ).trace = (ρ.mat σ).trace from rfl, htr v σ hv hσ, heq]
  obtain ⟨P, hP⟩ := hconj
  rw [← hcond0 p hpl]
  exact (condExp_conj (ρ.restrictLocal p) (ρ0.restrictLocal p) P fun σ => hP _).symm

end ModularSplit.R17

#print axioms ModularSplit.R17.carayolR17'_of_realization
