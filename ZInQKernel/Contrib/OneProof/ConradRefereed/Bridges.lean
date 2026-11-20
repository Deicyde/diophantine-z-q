import ZInQKernel.Contrib.OneProof.C8ConradB
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.C8Twist

/-! For `diophantine_zq.tex` 760–764: convert the row's multiplicity to a pure
Hodge–Tate splitting, and an identity period after coefficient extension to the exact dimension
in the row. The intermediate Props below are proof interfaces, not printed inputs.
Provenance (c): coefficient and invariant-space comparisons. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Bridges

open Module
open scoped TensorProduct Topology Filter

set_option linter.style.longLine false
set_option linter.style.haveILetI false

variable (p : ℕ) [Fact p.Prime]

/-- The constant-weight splitting in the convention `wt(χ) = +1`.
The displayed equivariance on pure tensors extends by additivity. -/
def PureHT {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (i : ℤ) : Prop :=
  ∃ e : (ℂ_[p] ⊗[ℚ_[p]] (Fin 1 → E)) ≃ₗ[ℂ_[p]] (Fin (finrank ℚ_[p] E) → ℂ_[p]),
    ∀ (σ : PkgI4.GQp p) (a : ℂ_[p]) (v : Fin 1 → E) j,
      e ((PkgI4.cpAct p σ a) ⊗ₜ[ℚ_[p]]
          ((charRep ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v)) j =
        PkgI4.cycPow p σ i • PkgI4.cpAct p σ (e (a ⊗ₜ[ℚ_[p]] v) j)

private theorem cp_fixed {x : ℂ_[p]} (hx : ∀ σ : PkgI4.GQp p, PkgI4.cpAct p σ x = x) :
    ∃ q : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] q := by
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥
  obtain ⟨y, hy⟩ := _root_.ZInQ.Contrib.CloudB3W11.axSenTate_proof p K x (fun σ _ => hx σ)
  obtain ⟨q, hq⟩ := (IntermediateField.mem_bot.mp y.2)
  refine ⟨q, ?_⟩
  rw [hy, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], hq,
    ← PadicComplex.coe_eq]

/-- The constant weight case of Tate–Sen independence, on the *underlying*
`ℚ_p`-representation and for the full group. A minimal relation normalized at
one nonzero coefficient has invariant coefficients (Ax–Sen–Tate). -/
private theorem ht_independent {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (i : ℤ) {d : ℕ}
    (f : Fin d → PkgI4.htSpace p (charRep ψ) i) (hf : LinearIndependent ℚ_[p] f) :
    LinearIndependent ℂ_[p] (fun j => (f j).1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  suffices main : ∀ (s : Finset (Fin d)) (b : Fin d → ℂ_[p]),
      (∀ j ∉ s, b j = 0) → ∑ j, b j • (f j).1 = 0 → ∀ j, b j = 0 from
    fun b hb => main Finset.univ b (by simp) hb
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro b hs hb
    by_contra! hn
    obtain ⟨j₀, hj₀⟩ := hn
    have hj : j₀ ∈ s := by
      by_contra h
      exact hj₀ (hs j₀ h)
    let c : Fin d → ℂ_[p] := fun j => (b j₀)⁻¹ * b j
    have hc₀ : c j₀ = 1 := inv_mul_cancel₀ hj₀
    have hcs : ∀ j ∉ s, c j = 0 := fun j hj' => by simp [c, hs j hj']
    have hc : ∑ j, c j • (f j).1 = 0 := by
      simp only [c, mul_smul, ← Finset.smul_sum, hb, smul_zero]
    have hfσ (σ : PkgI4.GQp p) (j : Fin d) (v : Fin 1 → E) :
        (f j).1 ((charRep ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v) =
          PkgI4.cycPow p σ i • PkgI4.cpAct p σ ((f j).1 v) := (f j).2 σ v
    have fix (σ : PkgI4.GQp p) (j : Fin d) : c j = PkgI4.cpAct p σ (c j) := by
      let c' : Fin d → ℂ_[p] := fun k => c k - PkgI4.cpAct p σ (c k)
      have hconj : ∑ k, PkgI4.cpAct p σ (c k) • (f k).1 = 0 := by
        apply LinearMap.ext
        intro v
        let R := _root_.ZInQ.Contrib.G9.matRep p (charRep ψ)
        let u := R σ⁻¹ v
        have huv : R σ u = v := by
          dsimp only [u]
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        have h := congrArg (fun g : (Fin 1 → E) →ₗ[ℚ_[p]] ℂ_[p] => g u) hc
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul] at h ⊢
        have hσ : ∑ k, PkgI4.cpAct p σ (c k) * PkgI4.cpAct p σ ((f k).1 u) = 0 := by
          simpa only [map_sum, map_mul, map_zero] using congrArg (PkgI4.cpAct p σ) h
        have hv (k : Fin d) := hfσ σ k u
        change ∀ k, (f k).1 (R σ u) = _ at hv
        simp only [huv] at hv
        rw [← mul_zero (algebraMap ℚ_[p] ℂ_[p] (PkgI4.cycPow p σ i)), ← hσ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hv, Algebra.smul_def]; ring
      have hc' : ∑ k, c' k • (f k).1 = 0 := by
        simp only [c', sub_smul, Finset.sum_sub_distrib, hc, hconj, sub_zero]
      have hz := ih (s.erase j₀) (Finset.erase_ssubset hj) c' (fun k hk => by
        by_cases e : k = j₀
        · subst k
          simp [c', hc₀]
        · have hk' : k ∉ s := by simpa [Finset.mem_erase, e] using hk
          simp [c', hcs k hk']) hc' j
      exact sub_eq_zero.mp hz
    choose q hq using fun j => cp_fixed p (fun σ => (fix σ j).symm)
    have he : ∑ j, q j • f j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      simpa only [hq, algebraMap_smul] using hc
    have hz := Fintype.linearIndependent_iff.mp hf q he j₀
    simpa [hc₀, hz] using hq j₀

/-- Bridge (1): the singleton kernel predicate gives the underlying `ℚ_p`
Hodge–Tate splitting in Conrad's sign convention (C8, L758–761; App. B, p. 32 (UNVERIFIED)). -/
theorem pureHT_of_hasHTWeights {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (w : ℤ)
    (hw : PkgI4.HasHTWeights p (charRep ψ) {w}) : PureHT p ψ (-w) := by
  classical
  let V := Fin 1 → E
  haveI : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  haveI : Module.Free ℚ_[p] V := Module.Free.of_divisionRing _ _
  let d := finrank ℚ_[p] E
  have hd : 0 < d := finrank_pos_intermediateField p E
  have hq := hw w
  rw [Multiset.count_singleton_self] at hq
  change finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) (-w)) / d = 1 at hq
  have hle : d ≤ finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) (-w)) := by
    exact (Nat.le_div_iff_mul_le hd).mp (by omega) |>.trans_eq' (one_mul d)
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hle
  let T := ℂ_[p] ⊗[ℚ_[p]] V
  let F : Fin d → Module.Dual ℂ_[p] T := fun j => (f j).1.liftBaseChange ℂ_[p]
  have hF : LinearIndependent ℂ_[p] F :=
    (ht_independent p ψ (-w) f hf).map'
      (LinearMap.liftBaseChangeEquiv ℂ_[p]).toLinearMap
      (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))
  have hV : finrank ℚ_[p] V = d := by simp [V, d, Module.finrank_pi_fintype]
  let b := (Module.finBasis ℚ_[p] V).baseChange ℂ_[p]
  have hT : finrank ℂ_[p] T = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin, hV]
  let B := basisOfLinearIndependentOfCardEqFinrank' F hF (by simp [Subspace.dual_finrank_eq, hT])
  let L : T →ₗ[ℂ_[p]] (Fin d → ℂ_[p]) := LinearMap.pi F
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hz : ∀ j, F j x = 0 := fun j => congrFun (LinearMap.mem_ker.mp hx) j
    refine (Module.forall_dual_apply_eq_zero_iff ℂ_[p] x).mp (fun φ => ?_)
    rw [← B.sum_repr φ]
    simp [B, hz]
  let e := LinearEquiv.ofBijective L ⟨hL,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show finrank ℂ_[p] T = finrank ℂ_[p] (Fin d → ℂ_[p]) by
        rw [hT, Module.finrank_fin_fun])).mp hL⟩
  refine ⟨e, fun σ a v j => ?_⟩
  change PkgI4.cpAct p σ a • (f j).1 ((charRep ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v) =
    PkgI4.cycPow p σ (-w) • PkgI4.cpAct p σ (a • (f j).1 v)
  have hf' := (f j).2 σ v
  change (f j).1 ((charRep ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v) =
    PkgI4.cycPow p σ (-w) • PkgI4.cpAct p σ ((f j).1 v) at hf'
  rw [hf']
  simp only [smul_eq_mul, Algebra.smul_def, map_mul]
  ring

/-- Restriction `G_K → G_{ℚ_p}`, using the same algebraic closure
`PadicAlgCl p` for `K` and `ℚ_p`. Its image is the fixing subgroup of `K`. -/
def restrictGalois (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* PkgI4.GQp p :=
  K.fixingSubgroup.subtype.comp K.fixingSubgroupEquiv.symm.toMonoidHom

theorem range_restrictGalois (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (restrictGalois p K).range = K.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    exact (K.fixingSubgroupEquiv.symm g).2
  · intro hσ
    exact ⟨K.fixingSubgroupEquiv ⟨σ, hσ⟩, by simp [restrictGalois]⟩

/-- The identity coefficient line is `ℂ_p(i)` over `G_K`
(C8 at L763–764, Conrad App. B, p. 33 (UNVERIFIED)). An isomorphism of semilinear lines
is multiplication by a nonzero scalar `c` satisfying the displayed relation. -/
def IdentityLine (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ : PkgI4.GQp p →* Kˣ) (i : ℤ) : Prop :=
  ∃ c : ℂ_[p], c ≠ 0 ∧
    ∀ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
      let σ := restrictGalois p K g
      algebraMap K ℂ_[p] (ψ σ : K) * c = _root_.ZInQ.Contrib.G9.PkgI4.cycPow p σ i • _root_.ZInQ.Contrib.G9.PkgI4.cpAct p σ c

/-- The concrete near-1 display, Conrad App. B p. 33 (UNVERIFIED), local base `ℚ_p`.
The equality for `ψ ∘ r_L` is written on representatives of the arithmetic
Artin symbol in the topological abelianization. -/
def ArtinNearOne {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∀ᶠ x : ℚ_[p]ˣ in 𝓝 1, ∀ σ : PkgI4.GQp p, IsArtinLift p σ x →
    ((ψ σ : Eˣ) : E) = algebraMap ℚ_[p] E (x : ℚ_[p]) ^ (-n)

/-- Every arithmetic Artin symbol has a lift, so quantification over lifts in
the p. 33 (UNVERIFIED) formula does not discard any unit. -/
theorem exists_artinLift (x : ℚ_[p]ˣ) : ∃ σ : PkgI4.GQp p, IsArtinLift p σ x :=
  Quotient.exists_rep (TauCeti.ClassFieldTheory.artinMap ℚ_[p] x)

/-- Bridge (2), concrete version: the reductions modulo powers of `p` describe
the neighborhoods of 1 in the display. No Weil restriction is involved. -/
theorem artinNearOne_iff {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) :
    ArtinNearOne p ψ n ↔ IsLocallyAlgebraicConrad p ψ n := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hrpos : 0 < (p : ℝ)⁻¹ := by positivity
  have hnorm (u : ℤ_[p]ˣ) :
      ‖((unitsQp p u : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ = ‖(u : ℤ_[p]) - 1‖ := by
    rw [← PadicInt.norm_coe, PadicInt.coe_sub, PadicInt.coe_one]
    rfl
  have hred (k : ℕ) (u : ℤ_[p]ˣ) :
      ‖(u : ℤ_[p]) - 1‖ ≤ ((p : ℝ)⁻¹) ^ k ↔ PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
    have hh := PadicInt.norm_le_pow_iff_mem_span_pow ((u : ℤ_[p]) - 1) k
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hh
    simpa only [inv_pow, zpow_neg, zpow_natCast] using hh
  have hb := Units.isEmbedding_val₀.isInducing.nhds_eq_comap (1 : ℚ_[p]ˣ)
  constructor
  · intro h
    unfold ArtinNearOne at h
    rw [hb] at h
    obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp h
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hr
    refine ⟨k, fun u hu σ hσ => ?_⟩
    have hball' : ((unitsQp p u : ℚ_[p]ˣ) : ℚ_[p]) ∈ Metric.ball (1 : ℚ_[p]) ε := by
      rw [Metric.mem_ball, dist_eq_norm, hnorm]
      exact ((hred k u).mpr hu).trans_lt hk
    exact hsub (hball hball') σ hσ
  · rintro ⟨k, hk⟩
    unfold ArtinNearOne
    rw [hb]
    let ε : ℝ := ((p : ℝ)⁻¹) ^ k
    have hε : 0 < ε := pow_pos hrpos _
    have hε1 : ε ≤ 1 := pow_le_one₀ hrpos.le hr.le
    refine Filter.mem_comap.mpr ⟨Metric.ball 1 ε, Metric.ball_mem_nhds _ hε, ?_⟩
    intro x hx σ hσ
    have hx' : ‖(x : ℚ_[p]) - 1‖ < ε := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hx
    have hx1 : ‖(x : ℚ_[p])‖ = 1 :=
      (Padic.norm_eq_of_norm_sub_lt_right (by simpa using hx'.trans_le hε1)).trans (norm_one)
    let u : ℤ_[p]ˣ := PadicInt.mkUnits hx1
    have hu : unitsQp p u = x := Units.ext rfl
    have hku : PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
      apply (hred k u).mp
      rw [← hnorm, hu]
      exact hx'.le
    have hσ' : IsArtinLift p σ (unitsQp p u) := hu.symm ▸ hσ
    calc ((ψ σ : Eˣ) : E) = algebraMap ℚ_[p] E ((unitsQp p u : ℚ_[p]ˣ) : ℚ_[p]) ^ (-n) :=
           hk u hku σ hσ'
      _ = _ := by rw [hu]

/-- Intermediate implication: a pure Hodge–Tate splitting gives the near-one formula. -/
def ConradNearOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (i : ℤ),
    Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)) →
    PureHT p ψ i → ∃ n : ℤ, ArtinNearOne p ψ n

/-- Intermediate implication: the near-one formula gives an identity period over the field
used for the coefficient extension. -/
def ConradIdentityWeight : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ),
    Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)) →
    ArtinNearOne p ψ n → IdentityLine p K ψ n

section Extension

variable {E K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] K]
  (hEK : E ≤ K) (ψ : PkgI4.GQp p →* Eˣ)

private def extendChar : PkgI4.GQp p →* Kˣ :=
  (Units.map (IntermediateField.inclusion hEK).toRingHom.toMonoidHom).comp ψ

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] K] in
private theorem charRep_extend :
    charRep (extendChar p hEK ψ) =
      (Matrix.GeneralLinearGroup.map (IntermediateField.inclusion hEK).toRingHom).comp (charRep ψ) := by
  ext σ : 1
  apply Units.ext
  ext j k
  have hjk : j = k := Subsingleton.elim j k
  subst k
  simp [charRep, extendChar, Matrix.algebraMap_matrix_apply]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] K] in
private theorem extend_conradLA (n : ℤ) :
    IsLocallyAlgebraicConrad p (extendChar p hEK ψ) n ↔ IsLocallyAlgebraicConrad p ψ n := by
  have hpow (x : ℚ_[p]) :
      (IntermediateField.inclusion hEK) ((algebraMap ℚ_[p] E x) ^ (-n)) =
        (algebraMap ℚ_[p] K x) ^ (-n) := by
    rw [map_zpow₀, AlgHom.commutes]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun u hu σ hσ => (IntermediateField.inclusion hEK).injective ?_⟩
    change ((extendChar p hEK ψ σ : Kˣ) : K) =
      (IntermediateField.inclusion hEK) ((algebraMap ℚ_[p] E ((u : ℤ_[p]) : ℚ_[p])) ^ (-n))
    exact (hk u hu σ hσ).trans (hpow _).symm
  · rintro ⟨k, hk⟩
    refine ⟨k, fun u hu σ hσ => ?_⟩
    change (IntermediateField.inclusion hEK) ((ψ σ : Eˣ) : E) = _
    exact (congrArg (IntermediateField.inclusion hEK) (hk u hu σ hσ)).trans (hpow _)

end Extension

open _root_.ZInQ.Contrib.HodgeSplit
open _root_.ZInQ.Contrib.CloudB3W11 (axSenTate_proof tateTwistInvariants_proof)

/-- The identity line gives a vector of `Y_n(ψ)` over `K` (default-budget helper). -/
private theorem identityLine_mem_Ysp (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ) (c : ℂ_[p])
    (he : ∀ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
      let σ := restrictGalois p K g
      algebraMap K ℂ_[p] (ψ σ : K) * c = _root_.ZInQ.Contrib.G9.PkgI4.cycPow p σ n • _root_.ZInQ.Contrib.G9.PkgI4.cpAct p σ c) :
    (fun _ : Fin 1 => c) ∈ Ysp p (charRep ψ) n K := by
  intro σ hσ
  have hr : σ ∈ (restrictGalois p K).range := range_restrictGalois p K ▸ hσ
  obtain ⟨g, rfl⟩ := hr
  ext j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC, vAct,
    charRep, Matrix.algebraMap_matrix_apply] using he g

/-- `Y_n(ψ)` is finite-dimensional over `K` (default-budget helper). -/
private theorem finiteDimensional_Ysp_charRep (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ) :
    FiniteDimensional K (Ysp p (charRep ψ) n K) :=
  Ysp_finiteDimensional p tateTwistInvariants_proof axSenTate_proof K (charRep ψ) n

/-- A nonzero vector makes `Y_n(ψ)` nonzero (default-budget helper; the torsion-freeness
instance is named, not searched for). -/
private theorem finrank_Ysp_charRep_pos (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ) (c : ℂ_[p]) (hc : c ≠ 0)
    (hv : (fun _ : Fin 1 => c) ∈ Ysp p (charRep ψ) n K) :
    0 < finrank K (Ysp p (charRep ψ) n K) := by
  have := finiteDimensional_Ysp_charRep p K ψ n
  have : Module.IsTorsionFree K (Fin 1 → ℂ_[p]) := DivisionSemiring.to_moduleIsTorsionFree
  refine Submodule.one_le_finrank_iff.mpr fun h => hc ?_
  have h0 : (fun _ : Fin 1 => c) = 0 := (Submodule.mem_bot K).mp (h ▸ hv)
  exact congrFun h0 0

/-- From the identity line to the *exact* invariant-space dimension for
Galois coefficients. It gives a nonzero element in the weight space on
restriction; Tate–Sen bounds its dimension by 1, and TailT then gives the
dimension on the full Galois group. -/
theorem conradHTMult_of_identityLine (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ) (h : IdentityLine p K ψ n) :
    conradHTMult p (charRep ψ) n = finrank ℚ_[p] K := by
  obtain ⟨c, hc, he⟩ := h
  have hv := identityLine_mem_Ysp p K ψ n c he
  have hpos := finrank_Ysp_charRep_pos p K ψ n c hc hv
  have hle := TwistHT.finrank_Ysp_le p K (charRep ψ) n
  have hone : finrank K (Ysp p (charRep ψ) n K) = 1 := by omega
  have := finiteDimensional_Ysp_charRep p K ψ n
  have : Module.Free ℚ_[p] K := Module.Free.of_divisionRing _ _
  have : Module.Free K (Ysp p (charRep ψ) n K) := Module.Free.of_divisionRing _ _
  change finrank ℚ_[p] (PkgI4.htSpace p (charRep ψ) n) = _
  rw [show PkgI4.htSpace p (charRep ψ) n = _root_.ZInQ.Contrib.G9.PkgI4.htSpace p (charRep ψ) n from rfl,
    finrank_htSpace_eq_Ysp p K tateTwistInvariants_proof axSenTate_proof,
    ← Module.finrank_mul_finrank ℚ_[p] K (Ysp p (charRep ψ) n K), hone, mul_one]

/-- C8: the original p. 32 (UNVERIFIED) hypothesis follows using the concrete p. 33 (UNVERIFIED) formula,
with the old sign translation. The normal closure is only a coefficient
enlargement; the local base stays `ℚ_p`. -/
theorem conradAppBQp_of_nearOne (h : ConradNearOne) : ConradAppBQp := by
  intro p _ E _ ψ hc hHT
  obtain ⟨w, hw⟩ := hHT
  let K := IntermediateField.normalClosure ℚ_[p] E (PadicAlgCl p)
  letI : FiniteDimensional ℚ_[p] K := normalClosure.is_finiteDimensional ℚ_[p] E (PadicAlgCl p)
  letI : IsGalois ℚ_[p] K := IsGalois.normalClosure ℚ_[p] E (PadicAlgCl p)
  have hEK : E ≤ K := IntermediateField.le_normalClosure E
  letI : Algebra E K := (IntermediateField.inclusion hEK).toRingHom.toAlgebra
  letI : IsScalarTower ℚ_[p] E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ_[p] E K
  letI : Module.Free E K := Module.Free.of_divisionRing _ _
  let ψK := extendChar p hEK ψ
  have hmap : charRep ψK = (Matrix.GeneralLinearGroup.map (algebraMap E K)).comp (charRep ψ) :=
    charRep_extend p hEK ψ
  have hHTK : PkgI4.HasHTWeights p (charRep ψK) {w} := by
    intro i
    rw [hmap, htMult_extend (Module.finBasis E K)]
    exact hw i
  obtain ⟨n, hn⟩ := h p K ψK (-w) hc (pureHT_of_hasHTWeights p ψK w hHTK)
  exact ⟨-n, (isLocallyAlgebraic_iff_conrad p ψ (-n)).mpr (by
    simpa only [neg_neg] using (extend_conradLA p hEK ψ n).mp ((artinNearOne_iff p ψK n).mp hn))⟩

/-- C8: B.3 gives the old numerical equality, after cancelling the
degree of the coefficient enlargement. No Hodge–Tate hypothesis is added. -/
theorem conradPropB3Qp_of_identityWeight (h : ConradIdentityWeight) : ConradPropB3Qp := by
  intro p _ E _ ψ n hc hn
  let K := IntermediateField.normalClosure ℚ_[p] E (PadicAlgCl p)
  letI : FiniteDimensional ℚ_[p] K := normalClosure.is_finiteDimensional ℚ_[p] E (PadicAlgCl p)
  letI : IsGalois ℚ_[p] K := IsGalois.normalClosure ℚ_[p] E (PadicAlgCl p)
  have hEK : E ≤ K := IntermediateField.le_normalClosure E
  letI : Algebra E K := (IntermediateField.inclusion hEK).toRingHom.toAlgebra
  letI : IsScalarTower ℚ_[p] E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ_[p] E K
  letI : Module.Free E K := Module.Free.of_divisionRing _ _
  let ψK := extendChar p hEK ψ
  have he := conradHTMult_of_identityLine p K ψK n (h p K ψK n hc ((artinNearOne_iff p ψK n).mpr ((extend_conradLA p hEK ψ n).mpr hn)))
  have hmap : charRep ψK = (Matrix.GeneralLinearGroup.map (algebraMap E K)).comp (charRep ψ) :=
    charRep_extend p hEK ψ
  change finrank ℚ_[p] (PkgI4.htSpace p (charRep ψK) n) = _ at he
  let i := finrank E K
  letI : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  letI : Module.Free ℚ_[p] K := Module.Free.of_divisionRing _ _
  letI : Module.Free ℚ_[p] (PkgI4.htSpace p (charRep ψ) n) := Module.Free.of_divisionRing _ _
  rw [hmap, (htSpaceExtendEquiv (Module.finBasis E K) (charRep ψ) n).finrank_eq,
    ← (Finsupp.linearEquivFunOnFinite ℚ_[p] (PkgI4.htSpace p (charRep ψ) n) (Fin i)).finrank_eq,
    Module.finrank_finsupp, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ_[p] E K,
    mul_comm (finrank ℚ_[p] E)] at he
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := E) (M := K)) he

#print axioms cp_fixed
#print axioms ht_independent
#print axioms pureHT_of_hasHTWeights
#print axioms range_restrictGalois
#print axioms exists_artinLift
#print axioms artinNearOne_iff
#print axioms charRep_extend
#print axioms extend_conradLA
#print axioms identityLine_mem_Ysp
#print axioms finiteDimensional_Ysp_charRep
#print axioms finrank_Ysp_charRep_pos
#print axioms conradHTMult_of_identityLine
#print axioms conradAppBQp_of_nearOne
#print axioms conradPropB3Qp_of_identityWeight

end HDec.G0Galois.C8Conrad.Bridges
