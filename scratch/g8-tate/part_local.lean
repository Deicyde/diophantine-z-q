/-! # g8-tate, part 2: g8-object's `LocalDataS` proved from the leaves R6, I2-Tors and `UnramRoots`

`G8Object.LocalDataS p L A ℓ β` (g8-object, `part_split.lean`) is G15's local data on `G7Data`'s
objects: a finite Galois `F ⊆ ℚ̄_p` with `e(F) ≤ (DG₀)!` (`p ≤ D`), resp. `p ∤ e(F)` (`p > D`),
containing `L` (`ContainsL`), on which wild inertia acts trivially on `V_ℓ(A)` for the model
`A/L` (`WildTateTrivial`), and on which `β` dies above `U₀` (`BetaUpperC`), resp. on wild inertia
(`BetaTameC`).

`localDataS_of_g7Data` proves it for every `G7Data` with `[L:ℚ] ≤ D` and `dim A = 2`, `p ≠ ℓ`, from
* `ObjBridge.RaynaudCriterion` (R6) and `ObjBridge.TorsionStructure` (I2-Tors), leaves in the
  bundles;
* `G15Ram.UnramRoots 2 ℓ` (local-glue's textbook Prop, unramified fourth roots), at `p = 2` only.

It reuses local-glue's `torsFixWildOdd_of_descent` (R6 + D2 on the torsion field `L_v(A[q])`),
`tateWildK_of_R6`, `betaUpper_of_twist`, `betaTwist2_of_unramRoots`, local-data's
`beta_wild_of_clauses`, `exists_finGal_ramCard_le`, and part 1's `ℂ ≃+* ℚ̄_ℓ` and tame closure.
`DescentPts A L` holds trivially here (`descentPts_self`): `A` is already the model over `L`. -/

noncomputable section

namespace G8Tate

open PkgI4 (GQ GQp decomp)
open LadicCond G0ModField
open ZInQ LeafQM.AV GlueDescent.B2
open CategoryTheory MonObj

/-- `T u` consists of primes (the argument inside g0-mod-field's `g7OutUnr_of_g4Out`). -/
theorem T_prime (u : ℚ) : ∀ q ∈ T u, q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- **`G7Data`'s cochain clauses, transported to `ℚ̄_ℓ` along a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ`,
are local-data's `G7Clauses` (proved).** -/
theorem g7Clauses_of_g7Data {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) :
    G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L := by
  obtain ⟨-, hDD, -, -, ⟨Tm, hTmT, hN⟩, hβlc, hβsq, hβε, -⟩ := h
  refine ⟨inferInstance, hLD, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    have := congrArg (fun z : ℂˣ => Φ (z : ℂ)) (hβε g h)
    simp only [Units.val_mul, map_mul] at this
    exact this
  · intro g
    exact (map_ne_zero Φ).mpr (Units.ne_zero _)
  · exact hβlc.comp (fun z : ℂˣ => Φ (z : ℂ))
  · have hT : ∀ q ∈ Tm, q.Prime := fun q hq => T_prime u q (hTmT hq)
    subst hN
    refine ⟨Tm, hT, inferInstance, χ, Units.map Φ.toRingHom.toMonoidHom, fun g => ?_⟩
    show Φ (β g : ℂ) ^ 2 = Φ ((GlueDescent.B2Q.galChar χ g : ℂˣ) : ℂ)
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hβsq g]
  · intro g h hg _
    obtain ⟨hε, hinf, h11, -⟩ := hDD
    have h1 := GlueDescent.B3Q.inflatedNormalized_of L ε hε hinf h11 g h
      (Or.inl (GlueDescent.B3Q.mem_GQL.mpr hg))
    show Φ (ε g h : ℂ) = 1
    rw [h1, Units.val_one, map_one]

/-- **`DescentPts A L` for a model `A` over `L` itself (proved):** `A₀ = A`, `φ = id`
(`resQ L` is injective, `resQ_injective'`). -/
theorem descentPts_self {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (hdim : A.dim = 2) :
    @G15Ram.DescentPts L _ (numberField_of_fd L) A L _ := by
  letI : NumberField L := numberField_of_fd L
  refine ⟨inferInstance, A, MulEquiv.refl _, hdim, fun σ₀ σ' hσ P => ?_⟩
  rw [G15Ram.resQ_injective' hσ]
  rfl

/-- `F ⊇ L_v` gives `ContainsL p L F` with `j = embP` (proved). -/
theorem containsL_of_Lv {p : ℕ} [Fact p.Prime] {L : IF} {F : Fld p}
    (h : G15Ram.Lv (p := p) L ≤ F) : G8Object.ContainsL p L F :=
  ⟨G15Ram.embP, fun σ x => G15Ram.decomp_spec σ x, fun _ hx => h (G15Ram.embP_mem_Lv hx)⟩

/-- **g8-object's `LocalDataS` on every G7 datum with `[L:ℚ] ≤ D`, `dim A = 2`, `p ≠ ℓ` (proved)**
from the leaves R6 and I2-Tors and, at `p = 2`, local-glue's textbook Prop `UnramRoots`.
* `p ≤ D`: `E = L_v(A[q])`-type field of `torsFixWildOdd_of_descent` (`q = 3`, or `5` if `p = 3`;
  `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p] ≤ DG₀`), `F` its Galois closure (`e(F) ≤ (DG₀)!`). `WildTateTrivial` from
  the torsion statement (`tate_eq_one_of_torsFix`); `BetaUpperC` at odd `p` because upper groups
  are wild (`upperWild`) and `β` kills wild inertia of `G_{L_v}` (`beta_wild_of_clauses`), at
  `p = 2` by `betaUpper_of_twist` (degree `≤ 4` twist field from `UnramRoots`).
* `p > D` (so `p ≥ 7`): `F` the Galois closure of `L_v`, tame since `[L_v:ℚ_p] ≤ D < p`
  (`exists_finGal_tame`); `WildTateTrivial` from `tateWildK_of_R6`, `BetaTameC` from
  `beta_wild_of_clauses`. -/
theorem localDataS_of_g7Data (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : p = 2 → G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (hdim : A.dim = 2) :
    G8Object.LocalDataS p L A ℓ β := by
  obtain ⟨Φ⟩ := exists_complex_equiv ℓ
  have hC := g7Clauses_of_g7Data Φ h hLD
  have hβ1 : ∀ g, Φ (β g : ℂ) = 1 → β g = 1 := fun g hg =>
    Units.ext (Φ.injective (by rw [hg, Units.val_one, map_one]))
  letI : NumberField L := numberField_of_fd L
  have hD := descentPts_self A hdim
  obtain ⟨hLvfd, hLvD⟩ := G15Ram.Lv_fin (p := p) L
  haveI := hLvfd
  have hU0 : (0 : ℝ) ≤ G0ModNewform.U0 := by unfold G0ModNewform.U0; positivity
  refine ⟨fun hpD => ?_, fun hpD => ?_⟩
  · obtain ⟨E, hEfd, hLvE, hEdeg, hfix⟩ :=
      G15Ram.torsFixWildOdd_of_descent hR6 hTors hD (Ne.symm hpℓ)
    haveI := hEfd
    have hEn : Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 := by
      calc Module.finrank ℚ_[p] E
          ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (G15Ram.Lv (p := p) L) := hEdeg
        _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul_left _ (hLvD.trans hLD)
        _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
    obtain ⟨F, hF, hEF, he⟩ := G15Ram.exists_finGal_ramCard_le hEn
    refine ⟨F, hF, he, containsL_of_Lv (hLvE.trans hEF), ?_, ?_⟩
    · intro σ hσ σL hσL
      exact G15Ram.tate_eq_one_of_torsFix A ℓ σL (fun n Q hQ =>
        hfix σ ⟨fun x hx => hσ.1 x (hEF hx), hσ.2⟩ σL hσL n Q hQ)
    · have hBU : G15Ram.BetaUpper (fun g => Φ (β g : ℂ)) (G15Ram.Lv (p := p) L)
          G0ModNewform.U0 := by
        by_cases hp2 : p = 2
        · exact G15Ram.betaUpper_of_twist hC
            (G15Ram.betaTwist2_of_unramRoots hp2 hC (hU hp2))
        · intro t ht σ hσ
          have hwild := G15Ram.upperWild (p := p) t (lt_of_le_of_lt hU0 ht) hσ.1
          exact G15Ram.beta_wild_of_clauses hp2 hC hwild (G15Ram.fixSet_Lv_iff.mp hσ.2)
      intro t ht σ hσ
      exact hβ1 _ (G15Ram.betaUpper_mono (hLvE.trans hEF) hBU t ht σ hσ)
  · have hpD' : ZInQ.heightD < p := by exact_mod_cast hpD
    have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    have h7 : 7 ≤ p := by omega
    have hp2 : p ≠ 2 := by omega
    have hlt : Module.finrank ℚ_[p] (G15Ram.Lv (p := p) L) < p :=
      lt_of_le_of_lt (hLvD.trans hLD) hpD'
    obtain ⟨F, hF, hLvF, htame⟩ := exists_finGal_tame hlt
    refine ⟨F, hF, htame, containsL_of_Lv hLvF, ?_, ?_⟩
    · intro σ hσ σL hσL
      exact G15Ram.tateWildK_of_R6 hR6 hTors hdim (Ne.symm hpℓ) h7 σ hσ.2 σL hσL
    · intro σ hσ
      exact hβ1 _ (G15Ram.beta_wild_of_clauses hp2 hC hσ.2
        (G15Ram.fixSet_Lv_iff.mp (fun x hx => hσ.1 x (hLvF hx))))

end G8Tate

end

#print axioms G8Tate.g7Clauses_of_g7Data
#print axioms G8Tate.descentPts_self
#print axioms G8Tate.localDataS_of_g7Data
