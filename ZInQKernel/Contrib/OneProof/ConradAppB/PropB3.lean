import ZInQKernel.Contrib.OneProof.ConradAppB.Defs
import ZInQKernel.Contrib.OneProof.ConradBridges
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic

/-!
# Conrad's Proposition B.3 over `ℚ_p` from two inputs on characters of `G_{ℚ_p}`

B. Conrad, *Lifting global representations with local properties*, preprint (2011), App. B,
Prop. B.3 (p. 33), for the base field `ℚ_p` (`HDec.G0Galois.C8Conrad.ConradPropB3Qp`): if a
continuous character `ψ : G_{ℚ_p} → E^×` (`E/ℚ_p` finite inside `ℚ̄_p`) satisfies
`ψ(Art(u)) = u^{-n}` for the units `u ≡ 1 (mod p^k)` (arithmetic Artin map), then every
Hodge–Tate weight of the underlying `ℚ_p`-representation is `n` (Conrad's sign: `χ_cyc` has
weight `+1`), i.e. `dim_{ℚ_p} H_n(ψ) = [E : ℚ_p]`.

The two inputs, stated verbatim below and used as hypotheses:

* `UnramifiedCyclotomicSplitting`: a continuous character `χ : G_{ℚ_p} → L^×` (`L/ℚ_p` finite
  inside `ℚ̄_p`) is a product `μ η` of a continuous character `μ` trivial on inertia and a
  character `η` trivial on the kernel of the cyclotomic character.
* `UnramifiedPeriod`: a continuous unramified character `μ : G_{ℚ_p} → L^×` has a nonzero period
  `u ∈ ℂ_p` over `G_L`: `σ(u) = μ(σ) u` for every `σ ∈ G_L`.

Proof. Let `K ⊆ ℚ̄_p` be a finite Galois extension of `ℚ_p` containing `E` and a primitive
`p^k`-th root of unity `ζ`, and `ψ_K` the character `ψ` with values in `K`.

1. Split `ψ_K = μ η`: `μ` continuous and trivial on inertia, `η` trivial on `ker χ_cyc`.
2. `η = χ_cyc^n` on `G_K` (`eta_eq_cycPow`). Let `σ ∈ G_K`; then `σ ζ = ζ`, so
   `χ(σ) ≡ 1 (mod p^k)`. By local class field theory the classes of the inertia elements in
   `G_{ℚ_p}^{ab}` are the Artin symbols of the units (`exists_inertia_isArtinLift`), so some
   inertia element `σ'` is an Artin lift of `u = χ(σ)^{-1}`; then `χ(σ') = u^{-1} = χ(σ)`,
   `μ(σ') = 1` and `η(σ') = ψ(σ') = u^{-n} = χ(σ)^n`, while `η(σ) = η(σ')` since
   `σ'^{-1} σ ∈ ker χ`.
3. A nonzero period `c` of `μ` over `G_K` then satisfies `ψ(σ) c = χ(σ)^n σ(c)` for `σ ∈ G_K`
   (`identityLine_of_period`): the identity line of weight `n`. Its dimension count over `G_K`
   (Tate–Sen independence, Ax–Sen–Tate and Galois descent, `conradHTMult_of_identityLine`) gives
   `dim_{ℚ_p} H_n(ψ_K) = [K : ℚ_p]`, and `H_n(ψ_K) ≅ H_n(ψ)^{[K:E]}` gives
   `dim_{ℚ_p} H_n(ψ) = [E : ℚ_p]`.
-/

set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.SenWeightZero


open Module
open HDec.G0Galois.C8Conrad HDec.G0Galois.C8Conrad.Bridges

/-! ## Inertia, Artin lifts and the cyclotomic character -/

section Lemmas

variable (p : ℕ) [Fact p.Prime]

/-- A unit of `ℤ_p` is a unit of the valuation ring of `ℚ_p`: it lies in `U(ℚ_p, 0)`. -/
theorem unitsQp_mem_unitFiltration_zero (u : ℤ_[p]ˣ) :
    unitsQp p u ∈ TauCeti.unitFiltration ℚ_[p] 0 := by
  rw [TauCeti.mem_unitFiltration_iff_exists]
  refine ⟨Units.map (Padic.integerRingEquiv p).symm.toRingHom.toMonoidHom u, ?_, rfl⟩
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- **Every unit of `ℤ_p` has an Artin lift in the inertia group** (local class field theory:
the classes in `G_{ℚ_p}^{ab}` of the inertia elements are the Artin symbols of the units). -/
theorem exists_inertia_isArtinLift (u : ℤ_[p]ˣ) :
    ∃ σ : HDec.PkgI4.GQp p, IsInertia p σ ∧ IsArtinLift p σ (unitsQp p u) := by
  have hmem : TauCeti.ClassFieldTheory.artinMap ℚ_[p] (unitsQp p u) ∈
      (TauCeti.inertiaSubgroup ℚ_[p]).map (QuotientGroup.mk' _) := by
    rw [← TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero]
    exact ⟨_, unitsQp_mem_unitFiltration_zero p u, rfl⟩
  obtain ⟨σ, hσ, hσu⟩ := hmem
  exact ⟨σ, hσ, hσu⟩

/-- If `χ(σ) = u⁻¹` then `χ(σ)^i = u^{-i}` in `ℚ_p`. -/
theorem cycPow_eq_of_cyc_eq (σ : HDec.PkgI4.GQp p) (u : ℤ_[p]ˣ)
    (hcyc : ZInQ.Contrib.G9.PkgI4.cyc p σ = u⁻¹) (i : ℤ) :
    ZInQ.Contrib.G9.PkgI4.cycPow p σ i = ((u : ℤ_[p]) : ℚ_[p]) ^ (-i) := by
  rw [ZInQ.Contrib.G9.PkgI4.cycPow, hcyc]
  change ((Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom (u⁻¹ ^ i) : ℚ_[p]ˣ) :
    ℚ_[p]) = _
  rw [map_zpow, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow']
  rfl

/-- **`η = χ^n` on the subgroup fixing `μ_{p^k}`.** Let `η` be trivial on `ker χ_cyc` and equal to
`u^{-n}` on the inertia Artin lifts of the units `u ≡ 1 (mod p^k)`. Then `η(σ) = χ(σ)^n` for every
`σ` fixing a primitive `p^k`-th root of unity. -/
theorem eta_eq_cycPow {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (η : HDec.PkgI4.GQp p →* Lˣ)
    (k : ℕ) (n : ℤ)
    (hker : ∀ σ : HDec.PkgI4.GQp p, cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 → η σ = 1)
    (hI : ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : HDec.PkgI4.GQp p, IsInertia p σ →
      IsArtinLift p σ (unitsQp p u) →
        ((η σ : Lˣ) : L) = algebraMap ℚ_[p] L ((u : ℤ_[p]) : ℚ_[p]) ^ (-n))
    (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ (p ^ k)) (σ : HDec.PkgI4.GQp p) (hσ : σ ζ = ζ) :
    ((η σ : Lˣ) : L) = algebraMap ℚ_[p] L (ZInQ.Contrib.G9.PkgI4.cycPow p σ n) := by
  have h1 : PadicInt.toZModPow k ((ZInQ.Contrib.G9.PkgI4.cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) = 1 :=
    toZModPow_cyc_eq_one p k ζ hζ σ hσ
  set u : ℤ_[p]ˣ := (ZInQ.Contrib.G9.PkgI4.cyc p σ)⁻¹ with hu_def
  have hu : PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
    have h3 : PadicInt.toZModPow k (u : ℤ_[p]) *
        PadicInt.toZModPow k ((ZInQ.Contrib.G9.PkgI4.cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
      rw [← map_mul, ← Units.val_mul, hu_def, inv_mul_cancel, Units.val_one, map_one]
    rwa [h1, mul_one] at h3
  have hcyc : ZInQ.Contrib.G9.PkgI4.cyc p σ = u⁻¹ := by rw [hu_def, inv_inv]
  obtain ⟨σ', hσ'I, hσ'⟩ := exists_inertia_isArtinLift p u
  have hcyc' : ZInQ.Contrib.G9.PkgI4.cyc p σ' = ZInQ.Contrib.G9.PkgI4.cyc p σ := by
    rw [hcyc]
    exact cyc_of_isArtinLift p σ' u hσ'
  have hker' : η (σ'⁻¹ * σ) = 1 := by
    apply hker
    change ZInQ.Contrib.G9.PkgI4.cyc p (σ'⁻¹ * σ) = 1
    have e : ∀ τ : HDec.PkgI4.GQp p, ZInQ.Contrib.G9.PkgI4.cyc p τ =
        (cyclotomicCharacter (PadicAlgCl p) p).comp (ZInQ.Contrib.G9.PkgI4.toRingEquivHom p) τ :=
      fun _ => rfl
    rw [e, map_mul, map_inv, ← e, ← e, hcyc', inv_mul_cancel]
  have hησ : η σ = η σ' := by
    calc η σ = η (σ' * (σ'⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = η σ' * η (σ'⁻¹ * σ) := map_mul η _ _
      _ = η σ' := by rw [hker', mul_one]
  rw [hησ, hI u hu σ' hσ'I hσ', ← map_zpow₀, cycPow_eq_of_cyc_eq p σ u hcyc n]

/-- **The identity line from a period.** If `c ≠ 0` is a period of `μ` over `G_K` and
`ψ = μ χ^n` on `G_K`, then `c` spans the identity line of weight `n` of `ψ`:
`ψ(σ) c = χ(σ)^n σ(c)` for `σ ∈ G_K`. -/
theorem identityLine_of_period (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ μ : HDec.PkgI4.GQp p →* Kˣ) (n : ℤ) (c : ℂ_[p]) (hc0 : c ≠ 0)
    (hc : ∀ σ ∈ K.fixingSubgroup, σ • c = cpVal p (μ σ) * c)
    (hψ : ∀ σ ∈ K.fixingSubgroup, ((ψ σ : Kˣ) : K) =
      ((μ σ : Kˣ) : K) * algebraMap ℚ_[p] K (ZInQ.Contrib.G9.PkgI4.cycPow p σ n)) :
    IdentityLine p K ψ n := by
  refine ⟨c, hc0, fun g => ?_⟩
  intro σ
  have hσ : σ ∈ K.fixingSubgroup := (K.fixingSubgroupEquiv.symm g).2
  have hact : ZInQ.Contrib.G9.PkgI4.cpAct p σ c = algebraMap K ℂ_[p] ((μ σ : Kˣ) : K) * c := by
    rw [← ZInQ.Contrib.CloudB3W11AxCompletion.galois_smul_eq_cpAct]
    exact (hc σ hσ).trans rfl
  have hq : ∀ x : ℚ_[p], algebraMap K ℂ_[p] (algebraMap ℚ_[p] K x) = algebraMap ℚ_[p] ℂ_[p] x := by
    intro x
    rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p],
      IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
    rfl
  rw [hact, hψ σ hσ, map_mul, hq, Algebra.smul_def]
  ring

end Lemmas

/-! ## Enlarging the coefficient field -/

section Extension

variable (p : ℕ) [Fact p.Prime] {E K : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEK : E ≤ K)

/-- `ψ` with values in a larger field `K ⊇ E`. -/
def extendCharTo (ψ : HDec.PkgI4.GQp p →* Eˣ) : HDec.PkgI4.GQp p →* Kˣ :=
  (Units.map (IntermediateField.inclusion hEK).toRingHom.toMonoidHom).comp ψ

theorem coe_extendCharTo (ψ : HDec.PkgI4.GQp p →* Eˣ) (σ : HDec.PkgI4.GQp p) :
    ((extendCharTo p hEK ψ σ : Kˣ) : K) = IntermediateField.inclusion hEK ((ψ σ : Eˣ) : E) :=
  rfl

theorem charRep_extendCharTo (ψ : HDec.PkgI4.GQp p →* Eˣ) :
    charRep (extendCharTo p hEK ψ) =
      (Matrix.GeneralLinearGroup.map (IntermediateField.inclusion hEK).toRingHom).comp
        (charRep ψ) := by
  ext σ : 1
  apply Units.ext
  ext j l
  have hjl : j = l := Subsingleton.elim j l
  subst l
  simp [charRep, extendCharTo, Matrix.algebraMap_matrix_apply]

end Extension

/-! ## The theorem -/

/-- **Conrad, App. B, Prop. B.3 over `ℚ_p`, from `UnramifiedCyclotomicSplitting` and
`UnramifiedPeriod`.** -/
theorem conradPropB3Qp_of_inputs (hS : UnramifiedCyclotomicSplitting) (hU : UnramifiedPeriod) :
    HDec.G0Galois.C8Conrad.ConradPropB3Qp := by
  intro p _ E _ ψ n hc hn
  obtain ⟨k, hk⟩ := hn
  -- a finite Galois `K` containing `E` and a primitive `p^k`-th root of unity
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) (p ^ k)
  let Z : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] {ζ}
  haveI : FiniteDimensional ℚ_[p] Z := IntermediateField.adjoin.finiteDimensional
    (hζ.isIntegral (pow_pos (Fact.out : p.Prime).pos k)).tower_top
  let F : IntermediateField ℚ_[p] (PadicAlgCl p) := E ⊔ Z
  haveI : FiniteDimensional ℚ_[p] F :=
    show FiniteDimensional ℚ_[p] (E ⊔ Z : IntermediateField ℚ_[p] (PadicAlgCl p)) from inferInstance
  let K := IntermediateField.normalClosure ℚ_[p] F (PadicAlgCl p)
  letI : FiniteDimensional ℚ_[p] K := normalClosure.is_finiteDimensional ℚ_[p] F (PadicAlgCl p)
  letI : IsGalois ℚ_[p] K := IsGalois.normalClosure ℚ_[p] F (PadicAlgCl p)
  have hFK : F ≤ K := IntermediateField.le_normalClosure F
  have hEK : E ≤ K := (le_sup_left : E ≤ E ⊔ Z).trans hFK
  have hζK : ζ ∈ K :=
    hFK ((le_sup_right : Z ≤ E ⊔ Z) (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ))
  -- the character with values in `K`, and its splitting
  have hcK : Continuous (fun σ => (((extendCharTo p hEK ψ σ : Kˣ) : K) : PadicAlgCl p)) := hc
  obtain ⟨μ, η, hμη, hμc, hμI, hηc⟩ := hS p K (extendCharTo p hEK ψ) hcK
  obtain ⟨c, hc0, hcμ⟩ := hU p K μ hμc hμI
  -- `η = χ^n` on `G_K`
  have hη : ∀ σ ∈ K.fixingSubgroup,
      ((η σ : Kˣ) : K) = algebraMap ℚ_[p] K (ZInQ.Contrib.G9.PkgI4.cycPow p σ n) := by
    intro σ hσ
    refine eta_eq_cycPow p η k n hηc ?_ ζ hζ σ
      ((IntermediateField.mem_fixingSubgroup_iff K σ).1 hσ ζ hζK)
    intro u hu σ' hσ'I hσ'
    have h1 := hμη σ'
    rw [hμI σ' hσ'I, one_mul] at h1
    rw [← h1, coe_extendCharTo, hk u hu σ' hσ', map_zpow₀, AlgHom.commutes]
  -- the identity line of weight `n` over `G_K`
  have hID : IdentityLine p K (extendCharTo p hEK ψ) n := by
    refine identityLine_of_period p K (extendCharTo p hEK ψ) μ n c hc0 hcμ fun σ hσ => ?_
    rw [hμη σ, Units.val_mul, hη σ hσ]
  -- the count over `G_K`, then from `K` down to `E`
  have he := conradHTMult_of_identityLine p K (extendCharTo p hEK ψ) n hID
  letI : Algebra E K := (IntermediateField.inclusion hEK).toRingHom.toAlgebra
  letI : IsScalarTower ℚ_[p] E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ_[p] E K
  letI : Module.Free E K := Module.Free.of_divisionRing _ _
  have hmap : charRep (extendCharTo p hEK ψ) =
      (Matrix.GeneralLinearGroup.map (algebraMap E K)).comp (charRep ψ) :=
    charRep_extendCharTo p hEK ψ
  change finrank ℚ_[p] (HDec.PkgI4.htSpace p (charRep (extendCharTo p hEK ψ)) n) = _ at he
  let i := finrank E K
  letI : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  letI : Module.Free ℚ_[p] K := Module.Free.of_divisionRing _ _
  letI : Module.Free ℚ_[p] (HDec.PkgI4.htSpace p (charRep ψ) n) := Module.Free.of_divisionRing _ _
  rw [hmap, (HDec.G0Galois.htSpaceExtendEquiv (Module.finBasis E K) (charRep ψ) n).finrank_eq,
    ← (Finsupp.linearEquivFunOnFinite ℚ_[p] (HDec.PkgI4.htSpace p (charRep ψ) n) (Fin i)).finrank_eq,
    Module.finrank_finsupp, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ_[p] E K,
    mul_comm (finrank ℚ_[p] E)] at he
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := E) (M := K)) he

end ZInQ.Contrib.SenWeightZero

end
