import ZInQKernel.Contrib.OneProof.RC.Wiring.AddressDict4
import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Pieces

/-!
# Theorem 5.3, Lane RC0 round 3: the even reading through (F.1)

`AddressPackage5` is `AddressPackage4` (`AddressDict4.lean`) with the even reading (18) and its
constant `C_{e,final}` (5) replaced by the inputs of (F.1) for the transported source of `E^{(k)}`
(App G tex 10079–10091, 10288–10321): (E.11) `v₂L_*(kD) = 2v₂a_new(D) + κ` with
`L_*(kD) ≠ 0 ⟺ a_new(D) ≠ 0` on the new filter (tex 8136–8146, 10307–10312: the normalized
central-value ratios agree), the coefficient lower bound (tex 10297–10303:
`v₂a_new(D) ≥ ω(D)`), a nonzero reference coefficient (`a_new(1) = 1`, tex 10291–10292) and the
meaning of a unit of the normalized symbol ("a unit of the normalized symbol means precisely
equality to this minimum", tex 10086–10087). The deduction of (18) with
`C_{e,final} = 2δ_e + κ` is batch 3's PROVED `AuxFactor.F1_unit` (tex 10079–10091, "For a unit of
this normalized source equality holds", 10320–10321): `addressPackage4_of_5` (PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter

/-- **The address package, form 5**: `AddressPackage4` with conjuncts 5 and 18 replaced by

| item | conjunct | tex | kind | owner |
|---|---|---|---|---|
| 18⁵ | on a filter `inF` of the transported source of `E^{(k)}` with coefficients of valuation `v₂ anew(D)` (the rational part `r_D` of (E.11)): (E.11), the lower bound `c ≤ v₂ anew(D) − ω(D)`, a nonzero reference coefficient, and: a unit of the even symbol at a realization `D` has `D` in the filter, `anew(D) ≠ 0` and `v₂ anew(D) − ω(D)` minimal | (E.11) 8136–8146; 10288–10321; (F.1) 10079–10091; 10854–10855 | ELLIOT/PRINT ((E.11), Waldspurger comparison), ELLIOT (lower bound), definition (normalization `a_new(1) = 1`; unit = attained minimum) | RC11 (transported source), batch 3 AuxFactor |

`C_{e,final} = 2δ_e + κ` is no longer a datum: batch 3's `AuxFactor.F1_unit` produces it. All other
conjuncts as in `AddressPackage4` (same tex lines, kinds and owners). -/
def AddressPackage5 {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4)
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : Fintype L₁) (_ : DecidableEq L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (T₁ : ℕ → CoefficientDictionary.TypeData L₁ ε₁) (Rodd : ℕ → Finset ℕ → ZMod 2)
    (apo : ℕ → ℕ → ℤ) (T₂ : CoefficientDictionary.TypeData L₂ ε₂)
    (Rev : Finset ℕ → ZMod 2) (apk : ℕ → ℤ) (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7)
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x) = ε x) ∧
    -- (8⁗) the constituent model of the odd stage source, within the budget of every cutoff
    (∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
      (∃ X : ConstituentModelRel (T₁ θ) (Rodd θ) (apo θ) (Wc + 1), X.Inputs) ∧
        CoefficientDictionary.ApEven (T₁ θ) (apo θ)) ∧
    -- (9⁗) the constituent model of the even source of `E^{(k)}`, at every budget
    ((∀ B, ∃ X : ConstituentModelRel T₂ Rev apk B, X.Inputs) ∧
      CoefficientDictionary.ApEven T₂ apk) ∧
    -- (11′), (12′)
    (∃ Γ₁ : Symbols.Config L₁, Γ₁.Compatible ε₁ ∧ Γ₁.V.Nonempty ∧
      ∀ᶠ θ in (W.stages : Filter ℕ), CoefficientDictionary.symb (T₁ θ) (Rodd θ) Γ₁ = 1) ∧
    (∀ Γ : Symbols.Config L₁, Γ.Compatible ε₁ →
      (∀ᶠ θ in (W.stages : Filter ℕ), CoefficientDictionary.symb (T₁ θ) (Rodd θ) Γ = 1) →
        Γ.total = 0) ∧
    -- (13)
    (∀ Γ : Symbols.Config L₂, Symbols.IsUnitSeed ε₂ (CoefficientDictionary.symb T₂ Rev) Γ →
      Γ.total = 0) ∧
    -- (14‴) the `K`-split seed: lane RC3's no-seed trace data
    (∃ (Fc : Type) (_ : Field Fc) (_ : CharZero Fc) (O : Subring Fc) (Sev : Finset ℕ),
      (¬ ∃ Γ₂ : Symbols.Config L₂,
        Symbols.IsUnitSeed ε₂ (CoefficientDictionary.symb T₂ Rev) Γ₂ ∧ Γ₂.V.Nonempty) →
      ∀ p : ℕ, ∀ hp : p.Prime, p ∉ Sev → ¬ (p : ℤ) ∣ 6 * (W.kfin * ℓ) →
        jacobiSym W.kfin p = 1 → Nonempty (@KSplit.NoSeedTraceData Fc _ O p ⟨hp⟩
          ((ZInQ.Manuscript.curve ((W.kfin * ℓ : ℤ) : ℚ)).LFunction p))) ∧
    -- (15)
    (∀ (θ b : ℕ) (Γ : Symbols.Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε → (∀ u ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' u = some w) →
      ∃ F : Family, ∃ hdim : F.b = b, Family.Admissible W.S W.kfin F ∧
        ∀ x : Fin b → ZMod 2, x ≠ 0 → Realizes θ (Γ.at act' x) (F.h (x ∘ Fin.cast hdim))) ∧
    -- (16₀)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      AppGEndpoints.omega D = Δ.V.card ∧ (Δ.total = 0 → W.prepared D)) ∧
    -- (17)
    (∀ (θ T Wb : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      Δ.V.card ≤ Wb → Wb + 1 ≤ T → (((max 0 (W.δo + Wb) + 2 : ℤ)) : ℚ) ≤ T - Ccoarse →
      (∀ D', W.admissible θ D' → AppGEndpoints.omega D' ≤ T → vZ (W.aθ θ D') < W.Mθ θ →
        (((AppGEndpoints.omega D' : ℤ) + W.δo : ℤ) : WithTop ℤ) ≤ vZ (W.aθ θ D')) →
      max 0 (W.δo + Wb) + 2 ≤ (W.Mθ θ : ℤ) → (T : ℤ) + W.δo < W.Mθ θ →
      CoefficientDictionary.symb (T₁ θ) (Rodd θ) (Δ.mapType π₁) = 1 →
      W.admissible θ D ∧
        vZ (W.aθ θ D) = (((AppGEndpoints.omega D : ℤ) + W.δo : ℤ) : WithTop ℤ)) ∧
    -- (18⁵) the even reading through (F.1) for the transported source
    (∃ (inF : ℤ → Prop) (anew : ℤ → ℚ) (κ c : ℤ),
      -- (E.11) for the transported source
      (∀ D, inF D → (W.Lstar (D * W.kfin) ≠ 0 ↔ anew D ≠ 0) ∧
        (anew D ≠ 0 →
          padicValRat 2 (W.Lstar (D * W.kfin)) = 2 * padicValRat 2 (anew D) + κ)) ∧
      -- the coefficient lower bound
      (∀ D, inF D → anew D ≠ 0 → c ≤ padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ)) ∧
      -- a nonzero reference coefficient
      (∃ D, inF D ∧ anew D ≠ 0) ∧
      -- a unit of the even symbol at a realization attains the minimum
      (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
        CoefficientDictionary.symb T₂ Rev (Δ.mapType π₂) = 1 →
        inF D ∧ anew D ≠ 0 ∧ ∀ D', inF D' → anew D' ≠ 0 →
          padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ) ≤
            padicValRat 2 (anew D') - (AppGEndpoints.omega D' : ℤ)))

/-- **Form 4 from form 5** (PROVED from batch 3's `AuxFactor.F1_unit`): the attained minimum
`δ_e` of `v₂ anew(D) − ω(D)` on the filter exists; a unit attains it, hence has `L_*(Dk) ≠ 0` and
`v₂L_*(Dk) = 2ω(D) + (2δ_e + κ)`; take `C_{e,final} = 2δ_e + κ`. -/
theorem addressPackage4_of_5 {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackage5 W Ccoarse) : AddressPackage4 W Ccoarse := by
  obtain ⟨hℓ, hk_odd, hk_sf, hq₀, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁,
    ε₂, π₁, π₂, T₁, Rodd, apo, T₂, Rev, apk, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, h8, h9, h11, h12,
    h13, h14, h15, h16, h17, ⟨inF, anew, κ, c, hE11, hE9, ⟨Dr, hDr, hDr0⟩, hunit⟩⟩ := h
  obtain ⟨δ, ⟨D₀, hD₀, hD₀δ⟩, hmin, hF1⟩ := AuxFactor.F1_unit (P := {D : ℤ // inF D})
    (fun D => anew D.1 ≠ 0) (fun D => W.Lstar (D.1 * W.kfin) ≠ 0)
    (fun D => padicValRat 2 (anew D.1)) (fun D => padicValRat 2 (W.Lstar (D.1 * W.kfin)))
    (fun D => AppGEndpoints.omega D.1) κ (fun D => hE11 D.1 D.2) c
    (fun D hD => hE9 D.1 D.2 hD) ⟨⟨Dr, hDr⟩, hDr0⟩
  refine ⟨hℓ, hk_odd, hk_sf, hq₀, 2 * δ + κ, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε,
    ε₁, ε₂, π₁, π₂, T₁, Rodd, apo, T₂, Rev, apk, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, h8, h9, h11,
    h12, h13, h14, h15, h16, h17, fun θ Δ D hc hR hu => ?_⟩
  obtain ⟨hDF, hne, hle⟩ := hunit θ Δ D hc hR hu
  have hDδ : padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ) = δ :=
    le_antisymm (hD₀δ ▸ hle D₀.1 D₀.2 hD₀) (hmin ⟨D, hDF⟩ hne)
  obtain ⟨hL0, hval⟩ := hF1 ⟨D, hDF⟩ hne hDδ
  exact ⟨hL0, le_of_eq hval⟩

/-- **The replacement leaf, form 5**: `AddressPackage5` for every choice of the constants (as
`AddressPackageLeaf3`). -/
def AddressPackageLeaf5 {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackage5 W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **Leaf 4 from leaf 5** (PROVED). -/
theorem addressPackageLeaf4_of_5 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf5 W) :
    AddressPackageLeaf4 W := fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
  addressPackage4_of_5 W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

/-- **The dictionary leaf from leaf 5** (PROVED). -/
theorem addressPackageDictLeaf_of_5 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf5 W) :
    AddressPackageDictLeaf W :=
  addressPackageDictLeaf_of_4 W (addressPackageLeaf4_of_5 W h)

/-- **`AddressLeaf` from leaf 5** (PROVED). -/
theorem addressLeaf_of_5 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf5 W) : AddressLeaf W :=
  addressLeaf_of_4 W (addressPackageLeaf4_of_5 W h)

end ZInQ.Manuscript.RC.Wiring
