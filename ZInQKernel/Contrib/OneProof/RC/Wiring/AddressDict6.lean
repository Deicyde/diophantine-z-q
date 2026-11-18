import ZInQKernel.Contrib.OneProof.RC.Wiring.AddressDict5
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.NonVacuity

/-!
# Theorem 5.3, Lane RC0 round 3: the address leaf with the `K`-split even symbol

**Faithfulness correction of leaves 3–5.** In the dictionary form and in leaves 3–5, the even
symbol is `symb T₂ Rev` on the full even type alphabet `L₂`, and the common alphabet projects
onto all of `L₂` (conjunct 7). For the genuine objects this fails:

* conjunct 15 realizes every compatible typed graph by `K`-split primes (`Family.Admissible`
  asks `(k/q) = 1`), so the common alphabet `L` consists of `K`-split types (tex 2674–2680,
  10795–10799);
* the transported even source of `E^{(k)}` has a support containing the primes of `k` (tex
  10291–10293), so its type records `(k/q)`: the character `χ_k` of `K = ℚ(√k)` is a coordinate
  of the even alphabet `L₂`;
* the even projection of the common alphabet therefore lands in `ker χ_k`, and is not surjective
  onto `L₂`.

The manuscript reads the even source on `K`-split primes only: the seed is "a nonempty unit seed
consisting of `K`-split primes" (Lemma `ex:sec7-ksplit-seed`, tex 2628–2633; tex 10259–10273,
10323–10326), and "both seeds can be read through the actual common alphabet, whose projections
onto the two intrinsic alphabets are separately surjective" (tex 10268–10273, 10283–10286). So the
even symbol of the address construction is the **`K`-split restriction** of the full even symbol:
`evenKSplit T₂ Rev χ_k Γ = symb T₂ Rev (Γ.mapType ι)`, `ι : ker χ_k ↪ L₂` the inclusion, on the
alphabet `ker χ_k` with the sign `ε₂ ∘ ι`, and the common alphabet projects onto `ker χ_k`.

**The restriction lemma** (the coefficient rules of the full even symbol restrict to the
`K`-split types) is lane RC2's PROVED `Symbols.CoefficientRules.mapType` at `ι`
(`evenKSplit_rules`; its general statement is `EvenRestrictionLemma`, PROVED as
`evenRestrictionLemma`). The full even rules are the corrected constituent models
(`coefficientRules_of_constituentsRel`).

`AddressPackage6` is `AddressPackage5` (`AddressDict5.lean`) with the even side so restated; it is
discharged at the level of RC0's `AddressPackageStaged` (whose conjunct 9 is
`CoefficientRules ε₂ Aev` for an arbitrary even symbol `Aev`): `addressPackageStaged_of_6`,
`addressLeaf_of_6` (PROVED). Leaves 3–5 remain valid implications but should not be used as the
field type: their conjunct 7 is not satisfiable by the genuine objects.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter

/-- **The `K`-split restriction of the even symbol** (tex 2628–2633, 10259–10273, 10323–10326):
the even symbol `symb T₂ Rev` of the transported source of `E^{(k)}`, read on typed graphs whose
types lie in `ker χ_k` (the `K`-split even types), through the inclusion `ker χ_k ↪ L₂`. -/
def evenKSplit {L₂ : Type} [AddCommGroup L₂] {ε₂ : L₂ →+ ZMod 2}
    (T₂ : CoefficientDictionary.TypeData L₂ ε₂) (Rev : Finset ℕ → ZMod 2) (χk : L₂ →+ ZMod 2) :
    Symbols.Config χk.ker → ZMod 2 :=
  fun Γ => CoefficientDictionary.symb T₂ Rev (Γ.mapType χk.ker.subtype)

/-- **The restriction lemma, general form**: the coefficient rules of any symbol on an alphabet
`L₂` restrict to the kernel of any character `χ` of `L₂`, with the restricted sign. -/
def EvenRestrictionLemma : Prop :=
  ∀ (L₂ : Type) [AddCommGroup L₂] (ε₂ χ : L₂ →+ ZMod 2) (A : Symbols.Config L₂ → ZMod 2),
    Symbols.CoefficientRules ε₂ A →
      Symbols.CoefficientRules (ε₂.comp χ.ker.subtype) (fun Γ => A (Γ.mapType χ.ker.subtype))

/-- **The restriction lemma** (PROVED: lane RC2's `Symbols.CoefficientRules.mapType`, tex
2060–2065, 2102–2136: the inclusion is additive, keeps the sign coordinate and primary types, and
commutes with flips and contractions). -/
theorem evenRestrictionLemma : EvenRestrictionLemma :=
  fun _ _ _ _ _ h => h.mapType _ (fun _ => rfl)

/-- **The coefficient rules of the `K`-split even symbol** from those of the full even symbol
(PROVED by `evenRestrictionLemma`). -/
theorem evenKSplit_rules {L₂ : Type} [AddCommGroup L₂] {ε₂ : L₂ →+ ZMod 2}
    (T₂ : CoefficientDictionary.TypeData L₂ ε₂) (Rev : Finset ℕ → ZMod 2) (χk : L₂ →+ ZMod 2)
    (h : Symbols.CoefficientRules ε₂ (CoefficientDictionary.symb T₂ Rev)) :
    Symbols.CoefficientRules (ε₂.comp χk.ker.subtype) (evenKSplit T₂ Rev χk) :=
  evenRestrictionLemma L₂ ε₂ χk _ h

/-- **The address package, form 6** (the even side restricted to `K`-split types). The
conjuncts, with tex lines, kind and owner (`=` marks a conjunct of `AddressPackage5` kept
verbatim):

| item | conjunct | tex | kind | owner |
|---|---|---|---|---|
| 1 (=) | `Adm ℓ` | 1005–1011 | hypothesis of Theorem 5.3 | top layer |
| 2 (=) | `k` odd | 2596 | ELLIOT (choice of the companion) | companion: RC2 / RC11 / RC13 |
| 3 (=) | `k` squarefree | 2596–2599 | ELLIOT | companion |
| 4 (=) | a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` | 2600–2601, 2613–2614, 10484–10486 | ELLIOT (fresh ramification) | companion |
| 6 (=) | `L` finite with `x + x = 0`; the signs `ε` | 2015–2041, 2656–2657, 10525–10532 | definition (RC2 D2) | RC2 |
| 7⁶ | `π₁ : L → L₁` surjective with `ε₁ ∘ π₁ = ε`; `π₂ : L → ker χ_k` surjective with `ε₂ ∘ π₂ = ε` (the even projection onto the `K`-split even types) | 2060–2065, 2604–2611, 10268–10273, 10283–10286, 10519–10521, 10549–10551 | ELLIOT (fresh ramification lifts each old label to a `K`-split label) | RC2 |
| 7k | `χ_k(type of q) = 0 ⟺ (k/q) = 1` for every good prime `q` of the even type data | 2017–2030, 10291–10293 | definition (the support of the transported source contains the primes of `k`, so the type records `(k/q)`) | RC11 (transported source), RC2 |
| 8⁗ (=) | odd stage source: a `ConstituentModelRel` with its two inputs within the budget `W + 1`, for every cutoff `W`, at the stages of a set of `𝒰`; `a_p` even | App F 9641–9771, 9905–9953; 9585, 9593; 10533–10540 | GLUE (`stable_t`, `stable_d`, `det_orbit`, `level_red`, `kummer`, `chi_surj`, `chebotarev` in `G/N_U`, `typ_frob`, `bit_frob`; `a_p` even), ELLIOT (`two_fresh`, `reading`, `o12`), definition (`N_anti`, `N_chi`) | RC12 (App F), batch 3 CoefficientDictionary |
| 9⁶ (= 9⁗) | the full even source of `E^{(k)}` on `L₂`: a `ConstituentModelRel` with its inputs at every budget; `a_p` even. Its rules restrict to `ker χ_k` by `evenKSplit_rules` (PROVED) | as 8⁗; transported source 10288–10318 | as 8⁗ | RC12, RC11 (source) |
| 11′ (=) | bounded-weight witness of the odd stage symbols | 2588–2593, 10501–10505, 10547 | ELLIOT | RC3 seeds / batch 3 GenusOdd |
| 12′ (=) | such a graph has total type `0` | 10236–10240, 10589–10596 | definition | RC2 / RC12 |
| 13⁶ | unit seeds of the `K`-split even symbol have total type `0` | 2042–2044, 2079, 10264–10265, 10591–10594 | definition (positive square-unit filter containing `1`) | RC11, RC2 |
| 14⁶ | no nonempty unit seed of the `K`-split even symbol ⇒ lane RC3's `NoSeedTraceData` at every fresh good `K`-split prime outside a finite support | 2628–2641, 10319–10481 | ELLIOT/PRINT ((E.12), (O.11), trace identity, `d(φ)` blocks, Hecke at `p′`, (G.4a), (G.4b), `v₂a(pp′) ≥ 3`) | RC3; RC11 (transported source) |
| 15 (=) | prime realization at any stage by an admissible (`K`-split) family | 2151–2174, 2670–2672, 10582–10585, 10785–10788, 10825–10828 | GLUE/ELLIOT | RC2 |
| 16₀ (=) | `ω(D) = |V(Δ)|`, fixed local types at total type `0` | 2042–2044, 2678–2686, 10589–10596, 10795–10804 | definition/GLUE | RC2 |
| 17 (=) | odd reading at a valid stage | 2068–2079, 9670–9704, 10236–10249 (F.7), 10846–10850 | ELLIOT/definition | RC12; batch 3 AppGEndpoints |
| 18⁶ | the inputs of (F.1) for the transported source ((E.11), the lower bound, a reference coefficient), and: a unit of the `K`-split even symbol at a realization `D` attains the minimum | (E.11) 8136–8146; 10079–10091; 10288–10321; 10854–10855 | ELLIOT/PRINT ((E.11), Waldspurger comparison), ELLIOT (lower bound), definition (normalization `a_new(1) = 1`; unit = attained minimum) | RC11 (transported source), batch 3 AuxFactor |

As in leaf 5, `C_{e,final}` is produced by batch 3's `AuxFactor.F1_unit`, the readings of both
sources by the corrected constituent models, the `K`-split congruence by lane RC3's trace data;
the open-image results feed no conjunct (`AddressPackage3`). -/
def AddressPackage6 {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4)
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : Fintype L₁) (_ : DecidableEq L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (χk : L₂ →+ ZMod 2)
    (π₁ : L →+ L₁) (π₂ : L →+ χk.ker)
    (T₁ : ℕ → CoefficientDictionary.TypeData L₁ ε₁) (Rodd : ℕ → Finset ℕ → ZMod 2)
    (apo : ℕ → ℕ → ℤ) (T₂ : CoefficientDictionary.TypeData L₂ ε₂)
    (Rev : Finset ℕ → ZMod 2) (apk : ℕ → ℤ) (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7⁶) the common alphabet, its odd projection and its even projection onto the
    -- `K`-split even types `ker χ_k`
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x : L₂) = ε x) ∧
    -- (7k) `χ_k` is the character of `K = ℚ(√k)` read on the even types
    (∀ q : ℕ, T₂.Good q → (χk (T₂.typ q) = 0 ↔ jacobiSym W.kfin q = 1)) ∧
    -- (8⁗) the constituent model of the odd stage source, within the budget of every cutoff
    (∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
      (∃ X : ConstituentModelRel (T₁ θ) (Rodd θ) (apo θ) (Wc + 1), X.Inputs) ∧
        CoefficientDictionary.ApEven (T₁ θ) (apo θ)) ∧
    -- (9⁶) the constituent model of the full even source of `E^{(k)}`, at every budget
    ((∀ B, ∃ X : ConstituentModelRel T₂ Rev apk B, X.Inputs) ∧
      CoefficientDictionary.ApEven T₂ apk) ∧
    -- (11′), (12′)
    (∃ Γ₁ : Symbols.Config L₁, Γ₁.Compatible ε₁ ∧ Γ₁.V.Nonempty ∧
      ∀ᶠ θ in (W.stages : Filter ℕ), CoefficientDictionary.symb (T₁ θ) (Rodd θ) Γ₁ = 1) ∧
    (∀ Γ : Symbols.Config L₁, Γ.Compatible ε₁ →
      (∀ᶠ θ in (W.stages : Filter ℕ), CoefficientDictionary.symb (T₁ θ) (Rodd θ) Γ = 1) →
        Γ.total = 0) ∧
    -- (13⁶) unit seeds of the `K`-split even symbol have total type zero
    (∀ Γ : Symbols.Config χk.ker,
      Symbols.IsUnitSeed (ε₂.comp χk.ker.subtype) (evenKSplit T₂ Rev χk) Γ → Γ.total = 0) ∧
    -- (14⁶) the `K`-split seed: lane RC3's no-seed trace data, for the `K`-split symbol
    (∃ (Fc : Type) (_ : Field Fc) (_ : CharZero Fc) (O : Subring Fc) (Sev : Finset ℕ),
      (¬ ∃ Γ₂ : Symbols.Config χk.ker,
        Symbols.IsUnitSeed (ε₂.comp χk.ker.subtype) (evenKSplit T₂ Rev χk) Γ₂ ∧
          Γ₂.V.Nonempty) →
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
    -- (18⁶) the even reading through (F.1) for the transported source, at units of the
    -- `K`-split symbol
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
        evenKSplit T₂ Rev χk (Δ.mapType π₂) = 1 →
        inF D ∧ anew D ≠ 0 ∧ ∀ D', inF D' → anew D' ≠ 0 →
          padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ) ≤
            padicValRat 2 (anew D') - (AppGEndpoints.omega D' : ℤ)))

/-- **The staged package from form 6** (PROVED). The odd stage symbols are
`symb (T₁ θ) (Rodd θ)`, with the rules within the budget of every cutoff from the corrected
constituent models (`rulesUpTo_of_constituentsRel`); the even symbol is the `K`-split restriction
`evenKSplit T₂ Rev χ_k` on `ker χ_k` with the sign `ε₂ ∘ ι`, its rules from the full even rules
(`coefficientRules_of_constituentsRel`) by the restriction lemma (`evenKSplit_rules`); the
`K`-split congruence from lane RC3's trace data (`ksplitCongruence_of_traceData`); the even
reading with `C_{e,final} = 2δ_e + κ` from batch 3's `AuxFactor.F1_unit`. -/
theorem addressPackageStaged_of_6 {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackage6 W Ccoarse) : AddressPackageStaged W Ccoarse := by
  obtain ⟨hℓ, hk_odd, hk_sf, hq₀, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁, ε₂, χk,
    π₁, π₂, T₁, Rodd, apo, T₂, Rev, apk, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, -, h8, ⟨hX, hap⟩,
    h11, h12, h13, ⟨Fc, iF, iC, O, Sev, hD⟩, h15, h16, h17,
    ⟨inF, anew, κ, c, hE11, hE9, ⟨Dr, hDr, hDr0⟩, hunit⟩⟩ := h
  obtain ⟨δ, ⟨D₀, hD₀, hD₀δ⟩, hmin, hF1⟩ := AuxFactor.F1_unit (P := {D : ℤ // inF D})
    (fun D => anew D.1 ≠ 0) (fun D => W.Lstar (D.1 * W.kfin) ≠ 0)
    (fun D => padicValRat 2 (anew D.1)) (fun D => padicValRat 2 (W.Lstar (D.1 * W.kfin)))
    (fun D => AppGEndpoints.omega D.1) κ (fun D => hE11 D.1 D.2) c
    (fun D hD => hE9 D.1 D.2 hD) ⟨⟨Dr, hDr⟩, hDr0⟩
  have hfull : Symbols.CoefficientRules ε₂ (CoefficientDictionary.symb T₂ Rev) :=
    coefficientRules_of_constituentsRel (fun B => (hX B).choose) (fun B => (hX B).choose_spec)
      hap
  refine ⟨hℓ, hk_odd, hk_sf, hq₀, 2 * δ + κ, L, L₁, χk.ker, iL, iLf, iLd, iL₁, iL₁f, iL₁d,
    inferInstance, ε, ε₁, ε₂.comp χk.ker.subtype, π₁, π₂,
    fun θ => CoefficientDictionary.symb (T₁ θ) (Rodd θ), evenKSplit T₂ Rev χk, Realizes, hL, hπ₁,
    hπ₂, hε₁, hε₂,
    fun Wc => (h8 Wc).mono fun θ hθ => hθ.1.elim fun X hI =>
      rulesUpTo_of_constituentsRel X hI hθ.2,
    evenKSplit_rules T₂ Rev χk hfull, h11, h12, h13,
    ⟨Sev, ksplitCongruence_of_traceData O _ hD⟩, h15, h16, h17, fun θ Δ D hc hR hu => ?_⟩
  obtain ⟨hDF, hne, hle⟩ := hunit θ Δ D hc hR hu
  have hDδ : padicValRat 2 (anew D) - (AppGEndpoints.omega D : ℤ) = δ :=
    le_antisymm (hD₀δ ▸ hle D₀.1 D₀.2 hD₀) (hmin ⟨D, hDF⟩ hne)
  obtain ⟨hL0, hval⟩ := hF1 ⟨D, hDF⟩ hne hDδ
  exact ⟨hL0, le_of_eq hval⟩

/-- **The replacement leaf, form 6**: `AddressPackage6` for every choice of the constants
supplied by the other inputs (as `AddressPackageDictLeaf`; App G tex 10508–10861). -/
def AddressPackageLeaf6 {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackage6 W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **The staged leaf from leaf 6** (PROVED). -/
theorem addressPackageStagedLeaf_of_6 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf6 W) :
    AddressPackageStagedLeaf W := fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
  addressPackageStaged_of_6 W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

/-- **`AddressLeaf` from leaf 6** (PROVED, through RC0's `addressLeaf_of_stagedPackage`). -/
theorem addressLeaf_of_6 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf6 W) : AddressLeaf W :=
  addressLeaf_of_stagedPackage W (addressPackageStagedLeaf_of_6 W h)

/-- **The `K`-character conjunct (7k) is satisfiable** (PROVED; a toy case): for batch 3's sign
type data `signTypeData` (`L₂ = 𝔽₂`, the type of `q` is `(q − 1)/2 mod 2`) and `k = −1`, the
character `χ = id` satisfies `χ(type of q) = 0 ⟺ (−1/q) = 1` at every good prime. -/
theorem kCharacter_example : ∀ q : ℕ, CoefficientDictionary.signTypeData.Good q →
    ((AddMonoidHom.id (ZMod 2)) (CoefficientDictionary.signTypeData.typ q) = 0 ↔
      jacobiSym (-1 : ℤ) q = 1) := by
  intro q hq
  have hodd : q % 2 = 1 := by
    have h2 : ¬ 2 ∣ q := fun h => by
      have := Nat.Coprime.coprime_dvd_right (show 2 ∣ 4 by norm_num) hq.2
      exact absurd (Nat.Coprime.eq_one_of_dvd this.symm h) (by norm_num)
    omega
  rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr hodd)]
  show ((q / 2 : ℕ) : ZMod 2) = 0 ↔ _
  rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, ZMod.natCast_eq_zero_iff_even]
    exact ⟨fun _ => rfl, fun _ => ⟨q / 4, by omega⟩⟩
  · rw [ZMod.χ₄_nat_three_mod_four h, ZMod.natCast_eq_zero_iff_even]
    constructor
    · rintro ⟨r, hr⟩; omega
    · intro h'; norm_num at h'

end ZInQ.Manuscript.RC.Wiring
