import ZInQKernel.Contrib.OneProof.RC.Wiring.Address
import ZInQKernel.Contrib.OneProof.RC.Wiring.TraceModelRel

/-!
# Theorem 5.3, Lane RC0 round 3: a smaller address leaf

`PostLeaves.address : AddressPackageDictLeaf W` (`Wiring/Address.lean`) asks, in Branch 2 and
for every choice of the constants of (F.3), (3.4), (3.5), (O.8), for lane RC2's address package in
the dictionary form `AddressPackageDict`. This file gives a replacement leaf
`AddressPackageLeaf3 W` and the PROVED conversion
`addressPackageDictLeaf_of_3 : AddressPackageLeaf3 W → AddressPackageDictLeaf W` (hence
`addressLeaf_of_3 : AddressPackageLeaf3 W → AddressLeaf W`). Two conjunct groups shrink:

* **the coefficient readings** (8″), (9″) of `AddressPackageDict` (lane RC12's readings on prime
  sets: fixed-`U` factorization, (O.12) with the product-label rule, primary isolation) are
  replaced by the trace-module model they come from (App F tex 9641–9953): the corrected model
  `TraceModelRel` (`Wiring/TraceModelRel.lean`) of the odd stage source within the budget of
  every cutoff at the stages of a set of `𝒰` (8‴), and of the even source of `E^{(k)}` at every
  budget (9‴). The three readings are PROVED from the model (`TraceModelRel.fixedU_of_model`,
  `o12_of_model`, `primary_of_model`, which follow batch 3's proofs). Batch 3's own `TraceModel`
  and `ConstituentModel` are not used: they are inconsistent (`traceModel_false`,
  `constituentModel_false`), so `coefficientRules_of_model` and `coefficientRules_of_constituents`
  hold vacuously and a leaf asking for them could never be discharged;
* **the `K`-split congruence** (14) (Elliot's conditional App G congruence
  `a_p(E^{(k)}) ≡ p + 1 (mod 8)`, tex 2636–2641, 10319–10481) is replaced by lane RC3's
  `NoSeedTraceData` at the fresh good `K`-split primes outside a finite support (14‴): the
  deduction of the congruence from the trace data ((G.4c), `H[p³] ∈ 2𝒪`, the mod-eight step, and
  the full rational two-torsion congruence `4 ∣ p + 1 − a_p`) is lane RC3's PROVED
  `appGCongruence_of_traceData`, wired through `ksplitCongruence_of_traceData` (`Address.lean`).
  `NoSeedTraceData` is satisfiable (lane RC3's `noSeedTraceData_example`).

Every other conjunct is that of `AddressPackageDict`, verbatim. The open-image results of batch 3
(`OpenImage.openImageInput`, `OpenImage.h2_genuine`, tex 2881–2900) feed no conjunct of the
package; see the docstring of `AddressPackage3`.

Kinds: `PROVED` (Lean proof), `ELLIOT` (Elliot's step, stated), `GLUE` (textbook fact),
`PRINT` (published theorem), `definition`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter

/-- **The address package, form 3.** The conjuncts, with tex lines, kind and owner (conjuncts
marked `=` are those of `AddressPackageDict`, verbatim):

| item | conjunct | tex | kind | owner |
|---|---|---|---|---|
| 1 | `Adm ℓ` (=) | 1005–1011 | hypothesis of Theorem 5.3 | top layer |
| 2 | `k` odd (=) | 2596 | ELLIOT (choice of the companion) | companion: RC2 / RC11 / RC13 |
| 3 | `k` squarefree (=) | 2596–2599 | ELLIOT | companion |
| 4 | a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` (=) | 2600–2601, 2613–2614, 10484–10486 | ELLIOT (fresh ramification) | companion |
| 5 | `C_{e,final}` (=) | 10320–10322, 10854–10857 | definition | RC11 |
| 6 | `L` finite with `x + x = 0`; the signs `ε` (=) | 2015–2041, 2656–2657, 10525–10532 | definition (RC2 D2) | RC2 |
| 7 | `π₁, π₂` surjective, `ε₁ ∘ π₁ = ε`, `ε₂ ∘ π₂ = ε` (=) | 2060–2065, 2604–2611, 10270–10273, 10283–10286, 10519–10521, 10549–10551 | ELLIOT (fresh ramification lifts each old odd label to a `K`-split label) | RC2 |
| 8‴ | for every cutoff `W`, at the stages of a set of `𝒰`: a `TraceModelRel` of the odd stage source within the budget `W + 1`, and `a_p` even | App F 9641–9771, 9905–9953; 9585, 9593; 10533–10540 | model: ELLIOT trace identities (tex 9705–9745), GLUE (level and continuity, Kummer, independence, Chebotarev in `G/N_U`, Frobenius dictionary; tex 9524–9548, 9663–9669, 9745–9750), definition (`N_U`), ELLIOT inputs `reading` (9671–9704) and `o12` (9905–9918); `a_p` even GLUE | RC12 (App F), batch 3 CoefficientDictionary |
| 9‴ | the same for the even source of `E^{(k)}`, at every budget | as 8‴; transported source 10288–10318 | as 8‴ | RC12, RC11 (source) |
| 11′ | bounded-weight witness: a nonempty compatible graph where the stage symbols are one on a set of `𝒰` (=) | 2588–2593, 10501–10505, 10547 | ELLIOT | RC3 seeds / batch 3 GenusOdd |
| 12′ | such a graph has total type `0` (=) | 10236–10240, 10589–10596 | definition | RC2 / RC12 |
| 13 | unit seeds of the even symbol have total type `0` (=) | 2042–2044, 2079, 10264–10265, 10591–10594 | definition | RC11, RC2 |
| 14‴ | no nonempty unit seed of the even symbol ⇒ lane RC3's `NoSeedTraceData` at every fresh good `K`-split prime outside a finite support, with `a_p = a_p(E^{(k)})` | 2636–2641, 10319–10481 | ELLIOT/PRINT ((E.12), `a(1) = 1`, `ψ/η = χ₋₁`, integrality of `H` (O.11), the trace identity, the `d(φ)` block action, the Hecke formula at `p′`, (G.4a), (G.4b), `v₂ a(pp′) ≥ 3`) | RC3; RC11 (transported source) |
| 15 | prime realization at any stage by an admissible family (=) | 2151–2174, 2670–2672, 10582–10585, 10785–10788, 10825–10828 | GLUE/ELLIOT | RC2 |
| 16₀ | `ω(D) = |V(Δ)|`, fixed local types at total type `0` (=) | 2042–2044, 2678–2686, 10589–10596, 10795–10804 | definition/GLUE | RC2 |
| 17 | odd reading at a valid stage (=) | 2068–2079, 9670–9704, 10236–10249 (F.7), 10846–10850 | ELLIOT/definition | RC12; batch 3 AppGEndpoints |
| 18 | even reading (=) | (E.11) 8141, (F.1) 10079–10094, 10288–10322, 10854–10855 | ELLIOT | RC11 |

**Open image (batch 3's `OpenImage`) feeds none of these.** `openImageInput` and `h2_genuine` are
the uniform torsion annihilator (H1), (H2) of Proposition `ex:arith-finite-heegner` (tex
2881–2900): the scalar `g` with `ρ_T(g) = (1 + 2ⁿ)I`, complex conjugation and `G_K` of index two,
bounding `E(H_d)[2^∞]` over ring-class fields. No conjunct mentions the `2`-adic image `ρ_T`,
complex conjugation, ring-class fields or torsion points. The only Galois input about `K` here is
the independence of the quadratic character of `K` from the old label characters, `χ₋₁` and
`χ_ℓ`, and of `K` from `ℚ(E[8])` (tex 2604–2614). It comes from the fresh ramification at `q₀`
(conjunct 4), not from open image, and it is consumed by lane RC3's PROVED
`exists_ksplit_prime_v2_eq_two_b3` (CRT and Dirichlet, inside `exists_unitSeed_of_ksplit`) and by
conjunct 7. `stabilizer_index_eq_two` (`[G_ℚ : G_K] = 2`) is the Galois form of "`k` is not a
square", which nothing here needs in that form. The Chebotarev field of the trace model
(8‴, 9‴) is Chebotarev for the finite quadratic and trace quotients `G/N_U` (tex 9666–9668, 9749),
which open image does not supply. -/
def AddressPackage3 {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ) : Prop :=
  -- (1)–(4)
  Adm ℓ ∧ Odd W.kfin ∧ Squarefree W.kfin ∧
  (∃ q₀ : ℕ, q₀.Prime ∧ (q₀ : ℤ) ∣ W.kfin ∧ ¬ q₀ ∣ 2 * ℓ) ∧
  -- (5)
  ∃ CeFinal : ℤ,
  ∃ (L L₁ L₂ : Type) (_ : AddCommGroup L) (_ : Fintype L) (_ : DecidableEq L)
    (_ : AddCommGroup L₁) (_ : Fintype L₁) (_ : DecidableEq L₁) (_ : AddCommGroup L₂)
    (ε : L →+ ZMod 2) (ε₁ : L₁ →+ ZMod 2) (ε₂ : L₂ →+ ZMod 2) (π₁ : L →+ L₁) (π₂ : L →+ L₂)
    (T₁ : ℕ → CoefficientDictionary.TypeData L₁ ε₁) (Rodd : ℕ → Finset ℕ → ZMod 2)
    (apo : ℕ → ℕ → ℤ) (T₂ : CoefficientDictionary.TypeData L₂ ε₂)
    (Rev : Finset ℕ → ZMod 2) (apk : ℕ → ℤ) (Realizes : ℕ → Symbols.Config L → ℤ → Prop),
    -- (6), (7)
    (∀ x : L, x + x = 0) ∧ Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    (∀ x, ε₁ (π₁ x) = ε x) ∧ (∀ x, ε₂ (π₂ x) = ε x) ∧
    -- (8‴) the trace model of the odd stage source, within the budget of every cutoff
    (∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
      Nonempty (TraceModelRel (T₁ θ) (Rodd θ) (apo θ) (Wc + 1)) ∧
        CoefficientDictionary.ApEven (T₁ θ) (apo θ)) ∧
    -- (9‴) the trace model of the even source of `E^{(k)}`, at every budget
    ((∀ B, Nonempty (TraceModelRel T₂ Rev apk B)) ∧ CoefficientDictionary.ApEven T₂ apk) ∧
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
    -- (18)
    (∀ (θ : ℕ) (Δ : Symbols.Config L) (D : ℤ), Δ.Compatible ε → Realizes θ Δ D →
      CoefficientDictionary.symb T₂ Rev (Δ.mapType π₂) = 1 →
      W.Lstar (D * W.kfin) ≠ 0 ∧
        padicValRat 2 (W.Lstar (D * W.kfin)) ≤ 2 * (AppGEndpoints.omega D : ℤ) + CeFinal)

/-- **The dictionary package from form 3** (PROVED): the readings (8″), (9″) from the corrected
trace models (`TraceModelRel.fixedU_of_model`, `o12_of_model`, `primary_of_model`), and the
conditional congruence (14) from lane RC3's trace data (`ksplitCongruence_of_traceData`, i.e.
lane RC3's `appGCongruence_of_traceData`). -/
theorem addressPackageDict_of_3 {ℓ : ℕ} (W : WData ℓ) (Ccoarse : ℚ)
    (h : AddressPackage3 W Ccoarse) : AddressPackageDict W Ccoarse := by
  obtain ⟨hℓ, hk_odd, hk_sf, hq₀, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁,
    ε₂, π₁, π₂, T₁, Rodd, apo, T₂, Rev, apk, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂, hodd8,
    ⟨hX, hap⟩, h11, h12, h13, ⟨Fc, iF, iC, O, Sev, hD⟩, hrest⟩ := h
  exact ⟨hℓ, hk_odd, hk_sf, hq₀, CeFinal, L, L₁, L₂, iL, iLf, iLd, iL₁, iL₁f, iL₁d, iL₂, ε, ε₁,
    ε₂, π₁, π₂, T₁, Rodd, apo, T₂, Rev, apk, Realizes, hL, hπ₁, hπ₂, hε₁, hε₂,
    fun Wc => (hodd8 Wc).mono fun θ hθ => hθ.1.elim fun X =>
      ⟨X.fixedU_of_model, X.o12_of_model, hθ.2, X.primary_of_model⟩,
    ⟨fun B => (hX B).elim fun X => X.fixedU_of_model,
      fun B => (hX B).elim fun X => X.o12_of_model, hap,
      fun B => (hX B).elim fun X => X.primary_of_model⟩,
    h11, h12, h13, ⟨Sev, ksplitCongruence_of_traceData O _ hD⟩, hrest⟩

/-- **The replacement leaf**: `AddressPackage3` for every choice of the constants supplied by the
other inputs (as `AddressPackageDictLeaf`): in Branch 2, for all constants `A, C_E, C_R, C_per,
C_det` satisfying (F.3), (3.4) at the companions, (3.5) and (O.8), the package at the coarse
constant `C_coarse = C_gen/2 + C_det` of (F.5) (App G tex 10508–10861; owners as in
`AddressPackage3`). -/
def AddressPackageLeaf3 {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → ¬ W.OddEmptyUnit →
    AddressPackage3 W
      (((2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2) : ℤ) : ℚ) / 2 +
        Cdet)

/-- **The dictionary leaf from the replacement leaf** (PROVED). -/
theorem addressPackageDictLeaf_of_3 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf3 W) :
    AddressPackageDictLeaf W := fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
  addressPackageDict_of_3 W _ (h A CE CR Cper Cdet h33 h34 h35 hvis hU)

/-- **`AddressLeaf` from the replacement leaf** (PROVED). -/
theorem addressLeaf_of_3 {ℓ : ℕ} (W : WData ℓ) (h : AddressPackageLeaf3 W) : AddressLeaf W :=
  addressLeaf_of_dictPackage W (addressPackageDictLeaf_of_3 W h)

/-! ## Non-vacuity of the new coefficient conjuncts -/

/-- **The new coefficient conjuncts (8‴), (9‴) are satisfiable** (PROVED): for any stage type data
`T₁ θ`, any even type data `T₂` and any filter of stages, the zero readings with `a_p = 0` carry
corrected trace models at every budget (`TraceModelRel.zero`). This is the non-vacuity of these
conjuncts in the sense of batch 3's `coefficientRules_symb_nonvacuous`; batch 3's `TraceModel`
has no such witness (`traceModel_false`). -/
theorem coefficientConjuncts3_zero {L₁ L₂ : Type} [AddCommGroup L₁] [AddCommGroup L₂]
    {ε₁ : L₁ →+ ZMod 2} {ε₂ : L₂ →+ ZMod 2} (𝒰 : Filter ℕ)
    (T₁ : ℕ → CoefficientDictionary.TypeData L₁ ε₁) (T₂ : CoefficientDictionary.TypeData L₂ ε₂) :
    (∀ Wc : ℕ, ∀ᶠ θ in 𝒰,
      Nonempty (TraceModelRel (T₁ θ) (fun _ => 0) (fun _ => 0) (Wc + 1)) ∧
        CoefficientDictionary.ApEven (T₁ θ) (fun _ => 0)) ∧
    ((∀ B, Nonempty (TraceModelRel T₂ (fun _ => 0) (fun _ => 0) B)) ∧
      CoefficientDictionary.ApEven T₂ (fun _ => 0)) :=
  ⟨fun _ => Filter.Eventually.of_forall fun θ =>
      ⟨traceModelRel_zero_nonempty (T₁ θ) _ _, fun _ _ => ⟨0, rfl⟩⟩,
    ⟨fun B => traceModelRel_zero_nonempty T₂ _ B, fun _ _ => ⟨0, rfl⟩⟩⟩

end ZInQ.Manuscript.RC.Wiring
