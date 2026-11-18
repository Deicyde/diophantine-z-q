import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.FinalFamily

/-!
# App G endpoints: the field `final_family` (3.9) of the Theorem 5.3 deduction

Target: the field `RCSteps.final_family` of `structure RCSteps (D : RCData ℓ)` in
`ZInQKernel/Contrib/OneProof/RC/Skeleton/Steps.lean` (integration branch of the Theorem 5.3
lanes, commit 839ff728), verbatim:

```
final_family : ¬ D.OddEmptyUnit → ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
  ∃ F : Family, F.b = b ∧ D.FinalFamilyAt Co Ce F
```

with (same file) `OddEmptyUnit := ∀ᶠ θ in (D.stages : Filter ℕ), vZ (D.aθ θ 1) = D.δo` and
`FinalFamilyAt Co Ce F := F.Admissible D.S D.kfin ∧ ∀ x : Addr F.b, x ≠ 0 →
D.prepared (F.h x) ∧ AnalyticRank (Etw ℓ (F.h x)) 1 ∧ D.Lstar (F.h x * D.kfin) ≠ 0 ∧
D.jgen (F.h x) ≤ omega (F.h x) + Co ∧ padicValRat 2 (D.Lstar (F.h x * D.kfin)) ≤ 2 * omega (F.h x) + Ce`.

These files may not import that file, so `FinalFamilyField` is the same statement with the
interface data abstracted: instantiate `prepared := D.prepared`,
`simpleZero := fun h => AnalyticRank (Etw ℓ h) 1`, `Lstar := D.Lstar`, `jgen := D.jgen`,
`jrc := D.jrc`, `hstar := D.hstar`, `stages := D.stages`, `Mθ := D.Mθ`,
`v := fun θ Dd => vZ (D.aθ θ Dd)`, `admissible := D.admissible`, `δo := D.δo`, `kfin := D.kfin`,
`Fam := Family`, `dim := Family.b`, `hfam := Family.h`, `FamAdm := Family.Admissible D.S D.kfin`.
Then the premise `¬ (∀ᶠ θ, v θ 1 = δo)` is `¬ D.OddEmptyUnit` and the conclusion is the field's
conclusion (our `omega` has the same body as the interface's `omega`).

Inputs, as hypotheses:
* `RCSteps.visibility` (O.8) (App F L9407–9445), copied for its constant `C_det`;
* `RCSteps.stages_advance` (L2491–2500, L2536–2551), copied;
* the three inputs of (F.4) — the rough companion with (F.3) (L2343–2401, L10131–10146), (3.4) at
  the companions (L2427–2439) and (3.5) (L2443–2446) — exactly as in `GenusLowerF4`; these are not
  `RCSteps` fields (the field `gz_comparison` is (3.4) at the final `k` only);
* admissible theta parameters lie in the prepared filter (GLUE, L2404–2410, L8408–8429);
* **`δ_o` is the attained odd minimum** (L10189–10193, L2538–2542): `IsLeast (DepthSet …) δo`.
  This is the definition of `δ_o` in the text. `RCData` has `δo` as a bare field and `RCSteps` has
  no field fixing it; one is needed for `final_family` (Branch 2's address input is about the symbol
  `A_o(D) = [v₂ a(D) = δ_o + ω(D)]`). Proposed field, discharged for the genuine data by
  `oddMinimumF6_proof` (which produces the minimum from (F.5) and the fixed witness `D_w`):
  `odd_minimum : IsLeast {r : ℤ | ∃ (W : ℕ) (Ds : ℕ → ℤ), ∀ᶠ θ in (D.stages : Filter ℕ),
  D.admissible θ (Ds θ) ∧ omega (Ds θ) ≤ W ∧ vZ (D.aθ θ (Ds θ)) < D.Mθ θ ∧
  vZ (D.aθ θ (Ds θ)) = ((omega (Ds θ) : ℤ) + r : ℤ)} D.δo`. (RC0 round 2 resolves this in
  `RC/Wiring/OddMinimum.lean`: `exists_oddMinimum` is PROVED and the skeleton's `δ_o` is chosen as
  that least element, so `odd_minimum` is a theorem there.)
* in Branch 2, the address input (`AddressInput`, see `FinalFamily.lean`) at `δ_o`, for one
  constant `C_{e,final}` and the coarse constant `C_coarse = C_gen/2 + C_det`.

Kind: PROVED (from these inputs). `C_o = δ_o + C_det`, `C_e = C_{e,final}`, both before `b`.
-/

namespace ZInQ.Contrib.CloudB3RC53.AppGEndpoints

open Filter

/-- **The field `final_family` (3.9)** (Proposition `ex:sec7-final-family`, tex L2674–2713; App G
`ex:app-odd-minimum` L10151–10256 and `ex:app-final-family` L10792–10861; PROVED from the inputs
listed in the module docstring). -/
def FinalFamilyField : Prop :=
  ∀ (prepared simpleZero : ℤ → Prop) (Lstar : ℤ → ℚ) (jgen : ℤ → ℤ) (jrc : ℤ → ℤ → ℤ)
    (hstar : ℤ) (stages : Ultrafilter ℕ) (Mθ : ℕ → ℕ) (v : ℕ → ℤ → WithTop ℤ)
    (admissible : ℕ → ℤ → Prop) (δo kfin : ℤ)
    (companion : ℤ → ℤ → Prop) (s : ℤ → ℕ) (A CR CE Cper Cdet : ℤ)
    (Fam : Type) (dim : Fam → ℕ) (hfam : (F : Fam) → (Fin (dim F) → ZMod 2) → ℤ)
    (FamAdm : Fam → Prop),
    -- `RCSteps.visibility` (O.8), at its constant `C_det`
    (∀ θ : ℕ, ∀ Dd : ℤ, admissible θ Dd → v θ Dd < Mθ θ →
      simpleZero Dd ∧ (jgen Dd : WithTop ℤ) ≤ v θ Dd + Cdet) →
    -- `RCSteps.stages_advance`
    Tendsto Mθ (stages : Filter ℕ) atTop →
    -- the inputs of (F.4): rough companion with (F.3), (3.4) at the companions, (3.5)
    (∀ h, prepared h → simpleZero h → ∃ k', companion h k' ∧ (omega k' : ℤ) ≤ A ∧
      Lstar (h * k') ≠ 0 ∧
      padicValRat 2 (Lstar (h * k')) ≤ 2 * omega h + 2 * omega k' + s (h * k') + CE) →
    (∀ h k', prepared h → simpleZero h → companion h k' → ∃ ε : ℤ, |ε| ≤ 2 ∧
      2 * jrc h k' - 2 * jgen h =
        padicValRat 2 (Lstar (h * k')) - padicValRat 2 (Lstar hstar) + Cper + ε) →
    (∀ h k', prepared h → simpleZero h → companion h k' → (omega k' : ℤ) ≤ A →
      4 * (omega h : ℤ) + s h + s (h * k') - CR ≤ 2 * jrc h k') →
    -- admissible theta parameters lie in the prepared filter
    (∀ θ Dd, admissible θ Dd → prepared Dd) →
    -- `δ_o` is the attained odd minimum
    IsLeast (DepthSet stages Mθ v admissible) δo →
    -- Branch 2: the address input at `δ_o`
    (¬ (∀ᶠ θ in (stages : Filter ℕ), v θ 1 = (δo : WithTop ℤ)) → ∃ CeFinal : ℤ,
      AddressInput stages Mθ v admissible prepared Lstar kfin δo CeFinal
        (((2 * A + CR + CE - padicValRat 2 (Lstar hstar) + (Cper + 2) : ℤ) : ℚ) / 2 + Cdet)
        Fam dim hfam FamAdm) →
    -- the field
    ¬ (∀ᶠ θ in (stages : Filter ℕ), v θ 1 = (δo : WithTop ℤ)) →
    ∃ Co Ce : ℤ, ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∃ F : Fam, dim F = b ∧
      (FamAdm F ∧ ∀ x : Fin (dim F) → ZMod 2, x ≠ 0 →
        prepared (hfam F x) ∧ simpleZero (hfam F x) ∧ Lstar (hfam F x * kfin) ≠ 0 ∧
        jgen (hfam F x) ≤ (omega (hfam F x) : ℤ) + Co ∧
        padicValRat 2 (Lstar (hfam F x * kfin)) ≤ 2 * (omega (hfam F x) : ℤ) + Ce)

theorem finalFamilyField_proof : FinalFamilyField := by
  intro prepared simpleZero Lstar jgen jrc hstar stages Mθ v admissible δo kfin companion s A CR
    CE Cper Cdet Fam dim hfam FamAdm hvis hM h33 h34 h35 hprep hδo hAddr hne
  set Cgen : ℤ := 2 * A + CR + CE - padicValRat 2 (Lstar hstar) + (Cper + 2) with hCgen
  -- (F.4) and (F.5)
  have hF4 : ∀ D, (∃ θ, admissible θ D) → simpleZero D →
      2 * (omega D : ℤ) + s D - Cgen ≤ 2 * jgen D :=
    fun D ⟨θ, hD⟩ hz =>
      genusLowerF4_proof prepared simpleZero companion Lstar jgen jrc s hstar A CR CE Cper
        h33 h34 h35 D (hprep θ D hD) hz
  have hF5 : ∀ θ D, admissible θ D →
      QLe (min (Mθ θ : ℚ) (omega D - (((Cgen : ℤ) : ℚ) / 2 + Cdet))) (v θ D) :=
    fun θ D hD => coarseF5_proof (admissible θ) simpleZero jgen s (v θ) (Mθ θ) Cdet Cgen
      (fun D' hD' hlt => hvis θ D' hD' hlt) (fun D' hD' hz => hF4 D' ⟨θ, hD'⟩ hz) D hD
  -- (F.6) at `δ_o`
  have hF6 := f6_of_isLeast hF5 hδo
  -- the final family
  obtain ⟨CeFinal, hA⟩ := hAddr hne
  obtain ⟨b₀, hb⟩ := finalFamily39_proof stages Mθ v admissible simpleZero prepared jgen Lstar
    kfin δo Cdet CeFinal _ Fam dim hfam FamAdm hM hvis hF5 hF6 hA
  exact ⟨δo + Cdet, CeFinal, b₀, hb⟩

end ZInQ.Contrib.CloudB3RC53.AppGEndpoints
