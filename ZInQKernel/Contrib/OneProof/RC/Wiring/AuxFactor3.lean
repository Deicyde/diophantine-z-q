import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Dictionary
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.NonVacuity

/-!
# Theorem 5.3, Lane RC0 round 3: the partitionable auxiliary factor from the dictionary

The leaf `PreLeaves.aux_factor : ∃ A₀ : ℕ, AuxFactor W A₀` (App G, Proposition
`ex:app-rough-companion`, tex 10055–10150; the input `hdummy` of lane RC13's `roughCompanion`)
is replaced by `AuxFactorInputs W`: the specifications of the data on which batch 3's
`auxFactor_of_dictionary` proves it. They are, with tex lines and kinds:

1. the type data `T` of the coefficient dictionary over a finite elementary two-group `𝓛`
   (definition + GLUE; Definition `ex:sec7-typed-graph`, tex 2015–2044, and the proof of Lemma
   `ex:sec7-realization`, tex 2162–2168): the type of a prime is read from its reduced residue class
   modulo a conductor `m` with `2 ∣ m`, and the sign coordinate of the type is `(p − 1)/2 mod 2`;
2. the type conductor is supported on the fixed support `S` (definition; tex 2016–2020: types are
   read by characters at the fixed support, which contains two);
3. one prepared even source `A τ` for every total type `τ` (finitely many: `𝓛` is finite; tex
   10131–10132), with
   * the coefficient rules (ELLIOT; Lemma `ex:sec7-coefficient-rules`, tex 2102–2136, realized in
     App F, Proposition `ex:app-coefficient-rules`, tex 9447–9976);
   * zero off its filter (definition; Definition `ex:sec7-symbol`, tex 2068–2079);
   * a prepared unit seed, nonempty when the type is not negative (ELLIOT; tex 10131–10132:
     "Prepare these sources and nonempty seeds for every total type at the fixed support"; for
     negative types nonemptiness is automatic, tex 10096–10098);
4. the meaning of `W.Partitionable` (definition; Definition `ex:sec7-seed-partition`, tex
   2181–2185, read through the dictionary, tex 2031–2044): a nonzero `d` whose typed graph of
   primes (types from `T`, residue bits from Legendre symbols) is a partitionable list for the
   source of its total type is partitionable. Only this direction is required.

`auxFactor_of_inputs : SupportSpec W → AuxFactorInputs W → ∃ A₀, AuxFactor W A₀` (PROVED) is
batch 3's `auxFactor_of_dictionary`: one dummy for each anchor of a minimum seed of every total
type plus one reserve, realized after `h` and the exclusions by distinct primes in prescribed
reduced residue classes (CRT and Dirichlet), the anchors matched by RC2's
`partitionable_of_anchors` (tex 10096–10105, 10131–10139). `SupportSpec W` is the separate leaf
`PreLeaves.support`; of it only "the support consists of primes" and `2 ∈ S` are used.

The text restricts `h` to the prepared filter (in particular `h ≡ 1 mod 8`, tex 10061–10062);
`AuxFactor W A₀` quantifies over every `h > 0` prime to the support, a stronger conclusion, and the
proof does not use the congruence.

Non-vacuity (PROVED, partial): `auxFactorInputs_hstar` (the leaf does not involve `h_*`, so it is
unchanged by RC0's substitution of the genus partner); `auxFactorInputs_clauses_but_seeds`: for
every `W` satisfying `SupportSpec`, the zero symbol over batch 3's sign type data satisfies every
clause of `AuxFactorInputs` except the prepared seeds, so the content of the leaf is the seed clause
together with its coupling to `W.Partitionable`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **The inputs of the partitionable auxiliary factor** (App G, proof of
`ex:app-rough-companion`, tex 10096–10105, 10131–10139), as specifications of the data `W`: a
finite elementary two-group `𝓛` of types (`Fintype`: "There are finitely many", tex 10132) with
sign coordinate `ε`, the dictionary's type data `T` (definition + GLUE: types read from reduced
residue classes modulo `m`, `2 ∣ m`, and the sign coordinate `(p − 1)/2`; tex 2015–2044,
2162–2168; owner batch 3 CoefficientDictionary), and one prepared even source `A τ` for each total
type `τ`, such that
1. the type conductor `T.m` is supported on `W.S` (definition: the types are read at the fixed
   support, tex 2016–2020; owner RC0, construction of the data);
2. each `A τ` satisfies the coefficient rules (ELLIOT; Lemma `ex:sec7-coefficient-rules`, tex
   2102–2136, realized in App F, tex 9447–9976; owner RC2 with batch 3 CoefficientDictionary,
   whose `coefficientRules_symb` proves them for the dictionary's symbol from App F's readings);
3. each `A τ` is zero off its filter `τ` (definition; tex 2068–2079; owner RC2);
4. each `A τ` has a prepared unit seed, nonempty when `ε τ = 0` (ELLIOT; tex 10131–10132; for
   negative types nonemptiness is automatic, tex 10096–10098; owner RC2 / batch 3 AuxFactor);
5. a nonzero `d` whose typed graph of primes is a partitionable list for the source of its total
   type satisfies `W.Partitionable d` (definition; Definition `ex:sec7-seed-partition`, tex
   2181–2185, with the dictionary, tex 2031–2044; a requirement on the construction of `W`,
   owner RC0). -/
def AuxFactorInputs {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (L : Type) (_ : AddCommGroup L) (_ : Fintype L) (ε : L →+ ZMod 2)
    (T : CoefficientDictionary.TypeData L ε) (A : L → Symbols.Config L → ZMod 2),
    (∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S) ∧
    (∀ τ : L, Symbols.CoefficientRules ε (A τ)) ∧
    (∀ τ : L, Symbols.VanishesOffFilter (A τ) τ) ∧
    (∀ τ : L, ∃ Γ : Symbols.Config L, Symbols.IsUnitSeed ε (A τ) Γ ∧ (ε τ = 0 → Γ.V.Nonempty)) ∧
    ∀ d : ℤ, d ≠ 0 →
      Symbols.IsPartitionable ε (A (Symbols.primeConfig d.natAbs.primeFactors T.typ).total)
        (Symbols.primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d

/-- **The partitionable auxiliary factor** (App G, `ex:app-rough-companion`, tex 10055–10150;
PROVED from the leaf `SupportSpec W` and `AuxFactorInputs W` by batch 3's
`auxFactor_of_dictionary`). -/
theorem auxFactor_of_inputs {ℓ : ℕ} (W : WData ℓ) (hS : SupportSpec W)
    (h : AuxFactorInputs W) : ∃ A₀ : ℕ, AuxFactor W A₀ := by
  obtain ⟨L, iL, fL, ε, T, A, hmS, hA, hoff, hseed, hspec⟩ := h
  exact @ZInQ.Contrib.CloudB3RC53.AuxFactor.auxFactor_of_dictionary L iL fL ε ℓ W hS.1 hS.2.1 T
    hmS A hA hoff hseed hspec

/-! ## Non-vacuity -/

/-- **The leaf does not involve `h_*`** (PROVED): it reads only the support and `Partitionable`,
so it is unchanged when RC0 substitutes the genus partner (`WData.withHstar`). -/
theorem auxFactorInputs_hstar {ℓ : ℕ} (W : WData ℓ) (h : ℤ) (hA : AuxFactorInputs W) :
    AuxFactorInputs ({ W with hstar := h } : WData ℓ) :=
  hA

/-- The zero symbol satisfies the coefficient rules for every sign coordinate (PROVED). -/
theorem coefficientRules_zero {L : Type} [AddCommGroup L] (ε : L →+ ZMod 2) :
    Symbols.CoefficientRules ε (fun _ => (0 : ZMod 2)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ => rfl⟩

/-- **Every clause but the prepared seeds is satisfiable** (PROVED): for every `W` with
`SupportSpec W`, batch 3's sign type data (`𝓛 = ZMod 2`, conductor `4`) and the zero symbol
satisfy clauses 1, 2, 3 and 5 of `AuxFactorInputs` (clause 5 vacuously: no list is partitionable
for the zero symbol). The seed clause 4 fails for the zero symbol, which has no unit; it carries,
with its coupling to `W.Partitionable` through clause 5, the content of the leaf. -/
theorem auxFactorInputs_clauses_but_seeds {ℓ : ℕ} (W : WData ℓ) (hS : SupportSpec W) :
    (∀ p : ℕ, p.Prime → p ∣ CoefficientDictionary.signTypeData.m → p ∈ W.S) ∧
    (∀ _τ : ZMod 2, Symbols.CoefficientRules (AddMonoidHom.id (ZMod 2))
      (fun _ : Symbols.Config (ZMod 2) => (0 : ZMod 2))) ∧
    (∀ τ : ZMod 2, Symbols.VanishesOffFilter (fun _ : Symbols.Config (ZMod 2) => (0 : ZMod 2)) τ) ∧
    ∀ d : ℤ, d ≠ 0 →
      Symbols.IsPartitionable (AddMonoidHom.id (ZMod 2))
        (fun _ : Symbols.Config (ZMod 2) => (0 : ZMod 2))
        (Symbols.primeConfig d.natAbs.primeFactors CoefficientDictionary.signTypeData.typ) →
      W.Partitionable d := by
  refine ⟨fun p hp hpm => ?_, fun _ => coefficientRules_zero _, fun _ Γ h => ?_,
    fun d _ hpart => ?_⟩
  · have hm : CoefficientDictionary.signTypeData.m = 2 ^ 2 := rfl
    rw [hm] at hpm
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpm)
    rw [hp2]
    exact hS.2.1
  · exact absurd h zero_ne_one
  · obtain ⟨_, _, _, h1⟩ := hpart
    exact absurd h1 zero_ne_one

end ZInQ.Manuscript.RC.Wiring
