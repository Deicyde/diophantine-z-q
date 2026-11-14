import ZInQKernel.HDecomp.Conductor.D1Local
import ZInQKernel.Contrib.ConductorBounds.D1

/-!
# Reused D1 local and Krasner interfaces, with one canonical supplier set

The five full consumer interfaces below are adapted from PR70 by contributor
`loning`, source `8a91bb253f2462c303c8bd9c6fa5efe190b9b834`,
`ZInQKernel/Contrib/D1.lean` (SHA-256
`b15443d9cdfefcf2db0e6e674631c7e815f5356c94fe6adb4b9c393fbfc1fc2f`).
The original PR, source attribution and review history are retained. This is a
new destination/source binding, not a claim that its old audit covers this file.

Instead of importing a second 69-module Hilbert/Serre support closure, the
first interface consumes the already proved canonical `D1_closed` from PR59.
The four local/core/unique-prime/normal-closure interfaces preserve PR70's
original residual telescopes and the unchanged baseline `D1Local` maps.
No Krasner approximation, actual H/height input or Hilbert10 conclusion is
constructed here. No protected definition or supplier source is modified.
-/

namespace ZInQ.Contrib.Conductor

open NumberField Finset GlueConductor GlueD1Local

theorem D1_genuine
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [hPl : P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  ZInQ.Contrib.ConductorBounds.D1_closed L p P a ha hea b hb

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

theorem D1_local
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : (localSub L K P).index ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine L p P a ha (ramificationIdx_le_factorial_local L p P K hcore a hdeg) b hb

theorem D1_local'
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_local L p P K hcore a ha ((index_localSub L p P K).trans_le hdeg) b hb

theorem D1_krasner
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : K.fixingSubgroup.normalCore = ⊥)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine L p P a ha (ramificationIdx_le_factorial_of_unique L p P K hclos hunique a hdeg)
    b hb

theorem D1_krasner'
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : IntermediateField.normalClosure ℚ K L = ⊤)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_krasner L p P K (normalCore_fixingSubgroup_eq_bot L K hclos) hunique a ha hdeg b hb

end ZInQ.Contrib.Conductor
