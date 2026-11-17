# r17-bypass: the field `r17` (Carayol, `LadicCond.CarayolR17'`)

Task r17-bypass, branch `wip/r17-bypass`, base 9a100aa7 (leaf-fold22), 2026-11-15.

## 0. Verdict

**`r17` cannot be removed.** It is used once on the route, at general instances (not special, not
vacuous), and no bundle field implies even the weakest form the route needs. Two results:

1. **Weakest needed form** (VERIFIED by reading the consumer): the only theorem that applies `r17`
   is `G0ModNewform.g15` (step D5, "from conductor to level"), and it uses only the inequality
   `v_p(N) ≤ a(ρ|G_{ℚ_p})` for `p ∣ N`, at `ℓ = 5`, `p ≠ 5` and at `ℓ = 3`, `p = 5`. This is
   `CarayolLevel.CarayolLevelLe`, the "level divides the prime-to-ℓ conductor" half of Carayol's
   equality. It is a consequence of Carayol 1986 Théorème (A) with Casselman 1973, not a printed
   statement, and it is the deep half (it needs `ρ_f|G_{ℚ_p}` at `p ∣ N`), so weakening `r17` to it
   gains nothing for the GLUE count. The whole consumer chain up to `afterG7_of3` is re-proved from
   it (`scratch/r17-bypass/Bypass.lean`), for an integrator who wants the bypass anyway.
2. **Discharge (autofold-compatible): `r17` from a new leaf, the existence form**
   `CarayolLevel.NewformRepConductor`: *there is* a semisimple `ρ` attached to `f` with
   `a(ρ|G_{ℚ_p}) = v_p(N)` for every `p ≠ ℓ`. That is how the source and the surveys state the
   result: for the representation `ρ_{f,λ}` they build, not for every semisimple `ρ` with the same
   traces. The passage to every such `ρ` (one of the three silent steps the g0-mod-newform review
   listed in `CarayolR17'`) is now proved in Lean: Brauer–Nesbitt (kernel), Chebotarev (kernel T18),
   and the invariance of the Serre–Tate conductor `condExp` under isomorphism (new, proved without
   `SwanIndependent`). File `ZInQKernel/Contrib/OneProof/CarayolLevel.lean`, theorem
   `CarayolLevel.carayolR17'_of_newformRepConductor : NewformRepConductor → LadicCond.CarayolR17'`.
   Conversely `newformRepConductor_of_R17'` (with R14's existence) shows the two are equivalent
   modulo proved glue, so the new leaf is not stronger than the field it replaces.

**Count.** The new leaf is proposed as kind `published` with flag `pending reading` (the conductor
packaging "`ρ_{f,λ}` has prime-to-`ℓ` conductor `N`" is believed printed, Darmon–Diamond–Taylor §3.1
and Carayol §0 for `F = ℚ`, but nobody has read it; UNVERIFIED). It therefore counts GLUE until a
reading: the fold changes nothing in either count now (strict 46/10 unchanged), and becomes
**−1 strict GLUE** when a statement check finds the conductor equality printed for `ρ_{f,λ}`. If no
print states it, the leaf stays a consequence of Carayol (A) + Casselman, like `r17` today, with the
transport step removed from it.

**Compiles** (VERIFIED, 2026-11-15, Lean 4.35.0 / Mathlib v4.35.0): the contribution, the bypass
file, `#discharges` (r17 discharged, still assumes only the new leaf, standard axioms) and the
autofold dry-run fold (`sixContactMin_of_open29`, standard axioms). Details in §5.

## 1. Where `r17` is used (VERIFIED: grep and reading)

* Every `r17 := r.r17` / `n.r17` in `TailX`, `TailZ4` … `TailZ34` is a pass-through between bundle
  generations; `TailN.lean:118` (`carayolR17_ofK5`) only changes the copy of `GaloisRep`.
* The one consumer: `TailK.lean:333`, inside the G0 term, `G0AssembleMod.afterG7_of3 … r.r17 …`
  (`TailD.lean:156`) → `newformLeaves_of3` (`TailD:150`) puts it in `G0ModNewform.NewformLeaves.r17`
  (`TailA:3703`) → `modularConstituent_tail_G` (`TailA:4038`) → `modularConstituent_tail`
  (`TailA:3747`) → `g13_g16_ram` → `g13_g16` (`TailA:3712`) → **`g15 lv.r17 hSw …`** (`TailA:3537`),
  via `carayolR17_of_R17'` and `factorization_eq_condAt` (`TailA:3522`).
* Instances: `ℓ = 5` at every prime `p ≠ 5`, `ℓ = 3` at `p = 5`; `ρ` is R14's semisimple
  representation attached to `f`, isomorphic to G8's `r₅` (resp. `r₃`); `f` is the newform obtained
  from Pan–Berger's eigenform for `r₅` (`newform_of_pan`: twist T24, newform T25), of arbitrary level
  `N`. So: a general weight-2 newform whose 5-adic representation is a 2-dimensional constituent of
  `V₅(A)` for the manuscript's model `A/L'`, at every prime. Nothing makes the instance special: `N` is not
  computed, `A` varies with `u ∈ ℚ`.
* What g15 does with `v_p(N) = c` (`c` the conductor at an adapted level): `c ≤ E₀ ⇒ v_p(N) ≤ E₀`
  (`p ≤ D`), `c ≤ 2 ⇒ v_p(N) ≤ 2` (`p > D`), `c = 0 ⇒ p ∤ N` (`p ∉ T`). Only `v_p(N) ≤ c` is used,
  and only at `p ∣ N` (at `p ∤ N` the inequality is `0 ≤ c`).

## 2. The weakest needed form

```lean
def CarayolLevel.CarayolLevelLe : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ → p ∣ N →
      (N.factorization p : ℚ) ≤ condExp (ρ.restrictLocal p)
```

(`ℓ` general for readability; the route instantiates `ℓ ∈ {3, 5}` only.) `carayolLevelLe_of_R17'`
proves it from `CarayolR17'`. `scratch/r17-bypass/Bypass.lean` proves `g15_of_levelLe`
(`G15Out N u` from it), `g13_g16_levelLe`, `modularConstituent_tail_G_levelLe` and
`HSyn.G0AssembleMod.afterG7_of3_levelLe` (`AfterG7` from it, the other inputs of `afterG7_of3`
unchanged), with the original `afterG7_of3` recovered as a special case. A bypass fold would still
have to restate the G0 term of `TailK.lean` (a TailZ23-style fold); since it gains nothing in the
count, it is not recommended.

**Source and status.** Printed source: Carayol 1986, Théorème (A) (pp. 409-411, §0.8 p. 411; read
by the locator audit: all `p ∤ ℓ`, all `ℓ`, `p ∣ N` included) with Casselman 1973 (`a(π_p) = v_p(N)`
for newforms; UNVERIFIED) and the conductor compatibility of the local Langlands correspondence for
`GL₂`. **Not a printed statement** in this form: it is the "≤" half of the printed (UNVERIFIED)
equality `N(ρ_{f,λ}) = N` away from `ℓ`.

## 3. Why no bundle field gives it (argument)

The inequality is a statement about `ρ_f|G_{ℚ_p}` at primes `p ∣ N`. What the bundles say about `f`
and `ρ_f`: R14 (now from Diamond–Shurman 9.6.5, `dsThm965`) and R16 (Eichler–Shimura on `J₁(N)`,
`r16` / `R16CoreY`) only at `p ∤ Nℓ`; NOS (`r7a`) turns "`ρ_f` unramified at `p`" into "`A_f` has
good reduction at `p`", but "`A_f` (new quotient) has bad reduction at `p ∣ N`" is
Deligne–Rapoport/Carayol, in no bundle; Faltings (`r9a`, `r9b`), de Rham (`r10`, `deRhamH1AbVarT`),
Raynaud (`raynaudSemistableSH`), Kato (`eigenformHTNew`, at `ℓ`), the Tate-module and CM leaves
concern `A` or the place `ℓ`, not `ρ_f` at `p ∣ N`. Nor can the consumer avoid the level: `G16Out`
needs some bounded `N` with `A` a constituent of `J₁(N)`, and Pan's modularity theorem gives no level
(the level of Pan's eigenform `M` is not bounded by anything in the bundles). The instances are
general (§1), so no special-case computation applies. SPECULATIVE only in the sense that "no
combination of the fields implies it" is an argument, not a Lean statement; each field's content was
read.

## 4. The discharge

```lean
def CarayolLevel.NewformRepConductor : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

theorem CarayolLevel.carayolR17'_of_newformRepConductor (h : NewformRepConductor) :
    LadicCond.CarayolR17'
```

All objects are the kernel's (`ZInQKernel/HDecomp/Conductor/LadicCond.lean`: `GaloisRep`,
`AttachedTo`, `IsNewform`, `condExp`, `restrictLocal`). The proof: for the given `ρ` and the leaf's
`ρ'`, `iso_of_attached` (Brauer–Nesbitt `TSkolemKW.C10.brauerNesbittChar0'`, T18 from
`ZInQ.Contrib.frobeniusDense`, `C9Rhof.iso_of_arithFrob`) gives an equivariant `e : ρ ≅ ρ'`; then
`condExp_eq_of_intertwine` (new: codimensions of invariants agree, the adapted levels of `ρ` and
`ρ'` coincide, so the classical choice in `swan` picks the same level) transfers the conductor.
The file imports only kernel modules (`LadicCond`, `ModCurves.C9`, `Textbook.C10Closed`,
`Contrib.Chebotarev.FrobeniusDense`), not the chain.

**Rating of the new leaf.** Printed form: *pending reading*. Carayol's Théorème (A) is stated for
`π` and the local Langlands correspondence (not definable in Mathlib, as the task notes); the
conductor packaging for `ρ_{f,λ}` is the form textbooks and surveys quote ("the conductor of
`ρ_{f,λ}` is `N` away from `ℓ`"), and is the published statement or its direct consequence:
existence of `ρ_{f,λ}` (Eichler–Shimura–Deligne), semisimplicity (Ribet 1977: irreducible),
continuity, the Tate normalization (dual of the cohomological one; the conductor is unchanged), and
the conductor equality (Carayol (A) + Casselman). It is not stronger than the print: it asserts one
representation, as printed; the extension of scalars `K_{f,λ} → ℚ̄_ℓ` along `ιL ∘ ιC⁻¹` does not
change the conductor (codimensions of invariants are invariant under field extension).
Proposed `locators.md` row (not added: another task's file):
`R17 (existence form) | Carayol 1986 §0 and Théorème (A); Darmon–Diamond–Taylor 1997 §3.1 | — |
UNVERIFIED | conductor of ρ_{f,λ} equals N away from ℓ; check whether printed for ρ_{f,λ} itself`.

## 5. Compile status and `#discharges`

All runs at base 9a100aa7 on the host, one Lean process at a time.

| what | command | outcome |
| --- | --- | --- |
| contribution | `lake build ZInQKernel.Contrib.OneProof.CarayolLevel` | success, 17 s, no warning in the file (VERIFIED) |
| bypass | `lake env lean scratch/r17-bypass/Bypass.lean` | success, 11 s; only lint warnings of TailA's style (ambiguous `open`, `haveI`, `push_neg`); `afterG7_of3_levelLe` and `carayolR17'_of_newformRepConductor`: `[propext, Classical.choice, Quot.sound]` (`scratch/r17-bypass/Bypass-output.txt`) |
| discharge check | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.CarayolLevel`, then `lake env lean scratch/r17-bypass/DischargesCheck.lean` | see below (`scratch/r17-bypass/DischargesCheck-output.txt`) |
| fold | `python3 scripts/one_proof/autofold.py scratch/r17-bypass/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/r17-bypass/FoldDryRun.lean` | `strict count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11`; `sixContactMin_of_open29` compiles with standard axioms (71 s) |

`#discharges` (first entry; the other five are the already-folded contributions, as in the kit's
worked example):

```
DISCHARGES [OpenResearchLeaves21.r17] by CarayolLevel.carayolR17'_of_newformRepConductor
  still assumes: [CarayolLevel.NewformRepConductor]
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 63 open hypotheses, 1630 theorems checked, 6 discharge one
```

The autofold spec `scratch/r17-bypass/autofold.json` replaces `r17` by the leaf `newformRepConductor`
(kind `published`, flag `pending reading: …`, so it counts GLUE until read; the dry run confirms no
count change). The contribution imports kernel modules only, so the fold has no import cycle.

## 6. What remains

* A reading of the conductor packaging (Darmon–Diamond–Taylor 1997 §3.1, Carayol 1986 §0 for
  `F = ℚ`, or another survey) to clear the flag: then `newformRepConductor` is LEAF and the strict
  GLUE count drops by one. If no print states it, re-flag it as a consequence.
* The fold itself (integrator): `autofold.py scratch/r17-bypass/autofold.json`, the build, the hash
  guard and OPEN.md, as for every fold. Not done here (this task edits nothing outside
  `ZInQKernel/Contrib/OneProof/`).
* Not recommended: a bypass fold to `CarayolLevelLe` (no count change; would need the G0 term of
  `TailK.lean` restated).
* Side benefit: `condExp_eq_of_intertwine` and `iso_of_attached` are the transport step that the
  `eigenformHTNew` row also names ("transported to any semisimple attached rho"); the same pattern
  could give that field an existence form too (not attempted).
