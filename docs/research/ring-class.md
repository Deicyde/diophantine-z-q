# ring-class: Tau Ceti's ring class fields for TYZ's genus-point package

Task ring-class (2026-11-13). Groundwork for splitting `TYZGenusPackage`
(`ZInQKernel/Contrib/TYZDecomp/Leaves.lean`, `docs/research/tyz-decomp.md` §4.2), with tasks x0-32
and cm-points. All Lean is in new files under `ZInQKernel/Contrib/` (no existing file edited apart from
`ThirdParty/TauCeti/NOTICE`). Every declaration below compiles, with no `sorry`, and its
`#print axioms` is `[propext, Classical.choice, Quot.sound]` (VERIFIED: `scratch/ring-class/AuditBridge.lean`,
output in §6).

## 1. Main results

**(a) Two of cm-points' leaves are proved** (`ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean`):

```lean
theorem hprimeNormal : ZInQ.Contrib.TYZGenus.Package.HprimeNormal      -- H'_d / ℚ normal
theorem iInH4 : ZInQ.Contrib.TYZGenus.Package.IInH4                    -- i ∈ H_{n,4}
```

So cm-points' finest main theorem loses the hypotheses `IInH4` and `HprimeNormal`:

```lean
theorem tyzThm35ReadingA_of_cmLeaves_ringClass (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hs : TYZSigmaFixesZn)
    (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA
```

**(b) cm-points' general CM leaf now has its family `H` pinned.** `CM.CMFieldOfDefinition H` takes `H`
as a parameter, and its docstring says the family is "intended … provided by RingClass.lean".
`ringClassFieldD : ℤ → IntermediateField ℚ Qbar` is that family: the ring class field of the order of
discriminant `D`. It is Tau Ceti's `ringClassField` of `ℤ + f𝓞_K`, with `K = ℚ(√−sqfPart|D|)`,
`f = condD D`, and `condD_spec` (`|D| = f²|d_K|`). It is normal over ℚ (`normal_ringClassFieldD`)
and does not depend on the embedding (`ringClassFieldBar_eq_map`). It also takes the TYZ value
`ringClassFieldD (−64n) = H4bar n` (`ringClassFieldD_tyz`). Hence:

```lean
theorem cmFieldTYZ_of_ringClassD (h : CM.CMFieldOfDefinition ringClassFieldD) : CMFieldOfDefinitionTYZ
theorem tyzThm35ReadingA_of_cmLeaves_ringClassD (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CM.CMFieldOfDefinition ringClassFieldD) (hs : TYZSigmaFixesZn)
    (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA
```

TYZ's CM leaf (Shimura/Gross for the one form `[16(n+1), −8, 1]`) is thereby replaced by the textbook
statement for all Heegner forms of level 32. That statement is Gross, *Heegner points on X₀(N)* (1984)
§3, and Shimura 1971 Ch. 5–6; the section numbers are UNVERIFIED. The caveat in cm-points' docstring
still applies: for conductors that share a prime with `N` (`D = −64n`, `N = 32`), this is the
full-CM-point-set version of Shimura reciprocity, which TYZ use at L1203–1260.

**(c) Galois theory of ring class fields over ℚ** (`RingClassGalois.lean`):

* `le_of_splitSet_diff_subset` (**Bauer's theorem**, from Tau Ceti's Chebotarev density theorem). For finite
  Galois `E, E' ⊆ Kˢ`: if `splitSet K E \ T ⊆ splitSet K E'` with `T` finite, then `E' ≤ E`.
* `mem_splitSet_iff` (**splitting law**). For a prime `𝔭 = J` prime to the conductor, `𝔭` splits completely
  in the subfield of the ring class field cut out by `S ≤ Pic O` iff `O.picClass J ∈ S`.
* `picClass_conj`: complex conjugation inverts `Pic(ℤ + f𝓞_K)`.
* `normal_ringSubfield`: for every `S ≤ Pic(ℤ + f𝓞_{K_d})`, the subfield it cuts out is normal over ℚ
  (`Gal(H/ℚ)` is generalized dihedral; Cox, *Primes of the form x² + ny²*, Lemma 9.3, UNVERIFIED
  numbering). Consequences: `normal_Hprimebar d`, `normal_H4bar d`, `normal_ringClassFieldBar m f`,
  all unconditional.
* `adjI_le_H4 : adjI (QNeg d) ≤ H4 d` (`K_d(√−1) ⊆ H_{d,4}` for every `d ≥ 1`) and
  `iQ_mem_H4bar : d ≠ 0 → iQ ∈ H4bar d`. Proof: `K(√−1)/K` is unramified outside 2, by Tau Ceti's
  `natCast_mul_mem_differentIdeal_of_pow_eq`. A prime `𝔭 ∤ 2` that splits in `H_{d,4}` is `β𝓞_K` with
  `β ∈ ℤ + 4𝓞_K`, so `N𝔭 ≡ 1 (mod 4)` and its Frobenius fixes `√−1`. Bauer's theorem concludes.
* `H4bar_eq_map'`, `Hprimebar_eq_map'`, `ringClassFieldBar_eq_map`: the images in `ℚ̄` do not depend on
  the embedding `K_dˢ → ℚ̄`.

**(d) The definition of `H'_d` is TYZ's field** (`RingClassTwo.lean`).
`Hprime_sup_sqrt_two : d % 8 = 5 → Hprime d ⊔ adjSqrt (QNeg d) 2 = H4 d`. This is the first assertion
of TYZ Prop. 3.2(1), `H'_d(√2) = H_{d,4}`; the second, that `H'_d` is fixed by `σ_{1+2ϖ}`, is the
definition. Ingredients:
* `mem_splitSet_adjSqrt_iff`: `𝔭 ∌ 2a` splits completely in `K(√a)` iff `a` is a square mod `𝔭`.
* `adjSqrt_two_le_H4`: `√2 ∈ H_{d,4}` for `d ≡ 1 (mod 4)`.
* `exists_prime_picClass_eq`: every class of `Pic(O_{d,4})` contains a prime outside any finite set
  (Chebotarev).
* `not_adjSqrt_two_le_Hprime`: `√2 ∉ H'_d`.

**(e) The genus field explicitly** (`RingClassGenus.lean`). For squarefree `n ≡ 1 (mod 4)`:
* `adjSqrt_le_hilbertField`: `K_n(√−1)` and `K_n(√p)` (`p ∣ n`) lie in `H_n`. This is genus theory (Cox Thm 6.1,
  UNVERIFIED numbering), proved with quadratic reciprocity in the form `FiniteField.isSquare_odd_prime_iff`.
* `Lni_le_Hprimebar`: `L_n(i) ⊆ H'_n`.
* `HHprime_eq_iSup`: for squarefree `n ≡ 5 (mod 8)`, `ℍ'_n = ⨆_{d₀ ∣ n, d₀ ≡ 5 (8)} H'_{d₀}`. The factor
  `L_n(i)` in TYZ's L1320 is redundant.

**(f) `Cl'_d`, lifts of `2Cl`, class 7** (also `RingClassGenus.lean`):
* `artinPrime d : Pic (O4 d) ⧸ Subgroup.zpowers (sigmaClass d) ≃* Gal(Hprime d/QNeg d)` is the Artin
  isomorphism for `H'_d` (TYZ's `Cl'_d`). `artinPrime_mk_apply` shows it is the restriction of Tau Ceti's
  `ringClassArtinEquiv`. `card_artinPrime` gives its degree.
* `exists_lift_picSquares_O4 n`: there is `R ⊆ Pic(O_{n,4})²` that `Pic O_{n,4} → Cl(K_n)` maps
  bijectively onto `Cl(K_n)²`, with `#R = gCl n = g(n)`. Such sets are the candidates for TYZ's `Φ₀`.
  TYZ's exact definition of `Φ₀` ("`Φ₀ = Φ ∩ 2Cl′_n`", `rv-tyz-inputs.md` §1.3) is not recorded precisely
  enough on this host to pin cm-points' `Φ`.
* `ringClassFieldD_neg : d % 4 = 3 → Squarefree d → ringClassFieldD (−d) = ((hilbertField d).restrictScalars ℚ).map (embed d)`
  says that the field of TYZ's class-7 CM points (discriminant `−d`) is `H_d`.

## 2. The orders and fields TYZ uses (as quoted in the project notes; `Period7.tex` is not on this host)

| TYZ object | where (TYZ arXiv v1 lines, via notes) | Lean (`RingClass.lean`) |
|---|---|---|
| `K = ℚ(√−n)`, `n ≡ 5 (mod 8)` squarefree, `d_K = −4n` | §3, L1203–1205 (`tyz-t1.md` §3.1) | `QNeg n` |
| order `𝒪_{n,4} = ℤ[4√−n] = ℤ + 4𝓞_K`, disc `−64n` | L1203–1205 (Heegner point of `[16(n+1),−8,1]`) | `O4 n = conductorOrder (QNeg n) 4` |
| `H_{d,4}` ring class field of conductor 4 | Prop 3.2(1), L1253–1258 | `H4 d = ringClassField (O4 d)`, `H4bar d` |
| `σ_{1+2ϖ}`, `ϖ = 1+√−d` | L1255–1256, `rv-tyz-inputs` §1.5 | `sigmaClass d` (class of `(3+2√−d)`), `orderOf = 2` |
| `H'_d` (fixed by `σ_{1+2ϖ}`, `H'_d(√2) = H_{d,4}`) | Prop 3.2(1), L1255–1256 | `Hprime d`, `Hprimebar d`; `Hprime_sup_sqrt_two` |
| `L_n(i) = ℚ(i, √d : d ∣ n)` | L1322 | `Lni n` |
| `ℍ'_n = L_n(i)·Π_{d₀≡5} H'_{d₀}` | L1320 | `HHprime n`; `HHprime_eq_iSup` |
| `d ≡ 7`: maximal order, disc `−d` | `tyz-t1.md` §3.1 | `maximalNumberFieldOrder (QNeg d)`, `hilbertField d` |
| `g(e) = #2Cl(ℚ(√−e))` | L363 | `gCl e = #Pic² = [H_e : G_e]` (`gNat_eq_gRingClass`) |

All line numbers are quoted from the notes, not re-read (STANDARD-as-quoted).

## 3. Genus data in Tau Ceti's terms (from the first part of the task, `RingClass.lean`)

* `genusField O`: the fixed field of `Pic(O)²` in `ringClassField O`. `finrank_genusField`:
  `[G : K] = #Pic(O)[2]`. `relfinrank_genusField`: `[H : G] = #Pic(O)²`.
* `finrank_genusField_eq`: `[G_n : K_n] = 2^{t−1}` (`t = #ramSet n`) for odd squarefree `n > 1`.
* `genusField_eq_fixedField_chi`: the genus field is the field cut out by the genus characters
  `RouteK.Redei.chi`.
* `PropN.GenusData`'s only class-group input is `gNat`, and `gNat_eq_gRingClass : PropN.gNat = gRingClass`
  (`[H_e : G_e]`). Also `T5aCl_eq_gRingClass`, `T5bCl_eq_gRingClass`, `GenusData.beta_five_ringClass`,
  `GenusData.beta_seven_ringClass`.
* `relfinrank_Hprime : d % 8 = 5 → [H_{d,4} : H'_d] = 2`. `hilbertField_le_Hprime : H_d ≤ H'_d`.
  `restrict_ringClassArtinEquiv`: Artin symbols are compatible with `Pic O → Cl(K)`.

## 4. Files

* `ZInQKernel/Contrib/TYZGenus/RingClass.lean`: definitions, Artin isomorphism `artin4`, genus field,
  `GenusData` bridges.
* `ZInQKernel/Contrib/TYZGenus/RingClassGalois.lean`: Bauer's theorem, splitting law, normality, `i ∈ H_{d,4}`,
  ring class fields by discriminant, embedding independence.
* `ZInQKernel/Contrib/TYZGenus/RingClassTwo.lean`: `K(√a)` splitting, Chebotarev primes in Picard classes,
  `H'_d(√2) = H_{d,4}`.
* `ZInQKernel/Contrib/TYZGenus/RingClassGenus.lean`: `L_n(i) ⊆ H_n ⊆ H'_n`, `ℍ'_n = ⨆ H'_{d₀}`, `artinPrime`,
  lifts of `2Cl`, `ringClassFieldD_neg`.
* `ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean`: proofs of cm-points' `HprimeNormal` and `IInH4`, and
  the main-theorem variants.
* Vendored Tau Ceti (earlier in this task): the `RingClass.Field` closure, `RayClassField`,
  `Narrow/NarrowClassGroup`, and 10 `Backport/` files (see `ThirdParty/TauCeti/NOTICE`).
  `diffcheck2`: MOD-UNNOTED 0, NOTE-ONLY 0 (VERIFIED, 2026-11-13).

Build: `lake build ZInQKernel.Contrib.TYZGenus.RingClassBridge ZInQKernel.Contrib.TYZGenus.RingClassGenus`
(VERIFIED, success).

## 5. What remains / caveats

* The remaining cm-points leaves are not ring-class-field statements and are not addressed here:
  `CM.CMFieldOfDefinition ringClassFieldD` (Gross/Shimura), `TYZSigmaFixesZn` (TYZ Cor. 3.9),
  `Lemma318Literal HHprime` (torsion of `A(ℍ'_n)`) and `GenusPointLeafCM`. `HHprime_eq_iSup` may help with
  Lemma 3.18, since `ℍ'_n` is a compositum of the `H'_{d₀}`.
* Caveats stay: reading A is not printed in any refereed text; TYZ was read in arXiv v1 only;
  Proposition N is AI-reviewed only. The TYZ line numbers are quoted from project notes.
* Proposals: none of the existing statements is wrong. cm-points could drop `HprimeNormal` and
  `IInH4` from its leaf list, now that `RingClassBridge.hprimeNormal`/`iInH4` prove them. It could also
  restate `CMFieldOfDefinitionTYZ` as `CM.CMFieldOfDefinition ringClassFieldD` (via
  `cmFieldTYZ_of_ringClassD`).

## 6. `#print axioms` (VERIFIED, `lake env lean scratch/ring-class/AuditBridge.lean`)

```
'ZInQ.Contrib.TYZGenus.RingClassBridge.hprimeNormal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClassBridge.iInH4' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.adjI_le_H4' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.normal_ringSubfield' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.le_of_splitSet_diff_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClassBridge.cmFieldTYZ_of_ringClassD' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClassBridge.normalFields_HHprime'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.ringClassFieldD_tyz' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.condD_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.normal_ringClassFieldD' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.Hprime_sup_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.exists_prime_picClass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.mem_splitSet_adjSqrt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.H4bar_eq_map'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.adjSqrt_le_hilbertField' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.Lni_le_Hprimebar' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.HHprime_eq_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.exists_lift_picSquares_O4' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.ringClassFieldD_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.artinPrime_mk_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZGenus.RingClass.card_artinPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(The round-1–3 declarations of `RingClass.lean`, such as `orderOf_sigmaClass`, were checked the same way;
see `scratch/ring-class/log.md`.)
