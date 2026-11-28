# `deligneCanonicalModelY3EveryPrint`: identifications with Deligne's PEL datum

Reading packet for the three-lens reading of the hypothesis
`HDec.HSyn.OpenResearchLeaves78.deligneCanonicalModelY3EveryPrint`, Lean statement
`Y3Hodge.DeligneCanonicalModelY3EveryPrint` (`ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean`).
It is no longer open: y3-deligne-1127 (`ZInQKernel/OneProof/H/TailZ112.lean`) replaced the field
by three rows, and y3-milne-1128 (`TailZ116.lean`) now fills it by
`DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne` from the five rows
`voightQMComplexModuliPrint`, `boutotCarayolPolarizationPrint`,
`boutotCarayolRepresentabilityPrint`, `milneShimuraFamilyPrint` and `milneCanonicalModelPrint`.

**What this directory is.** Proved identifications between the objects in the Lean statement and
the objects of the print, plus the leaf restated with the print's objects and proved equivalent
to it (`DeligneY3Bridges.PEL.print_iff_PEL`). It does **not** prove the hypothesis: the
discharge check lists `print_of_PEL` because its conclusion is the hypothesis, and it still
assumes `DeligneCanonicalModelY3EveryPEL`, which is the same statement in the print's notation.
No field is discharged and nothing is folded.

## Source

P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki 23e année (1970/71), exposé 389,
Lecture Notes in Math. 244, pp. 123–165. Legal copy: numdam, `SB_1970-1971__13__123_0.pdf`
(44 pages; pdf page N is printed page N + 121), SHA-256
`054847cecac9c396e2a6f568443db180786a0c5528ec08530fd464d5474bd534`.
The text layer is degraded: read the page images. Pages 148 and 149 were re-read as images for
this packet, and page 129 for 1.7–1.8. The other locators follow the statement-check sweep of
2026-11-18 (AI-READ, same copy and SHA-256; commit b1a8d27e7,
`docs/one-proof/statement-checks/deligneCanonicalModelY3EveryPrint-sweep-20261118.md`),
which read §1.2, §§1.5–1.12, §§3.13–3.15, §§4.9–4.12, §§4.15–4.17, Thm 4.21, Cor.
5.5–5.7 and Ex. 5.8. Rows below marked UNVERIFIED are outside that list and outside the pages
re-read here. All readings here are AI-READ evidence.

Locators used (printed pages):

| locator | page | what it says (quote or summary) |
|---|---|---|
| 1.7 | 128–129 | "Soit K_n le sous-groupe compact ouvert de G(𝔸^f) formé des k = (k_p) tels que k_p · V_ℤ ⊗ ℤ_p = V_ℤ ⊗ ℤ_p et que k_p ≡ 1 (mod n) pour p \| n" |
| 1.8 | 129 | "Soit K un sous-groupe compact ouvert de G(𝔸^f). L'espace K_∞ × K\G(𝔸)/G(ℚ) = K\X × G(𝔸^f)/G(ℚ) = X × (K\G(𝔸^f))/G(ℚ) […] On le notera _K M_ℂ(G, h₀)" |
| 4.9 | 147 | the PEL datum `(L, V, ψ)`; `G` = the `L`-linear symplectic similitudes of `(V, ψ)` |
| Thm 4.7 (Riemann) | 146 | polarized abelian varieties ↔ `(V, ψ, V_ℤ, h)` (UNVERIFIED) |
| Scholie 4.11 | 148 | "Les points de `_K M_ℂ(G, h₀)` correspondent bijectivement aux classes d'isomorphie de variétés abéliennes à isogénie près A, munies de (a) ρ : L → End(A) tel que Tr(ρ(ℓ), Lie(A)) = t(ℓ), (b) une polarisation homogène p̄ qui induise l'involution donnée de L, (c) une classe mod K, k̄, de similitudes symplectiques L-linéaires k : V̂(A) ≅ V ⊗ 𝔸^f, et telles que (*) les conditions (4.10.1) (4.10.2) soient vérifiées." |
| 4.12 | 148–149 | "Soient K un sous-groupe compact ouvert de G(𝔸^f), V_ℤ un réseau entier dans V tel que V̂_ℤ = V_ℤ ⊗ Ẑ soit K-invariant, L_ℤ un ordre de L tel que L_ℤ V_ℤ ⊂ V_ℤ, ψ_ℤ un multiple rationnel positif de la forme alternée de V, à valeurs entières sur V_ℤ […] Soient n un entier, et K_n = {g ∈ G(𝔸^f) \| (g−1) V̂_ℤ ⊂ n V̂_ℤ}. On suppose n assez grand pour que K ⊃ K_n." Then `T̂(B) = k⁻¹(V̂_ℤ)` and the points as `(B, p, ρ, k̄_n)` |
| 4.16–Prop. 4.17 | 150 | Mumford's moduli scheme of principally polarized abelian schemes with symplectic level `n ≥ 3` is a model |
| Thm 4.19 | 151 | Shimura–Taniyama; "On renvoie à [16] pour la démonstration" (locator and quote UNVERIFIED) |
| Thm 4.21 | 152 | the model of 4.17 is canonical (proof: "oubli de la multiplication complexe" and Mumford [8]; the proof paraphrase is UNVERIFIED) |
| Cor. 5.7 | 156 | canonical models for sub-data, proof via 5.1–5.3 |
| Ex. 5.8 | 157 | "Pour (G, h₀) comme en 4.9, on construit par 5.7 et 4.21 un modèle canonique M(G°, h₀) ⊂ M(Gp(V, ψ), h₀) ⊗_ℚ E(G°, h°)" |
| 6.3–Thm 6.4 | 160–161 | the quaternionic case over a totally real `F`; for `F = ℚ`, `E(G, h₀) = ℚ` (UNVERIFIED) |

## The PEL datum of the kernel

`L = B = (2, −3 | ℚ)` (`LeafQM.B`, Mathlib's `QuaternionAlgebra ℚ 2 0 (−3)`), `V = B` with `B`
acting by left multiplication, involution `x† = μ⁻¹ x̄ μ` with `μ = 2j + k`
(`RvQMPolar.dag`), `ψ(x, y) = trd(μ⁻¹ x ȳ)` (`RvQMPolar.E0`), `V_ℤ = L_ℤ = 𝒪` (the maximal order
`LeafQM.O`), `ψ_ℤ = ψ` (integral on `𝒪`: `Y3Hodge.E0_intO`; unimodular: `RvQMPolar.gram_det`),
`K = K₃`.

| print object | Lean object | identification (proved) |
|---|---|---|
| `ψ` (4.9) | `DeligneY3Bridges.psi ℚ` | `PEL.psi_rat : psi ℚ = RvQMPolar.E0`; alternating `PEL.psi_alt`; adjoint `†` `PEL.psi_rosati` |
| `G(R)`, `R` a `ℚ`-algebra (4.9; 4.11 (c)) | `DeligneY3Bridges.simGroup R` | `simEquiv R : (B ⊗ R)^× ≃* G(R)`, `γ ↦ (x ↦ x γ⁻¹)`; `mem_simGroup_iff` (every element is a right multiplication); multiplier `nrd(γ)⁻¹` (`psi_simEquiv`, `PEL.psi_toGQ`) |
| `G(ℚ)` | `PEL.GQ` | `PEL.toGQ : B^× ≃* G(ℚ)` |
| `G(𝔸_f)` | `PEL.GAf` | `PEL.toGAf : (B ⊗ 𝔸_f)^× ≃* G(𝔸_f)` (the kernel's `BAQˣ`) |
| `G(ℚ) ⊂ G(𝔸_f)` | `PEL.baseChange` | unique extension along `B ⊂ B ⊗ 𝔸_f` (`PEL.eq_baseChange_iff`); `baseChange (toGQ γ) = toGAf (bEmb γ)` (`PEL.baseChange_toGQ`) |
| `V̂_ℤ = 𝒪 ⊗ Ẑ` (4.12) | `PEL.VZhat = OhatQ` | definition |
| `G(Ẑ)` (stabilizer of `V̂_ℤ`) | `PEL.GZhat` | `PEL.mem_OhatU_iff : u ∈ OhatU ↔ toGAf u ∈ G(Ẑ)` |
| `K_3` (4.12) | `IsCongr VZhat 3` | `PEL.mem_K3Q_iff : k ∈ K3Q ↔ toGAf k ∈ G(Ẑ) ∩ K_3` (`DeligneY3Bridges.level_iff`) |
| level datum `k̄`, symplectic and `L`-linear (4.11 (c)) | the kernel's `𝒪`-linear `LevelPrint` | `LevelCompat.eq_smul_E0K`, `LevelCompat.level_similitude`: over every field of characteristic 0 (each `ℚ_ℓ`), a `B`-linear isomorphism to a space whose alternating form has adjoint `†` multiplies the forms by one scalar, nonzero if the form is not zero |

## Clause map

The Lean statement (`Y3HodgePrint.lean`, `DeligneCanonicalModelY3EveryPrint`):

```lean
∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), Y3Fix.R1fpPropsAbP Y Φ →
  ∃ Ψ, DeligneBodyAtPM Y Φ Ψ ∧ ModuliAtUnitsHP Y Φ Ψ
```

`DeligneY3Bridges.PEL.DeligneCanonicalModelY3EveryPEL` is the same text with `G(𝔸_f)`,
`DCRelPEL`, `G(Ẑ)` in place of `(B ⊗ 𝔸_f)^×`, `DCRelPM`, `OhatU`; `print_iff_PEL` proves the
two equivalent. `DCRelPEL` puts `G(ℚ)` on the left and `K` on the right, like the kernel;
Deligne's 1.8 puts `K` on the left and `G(ℚ)` on the right (`DCRelDel`), and `dcRelDel_iff_PM`
proves that the two agree after `g ↦ g⁻¹`.

| # | Lean clause | print (page, quote) | Lean theorem identifying it | rating to check |
|---|---|---|---|---|
| W | every witness `(Y, Φ)` of `Y3Fix.R1fpPropsAbP` | Ex. 5.8 p.157: "on construit par 5.7 et 4.21 un modèle canonique M(G°,h₀) ⊂ M(Gp(V,ψ),h₀) ⊗_ℚ E(G°,h°)"; Scholie 4.11 p.148 (points = PEL data) | any two witnesses are isomorphic compatibly with `Φ`: `Y3Fix.compare_iso_np` (with `Y3Fix.np_of_P`), already proved | reading steps R1 and R2 below |
| 1 | `Ψ` onto `Y(ℂ)` | 1.8 p.129 and the model structure `M(ℂ) = Sh_K(ℂ)` | `toGAf` is a bijection (`PEL.print_of_PEL`, `PEL.PEL_of_print`) | match |
| 2 | `Ψ z g = Ψ z' g' ↔ DCRelPM z g z' g'` (`γ ∈ B`, `nrd γ ≠ 0`, `k ∈ K3Q`) | 1.8 p.129: "K\X × G(𝔸^f)/G(ℚ)"; 4.9 (`G`); 1.7 p.129 and 4.12 p.148 (`K_n`) | `PEL.dcRelPEL_iff` (`γ ∈ B^× ↔ G(ℚ)`, `bEmb ↔ baseChange`, `K3Q ↔ G(Ẑ) ∩ K_3`); Deligne's side convention: `PEL.dcRelDel_iff_PM` (`g ↦ g⁻¹`); `X = ℍ^±` with the `GL₂(ℝ)` action: `Y3Hodge.iota_mul_Jmat`, `Y3Hodge.F0_iff`; restriction to `ℍ`: `Y3Hodge.dcRelPM_iff`, `Y3Hodge.exists_upper` | match after the identifications; the level is `K = G(Ẑ) ∩ K_3` (step R3) |
| 3 | `τ ↦ Ψ(τ, g)` holomorphic on `ℍ` for every `g` | 1.8 p.129: `_K M_ℂ` is a complex-analytic quotient | none needed | weaker than the print (it gives a biholomorphism) |
| 4 | at `g = 1`: `IsShimuraHolFamilyHP` (fibres in `IsHodgeH1Print` form) | Scholie 4.11 p.148 and 4.12 p.148–149: `H₁(A, ℚ) ≅ V` as `L`-module with `h`; `T̂(B) = k⁻¹(V̂_ℤ)` | `Y3Hodge.print_iff_hodge`, `Y3Hodge.lemmaP_H1`, `Y3Hodge.F0_iff` (already proved) | match on `H₁`; polarization and level dropped (weaker) |
| 5 | reciprocity at CM points, `ε`, `δ` existential | Def. 3.13 (canonical model) and Thm 4.19 p.151 | `toGAf` is a group isomorphism (`map_mul` in `PEL.print_of_PEL`) | weaker (existential conventions, CM points of `ℍ` only); **D2 open**: 4.19 is cited, not proved, in the print, and Shimura–Taniyama [16] must be read in the original |
| U | `ModuliAtUnitsHP`: at `u ∈ OhatU`, `IsHodgeH1Print` | 4.12 p.148–149: `T̂(B) = k⁻¹(V̂_ℤ)`, i.e. `H₁ = L_g = B ∩ 𝒪̂ g⁻¹` | `PEL.mem_OhatU_iff` (`OhatU ↔ G(Ẑ)`); `Y3Lattice412.latticeAt_eq_deligne` (`L_g = B ∩ k⁻¹(V̂_ℤ)` for Deligne's `k = toGAf g⁻¹`); `Y3Lattice412.latticeAt_of_mem_OhatU` (`L_u = 𝒪` for `u ∈ 𝒪̂^×`); `Y3Lattice412.latticeAt_dc` (`L_{γgk} = L_g γ⁻¹`); `Y3Lattice412.latticeAt_basis` (full `𝒪`-lattice); `Y3Lattice412.moduliAtUnitsHP_of_lattice` (the print's description in `L_g` form, `ModuliAtLattice`, implies the clause; `isHodgeH1PrintAt_O_iff` checks the generalization at `L = 𝒪`) | match on `H₁`; polarization and level dropped (weaker); the existence of `B` with `T̂(B) = k⁻¹(V̂_ℤ)` in each isogeny class is asserted in 4.12, not proved in Lean (`docs/research/y3-412-lattice.md`, part C) |

No clause is stronger than the print once the identifications are applied: `print_iff_PEL` is an
equivalence, and clauses 3, 4, 5 and U are weakenings of the print's statements.

## Reading steps (not provable in Lean today)

* **R1. Polarized versus polarization-free moduli.** The print's model `M(G, h₀)` (4.17, 4.21,
  Ex. 5.8) represents the *polarized* PEL problem (Scholie 4.11 (b), 4.12 (a)); the Lean witness
  `Y3Fix.R1fpPropsAbP` represents the *polarization-free* problem (`QMAbSchemeP` carries no
  polarization). The reading must accept that the two problems agree: over `ℂ` by Lemma P on
  `H₁` (`Y3Hodge.lemmaP_H1`, proved: the principal polarization inducing `†` is unique and
  automatic) together with Riemann's theorem 4.7; over a base by the relative Lemma P
  (printed in Buzzard, Duke Math. J. 87 (1997), §1, not part of this packet). This comparison is
  argued in the reading only; it is not attempted in Lean (Mathlib has no dual abelian scheme).
* **R2. The print's model is a witness.** Given R1, the print's `M(G, h₀)_K` carries the
  universal object of the polarization-free problem, so it is a witness of
  `Y3Fix.R1fpPropsAbP`; `Y3Fix.compare_iso_np` then transports the print's statement to every
  witness. The map `M → Y` cannot be built in Lean (no Shimura varieties in Mathlib).
* **R3. The level group.** 4.12 takes `K` compact open with `V̂_ℤ` `K`-invariant and `K ⊃ K_n`,
  `K_n = {g ∈ G(𝔸^f) | (g − 1) V̂_ℤ ⊂ n V̂_ℤ}`. The kernel's `K3Q` is `G(Ẑ) ∩ K_3`
  (`PEL.mem_K3Q_iff`), which is the group `K_3` of 1.7 (p.129: `k_p V_ℤ ⊗ ℤ_p = V_ℤ ⊗ ℤ_p` and
  `k_p ≡ 1 (mod 3)` for `p | 3`). Read literally, the set of 4.12 is not inside `G(Ẑ)`; the reader
  takes `K = G(Ẑ) ∩ K_3`, which is compact open and fixes `V̂_ℤ`.
* **R4. Level structures.** The print's `k̄` is a class of `L`-linear *symplectic* similitudes;
  the kernel's `LevelPrint` is `𝒪`-linear only. `LevelCompat.level_similitude` proves the
  algebraic half (at each `ℓ`, a `B`-linear isomorphism respects the forms up to one scalar);
  that the Weil pairing of the canonical polarization has adjoint `†` is a reading step.
* **D2 (open).** The print does not prove Thm 4.19: it refers it to Shimura–Taniyama [16]
  ("On renvoie à [16] pour la démonstration"; quote UNVERIFIED, see the locator table), and the
  last step of Thm 4.21 rests on Mumford [8] (UNVERIFIED).
  A statement that a paper only cites must be read in the original source, so Shimura–Taniyama
  [16] (for Thm 4.19) and Mumford [8] (for the last step of 4.21) must be read in the original.
  D2 stays open until then.

## Files

* `Similitude.lean` (Mathlib only): `QB R`, `psi`, `nrd`, `simGroup`, `simEquiv`,
  `mem_simGroup_iff`, `psi_simEquiv`, `baseChangeOf`, `IsStab`, `IsCongr`, `unit_iff`,
  `level_iff`, `rel_inv_iff`.
* `LevelCompat.lean` (Mathlib only): `eq_smul_E0K` (ported from the branch
  `wip/y3abu-strict`, head `e0197d03acee9946ebfa74617cf661ec77238665`, file
  `ZInQKernel/Contrib/OneProof/ShimuraY3StrictLemmaP.lean`, section `LevelCompat`),
  `psi_eq_E0K`, `level_similitude`.
* `Statement.lean`: the identifications at `ℚ` and `𝔸_f`, `DCRelPEL`, `DCRelDel`, the PEL form of
  the leaf and `print_iff_PEL`.
* `Check.lean`: `#print axioms` for the main theorems.
