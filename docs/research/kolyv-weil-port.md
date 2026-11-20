# Port of the pole-completeness rank supplier

The headline change is prepared on `96649019f`: replace `hB` and `hK` by
`hB6 : KolyvWeil.BCDTThmA6` and `hKPrint : KolyvWeil.KolyvaginThm1Print`.
The baseline build is in progress. Both replacement hypotheses are rated GLUE
in both columns under the current rule.

**VERIFIED (source and Git).** Merge `eab2f0277` brings in `8555b8d78`
without conflicts or edits to existing files. The predecessor splice was
prepared against `dcc3d7723`, where the H chain ends at `TailZ91` and
`sixContactMin_of_open84`. The port retains `TailZ93`,
`sixContactMin_of_open86 r t l` and the current H bundles. It also keeps the
recognition of Theorem 5.3 as the manuscript's own theorem. Fork PR #110
added a separate reduction of Theorem 5.3; the headline still assumes
`hRC : SelmerTwoPower.RestrictedConverseGenuine` and
`hCT : PoleS12.CasselsTatePairingCurves`. The existing restricted-converse
and Lemma 5.4 interfaces used by the pole supplier are unchanged.

The rank supplier specializes the printed result at analytic rank one,
giving it the conductor-level weak Weil map from `hB6`. The old `hK`
follows from these two premises without using its cusp form argument; the
pole proof needs only the rank projection. The old `hB` leaves the
headline because it only supplied that argument. The pairing still gives
Lemma 5.4, and the same descent proves pole completeness.

## Known issues

- **VERIFIED (recorded print reading).** BCDT's cited author manuscript,
  Theorem A (p. 1) and Introduction condition (6) (p. 3), gives the map
  from `X₁(N_E)`. The conductor-level map used here is from `X₀(N_E)`.
  **STANDARD:** trivial nebentypus, Shimura's `J₀(N_E)` quotient and Faltings'
  isogeny theorem give the realization, as recorded for Milne's *Modular
  functions and modular forms*, v1.31, Remark 11.18 and Theorem 11.19, p. 117.
  That consequence remains assumed as `hB6`.
- **VERIFIED (recorded print reading).** Kolyvagin's MPI/90-69 (1990),
  Theorem 1, is on printed p. 4 with its weak Weil hypothesis on p. 3.
  The Lean statement keeps both analytic rank cases and finiteness of the
  full Shafarevich–Tate group. The cited preprint is unrefereed. A ruling
  admitting it changes the rating; the Lean proof needs no change.

The print locators are from the [earlier fold report](kolyv-weil-fold.md#known-issues)
and its cited page audit; the prints were not reread for this port.

## Counts

**VERIFIED (board table and the recorded replacement ratings).** Both strict
and strictest use the same counts for the present ruling. Each cell gives
LEAF / GLUE.

| Scenario | H (29) | Other headline inputs (4) | Total (33) |
| --- | ---: | ---: | ---: |
| Before, both columns | 5 / 24 | 1 / 3 | 6 / 27 |
| After, both columns under the current rule | 5 / 24 | 1 / 3 | 6 / 27 |
| After, in any column that admits the preprint | 5 / 24 | 2 / 2 | 7 / 26 |

If the lead admits the preprint only in strict, strictest retains 6 / 27.

## Manuscript check

Line numbers below refer to [diophantine_zq.tex](../../diophantine_zq.tex).
The check is confined to the existing descent interface and the replaced
rank step.

| Lines | Verdict | Check |
| --- | --- | --- |
| L1001–1004 | OK | The pole-completeness conclusion is the existing one for the manuscript's pole polynomial. |
| L1005–1011 | OK | The unchanged input states the restricted converse on the specified squarefree family over the genuine two-power Selmer group. Its proof is outside this port. |
| L1019–1070 | OK | The existing descent supplies the simultaneous two-Selmer count on the two admissible curves. This part uses the same matrix and local arguments as before. |
| L1072–1084 | OK | The unchanged Lemma 5.4 argument combines the finite Kummer count with the alternating pairing on the quotient by the divisible subgroup. |
| L1086–1090 | OK | The printed result gives the rank and full Sha conclusions for analytic ranks zero and one. The pole argument specializes to rank one. |
| L1092–1093 | gap filled | The direct citation leaves Kolyvagin's `X₀(N_E)` parametrization implicit. L1779–1786 supplies the realization; the Lean interface exposes that bridge as `hB6`. |
| L1093–1097 | OK | The cited Theorem 1 already gives the required rank and finiteness over ℚ; the port invokes it directly as `hKPrint`. The auxiliary-field argument is covered by the prior audit. |
| L1098–1104 | OK | The ordinary Kummer sequence gives the corank from the rank once Sha is finite. The pole proof only reads the rank. |
| L1111–1113 | gap filled | Rank one and finiteness alone do not imply `Sha[2] = 0`. The finite Kummer count at L1077 gives it from rank one; the existing Lean descent already uses that count. |
| L1114–1121 | OK | The existing proof represents the Kummer classes by points and assembles the witnesses using the same descent. |
| L1779–1784 | OK | The manuscript records the rational newform and elliptic quotient of `J₀(N_E)` in the isogeny class of the actual curve, citing Milne. |
| L1785–1786 | OK | Composing with the isogeny and the based Jacobian map gives the conductor-level weak Weil map used at L1093. |
| L11150–11157, L11163–11167 | OK | The bibliography on this base gives the BCDT author manuscript, the Milne edition, and the correct Kolyvagin preprint and identifier. |
