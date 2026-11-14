# hodge-split (2026-11-14)

**Result.** Of the seven p-adic Hodge theory rows of frontier r3, five are now Lean theorems from
published-form leaves only. H-52 `FiniteImageHT`, H-32 T23, H-8 R10 amended, H-22 `R14Det` and
H-51 `SenTwist` follow from seven leaves:
- Tate 1967 §3.3 Thms 1–2 (`AxSenTate`, `TateTwistInvariants`);
- the Hodge–Tate decomposition of `V_p(A)` (Fontaine 1982);
- the de Rham property of `H¹ = V_p(A)^∨` with the printed `D_dR`;
- `B_dR^{G_ℚp} = ℚ_p` (Fontaine); Fontaine's Tannakian theorem for `B_dR`, which T23 is, is proved
  from it;
- Diamond–Shurman Thms 9.6.5 (Deligne) and 9.6.6 (Deligne–Serre).

H-10 `EigenformHT` is a theorem from its newform case `EigenformHTNew` (Kato's theorem, transported and
dualized), the kernel's leaf I4-L5 and the two DS leaves. Kato's `V_{F_λ}(f)` is not definable in Mathlib
(étale cohomology), so that case cannot be a leaf today. H-9 `PanBerger` cannot be split: Pan's and
Berger's theorems need `B_st`, which Mathlib lacks; `panBerger_of_templates` shows the row is their
composite for every predicate `IsPst`. No row statement was changed or found false.

**What compiles.** `scratch/hodge-split/HodgeSplit.lean`, one file, about 45 s after building the
imported modules; standard axioms only. Main theorem `hodge_rows_of_leaves`. All the glue the splits
introduced is proved:
- SenTwist via Tate–Sen independence and Dedekind coordinates, with no Sen operator;
- semisimplification, the determinant from Frobenius values (T18), Artin transport (Nullstellensatz,
  Maschke);
- Chebotarev with Brauer–Nesbitt (`AttachedConj`);
- coefficient-field independence of `htMult` and g12-det's `HTConj`.

Report: `docs/research/hodge-split.md`. Log: `scratch/hodge-split/log.md`.

**What remains.** H-10's newform case (Kato) and H-9 (Pan and Berger) wait for étale cohomology and
`B_st` in Mathlib. All theorem numbers are UNVERIFIED (no network on this host).
