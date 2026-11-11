# h-b1-fix: report

**Result.** All six repairs of `docs/research/rv-h-b1.md` §8 are now in `docs/research/h-b1.md`.
The changelog at the end of that note lists them, and the work log is `scratch/h-b1-fix/log.md`.
No other note was edited, and nothing under `ZInQKernel/` or `blueprint/` was touched.

**Repairs made**
1. Replacement table:
   - Corrected the locator L563-566 to L557-558.
   - Added L752-753 and L778-781.
   - Named all downstream uses of good reduction (L557-558, L752-753, L781, L848-849).
   - Kept the finding that L814 never used b11.
   - I re-read every locator in the frozen N5.
2. NV step 3 now has the full argument: residue degree 1 equals `[I_𝔓 : I_{Q_i}]`, plus going-down and `I_q ⊂ I_𝔓`. Prop. TS now also states finiteness (excellence) and flatness (normal of dimension 2 over a regular base).
3. M9 and NV step 2:
   - Step 2 now says "conductor prime to `p`".
   - Added the complete list of elliptic types (rv R2). The CM orders have discriminant −3, −4 and −24, all maximal, with their `W`-images. Type (0,2) does not occur.
4. Summary item 1: F1 shows that unramified branch fibres are not enough, so the `W`-step is essential.
5. New §4A on the one ℚ-structure on `Y₃ = Sh_{K₃}` that NV, PR(ii) and Baba–Granath's `j` must share. It cites four standard inputs, each marked UNVERIFIED with where to check it:
   - Shimura 1967, Deligne Bourbaki 389 §4-6, Milne §8/§14 and Kottwitz: the canonical model equals the moduli space.
   - Rotger 2003/2004: the μ-principal polarization is unique.
   - The Weil-pairing similitude `ψ(xu, yu) = nrd(u)ψ(x, y)`.
   - Level-3 rigidity (Serre's lemma, Mumford §21).
6. Optional repair: the `W`-layer check (Elkies' constants −1 and 3, rv R7) is recorded as independent support for NV.

**Not repaired**
- Every literature locator is still unread, because there was no network: Shimura, Deligne, Milne, Kottwitz, Rotger, Mumford, Baba–Granath §2-3, EGA IV, SGA 1/7, Serre–Tate and Beckmann.
- The Rotger statement is written as an expectation: "exactly one principal polarization of this Rosati type for disc 6". It must be checked against the papers.
- Lemma NV and Prop. TS are still PROVED HERE, reviewed only by rv-h-b1.

**Scripts.** Both were rerun with `~/pyenv/bin/python`, and both outputs are byte-identical to the saved ones:
- `scratch/h-b1/b1_checks.py`: 0.85 s.
- `scratch/rv-h-b1/rv_checks.py`: 1.26 s.

Copies of the outputs are in `scratch/h-b1-fix/`. No Lean was run.
