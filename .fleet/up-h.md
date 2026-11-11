# up-h: the H side of upstream Versions 13–16 and p214

The full note is `docs/research/up-h.md`. The log and script are in `scratch/up-h/`.

**Verdict.** No upstream version lets the fork narrow or remove `SixContactMin`.
- **The theorem is unchanged (VERIFIED, `checks.py`).** Theorem 4.1's statement and constants
  are identical in N5 and V13-V16.
- **The fork's target still uses it.** V16's 292,890,231,905-variable target is still proved
  from it (V16 L219).
- **Only V14 changed the proof.** V13 is N5. V14 rewrote the proof. V15 changed five lines,
  replacing the `b11` supplement by in-manuscript sections (V16 L30096-30122). V16's height
  section is byte-identical to V15's.
- **The new estimates concern another curve.** The sharper estimates in V15/V16 (exponents 24,
  19, then 3·(1+log)) and p214's (exponent 2103/1024) are five-contact estimates on the
  discriminant-210 Shimura curve, for the quartics. They use the same chain: QM surface,
  modularity, conductor, `J₁(N)`, isogeny. Nothing replaces the bound by a finite computation
  or a published theorem.
- **Gaudron–Rémond.** V16's "two corrected Gaudron–Rémond citations" (V16 L30664, L30677) are in
  that five-contact section. Upstream explicitly keeps the Duke citations of Theorem 4.1's proof
  (Thm 1.4 and §9, V16 L1599, L1616), so h-trust's steps E3 and E4 are unaffected.

**Most important finding.**
- **Upstream fixed some gaps the fork's reviews found (V14 on):**
  - C8: the normalization of `ρ_g`, weight one, and levels divisible by 5, through Kato 2004
    §9.4 and Deligne–Serre. The twist is also shown finite by a determinant argument, so
    local algebraicity is no longer needed.
  - C3: the restriction step R1 is avoided by choosing `F` Galois, and the Fontaine exposé is
    cited.
  - A9: Milne's course notes are replaced by Milne 2005.
- **Upstream kept others verbatim:**
  - C9's Euler-factor inference (V16 L1468-1474 = N5 L769-775);
  - A9's implicit descent;
  - the CM branch, which NoCM replaces;
  - rv-h-novel R2-R3;
  - uncited I2 and `ℓ`-independence.
- **Upstream added dependencies the fork avoids:** a survey statement in place of Pan, and four
  project supplements.

So h-trust's proof is already stronger than every upstream version where they differ. Its C9
repair, NoCM and Lemma PR remain necessary.

**Single next step.** Make an h-trust amendment, "h-v16-adopt", with a short model review:
- C8: replace the local-algebraicity step by V14's determinant argument (V16 L660-667). This
  drops the `conrad-local-characters` row of h-trust §2.4. Add Kato 2004 §9.4 as an all-levels
  supplier for (HT).
- C3: choose `F` Galois, which makes R1 unnecessary, and cite Fontaine, Astérisque 223,
  pp. 113-184, Thm 3.8.
- A4: import V16's Deligne 1971 locators.
- E4: add CMH 2014 §2.3 as a second locator.

Success criterion: no constant or Lean statement changes, one §2.4 row disappears, and the
review finds the C8 replacement sound.
