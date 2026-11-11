# rv-up: adversarial check of up-map, up-h, up-cr3, up-rest

Full note: `docs/research/rv-up.md`. Log and scripts: `scratch/rv-up/`.

**Verdicts.**
1. **CONFIRMED.**
   - Thm 1.1/1.3, Thm 4.1/4.2 with its constants, PC with the template x+3ℓ, RC, 22P, the
     catalogue, the literal cutoff, the assembly lemma, the generator certificate and the finite
     box are byte-identical in N5 and V16, by my own script.
   - §§9-12 are identical (N5 4382-6442 = V16 5365-7425).
   - The Frozen Lean file is byte-identical.
   - `construction/` is byte-identical except `README.md`.
   - Locator fix: the H constants block is N5 L391-396 = V16 L492-497.
2. **CONFIRMED.**
   - (a) Thm 4.1 is unchanged in V13-V16.
   - (b) The C8, C3 and A9 fixes appear in V14 and later.
   - (c) C9 and the other kept items are verbatim.
   - (d) The determinant argument is sound. It removes local algebraicity but not (HT) or
     Kronecker–Weber. h-v16-adopt changes no constant or Lean statement.
   - **Corrected scope:** up-h never treated the Baba–Granath item that up-map handed it.
3. **CONFIRMED / CORRECTED.**
   - The defect in BG Prop. 3.7's proof is real mathematics: the separation claim fails at the
     Weierstrass points, and the product map has degree 4 (VERIFIED, `bg37.py`). BG's printed
     text was not read.
   - The chain 3.7 → 3.9 → Lin–Yang (2) is upstream's account.
   - h-trust F1 cites LY eq. (2), but the computation `igusa_check.py` never used it.
   - A2, A5 and A7 do not use 3.7-3.10.
4. **CONFIRMED.** 22P uses `v15:gi-full`, and V16's first FINDINGS item fills a missing step in
   it. Route AP consists of Lean theorems with no inverse theorem.
5. **CONFIRMED.** The pole side is unchanged and none of the CR3 fixes is upstream. Minor fixes:
   "Tian" in V16 means Cai–Shu–Tian, not TYZ; openaipointwise sections appear as provenance
   labels in the source catalogue (already so in N5).
6. **CONFIRMED.** No quoted run exceeds 21 words (shingle scan of a 362 MB corpus).

**Most serious correction.** F1 (the theta formula for `j`) lists Lin–Yang eq. (2) as a supplier.
That equation descends from Baba–Granath Prop. 3.9 and 3.7, whose proof upstream found
defective, and up-h left the point open.
- F1 still stands. Its route is LY Example 30's divisor statements, Igusa's theta formulas and
  igusa_check.py.
- The disc −24 normalization is now checked without Lin–Yang or Baba–Granath by two scripts.
  `endo24.py` computes exactly that the surface at the disc −24 Heegner point carries N5's QM
  datum, with commutant ℤ[√−6]. `theta24.py` evaluates the theta formula there to −16/27, to 39
  digits.
- F1 does not stand on Igusa 1967 plus computation alone: the global shape on X still needs
  LY Example 30.

**Next step.** In a task allowed to edit `h-trust.md`, apply rv-up §3.5 together with
h-v16-adopt:
- F1: drop eq. (2), name Example 30, and cite `endo24.py` and `theta24.py`.
- A2: narrow the locator to Thm 2.1, Lemma 3.1 and the §3 datum.
- Summary 2 and §2.5: wording changes.
