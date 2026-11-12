# rv-routek: fleet report

**Verdict: SOUND AFTER REPAIRS** (both variants of route K: hdec-elementary §2.2 and hdec-alt §1.2).
Full review: `docs/research/rv-routek.md`. Checks: `scratch/rv-routek/` (`checks.py`,
`ind_conductor.py`, both ALL OK; `log.md`). No Lean run was needed.

- VERIFIED as arguments: hdec-elementary's Lemma GL₂ (G14: the `ℚ`-simple factor of
  `Res_{L'/ℚ} A` carrying `r_ℓ` is GL₂-type, `B_{L'} ∼ A^k`), its Lemma Ind (G16) and G17, and
  hdec-alt's twist lemma. G16 needs `G^u ⊂ G_{L'}` for `u > U₀`, which route P never used. It
  holds because N5 defines `L'` as the kernel field of `β|G_L` (L715).
- Constants unchanged: `[L':ℚ] ≤ QM`, `N ≤ QM²` (`f_p(B)/dim B ≤ 2 + 8(DG₀)² ≤ E₀ = 10(DG₀)²`),
  `g ≤ N²`. The dimension of the GL₂-type variety cancels and enters no bound.
- Nothing that route K drops (C9, C10, de Rham lemma, Weil pairing, oddness) is used elsewhere. E1
  is replaced by G15, and E2-E4 are unchanged.
- Repairs:
  1. L6 must cite KW (II) and Kisin 2009 (2-adic). hdec-elementary R2's "Kisin not needed" is
     wrong about the trust base.
  2. L7 is four results bundled. At `p = 3` G16 uses `ℓ = 2`, so add ℓ-independence of the
     conductor (SGA 7 IX) or check Carayol at `ℓ = 2`.
  3. Write out G16's `G^u ⊂ G_{L'}` and the Mackey step.
  4. hdec-alt step 3: "for some τ".
  5. Prefer G14 to hdec-alt's L13 (Ribet–Pyle): it avoids Pyle and Tate's `H²` theorem.
  6. Retract hdec-alt §1.1(ii): `dim B ≤ 2[L':ℚ] ≤ 2QM` is bounded in `M`.
- UNVERIFIED (no network, no sources on disk): every theorem number of Ribet 1992, Pyle 2004,
  KW (I)/(II), Kisin, Carayol; whether Ribet's converse covers more than `ℚ`-curves; von Känel's
  dependence on `g`.
