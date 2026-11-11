# rv-h-trust work log

Target: docs/research/h-trust.md (713 lines, merged at fd8677ac via 81057fcc).

## Step 1. Read h-trust.md in full
- Structure: Summary; §0 statement+route table; §1 36 steps A1-A10, B1-B3, C1-C10, D1-D5, E1-E4, F1-F4;
  §2 residuals 2.1-2.7; §3 docstring drafts; §4 next step.
- Count check (by reading): A=10, B=3, C=10, D=5, E=4, F=4 -> 36. OK.

## Step 2. Read Lean statements, hypothesis audit, N5 L380-966
- Height.lean: SixContactEstimate = ∀S (primes, ⊇ primes≤324) ∀R≥max(D,maxS,1e12) ∀u∉𝒞, h(u) ≤ H6(R) M_S(u)^24.
  H6 contains C_cm (the CM constant); with NoCM the CM branch is empty, the max only weakens. OK.
- HeightMin: SixContactMin instance S=S_mul, R=D; Main.lean:70 derives it. Uses: S_mul primes, ⊇ primes≤324,
  max S_mul ≤ D, 10^12 ≤ D (four facts, h-trust §3 HeightMin draft names two).
- Current Height.lean module docstring names "Buzzard's integral models" and "an effective CM argument".
- N5 L405-964 read in full; map of ranges to steps: L405-422 A1-A2; L423-441 A3; L443-530 A4-A6 (b11);
  L532-543 A7; L544-563 A8; L564-577 A9; L578-631 A10; L632-716 B1-B3; L719-795 C1-C10;
  L796-857 D1-D5; L860-905 E1-E4; L908-964 F1-F4. Every line range covered. (VERIFIED by reading)
- Findings to pursue:
  F-a C8 (N5 L757-768) silently uses that the eigenform's representation rho_g is de Rham at 5 with HT
      weights {0,1-k} (needed for "twisting character is a de Rham subrep of the Hom rep" and for the
      weight comparison). h-trust C8 lists only Conrad/Serre local algebraicity. Missing supplier
      (STANDARD: Faltings 1987 Math. Ann. 278 (HT); Scholl 1990 + Faltings 1989/Tsuji 1999, or Saito 1997,
      or Kato 2004 as V14 did). h-a011 §4: V14 used Deligne–Serre §1.9 + Kato 2004 + Washington.
  F-b C9: twisting an eigenform by a Dirichlet character and passing to the primitive newform
      (Atkin–Lehner–Li / Shimura) not in supplier list.
  F-c C10: semisimplicity of the modular 3-adic representation (Faltings on V_3(A_f), or Ribet 1977)
      and specialization of Tate modules at good reduction (Serre–Tate / BLR) not listed.
  F-d Height normalizations (Javanpeykar original Faltings; GR14 ?; Pazuki Deligne) not in §2.6;
      the transfer has slack, see later step.
  F-e Status rule "weakest supplier" not propagated: C6, D4, A8 depend on A5/A6.
  F-f rv-h-b1 (merged 3aae7eed before h-trust 81057fcc) reviewed Lemma PR, NV, TS and A4 -> h-trust's
      [U] labels, §2.2, docstring "not yet reviewed" and KERNEL_PLAN "review pending" are stale.
  F-g A1 says uniqueness of the principal polarization is not needed; rv-h-b1 §7 item 2 needs it for A4
      (λ adds no data). Elementary proof: λ'=λ∘a, same Rosati ⇒ a central symmetric ⇒ a∈ℚ_{>0}, principal ⇒ a=1.

## Step 3. Which N5 text did the Astra reviews actually read? (VERIFIED by diff)
- `git show 09c0c3f3:diophantine_zq.tex` has sha256 bfc4192de00e… (= Astra final_source_sha256);
  97cec7fd has cb1148cd6c77… (= N5).
- Diff of Thm 4.1 section, 11/4 L380-935 vs N5 L376-966: scratch/rv-h-trust/thm41_n4_vs_n5.diff (150 lines).
  Changed hunks inside the proof:
  1. A1 (N5 L417-419): Riemann-form convention sentence added (cosmetic).
  2. A9 (N5 L564-570): the Milne paragraph (polarizable tori, Hodge endos algebraic, defined over Q̄) is NEW in N5.
  3. C3 (N5 L734-737): 11/4 had "finite-extension descent … [faltings1988]"; N5 replaces it by
     Lemma lem:de-rham-descent (N5 L10938-11000, Scholze route). 11/4 has no such lemma
     (grep "de-rham\|scholze" in 11/4: only faltings1988 at L713). => Astra never read N5's C3.
  4. C8 (N5 L759-761): local algebraicity citation (Conrad) added; argument otherwise unchanged.
  5. C9 (N5 L765-769): Li Fricke formula + Shimura Thm 1 sentence NEW in N5.
  6. C10: "arithmetic Frobenius lift" -> lift of x↦x^p (cosmetic).
  7. D1 Herbrand derivation, D3 Silverman IV.6.4: new (covered by rv-h-novel on N5).
  8. F1 (N5 L908-927): LY/LNY substitution written out (covered by igusa_check.py).
  All other proof text (A2-A3, A7, A8, A9 centralizer part, B, C1-C2, C4-C7, D2, D4-D5, E, F2-F4) identical.
- Consequence: h-trust's "[M] (Astra …)" is accurate for A3, A7, A8, F2-F4, E, and the 11/4 parts;
  NOT for C3 (lemma), the Milne paragraph of A9, the Li/Shimura sentence of C9.
- Astra descent ADDENDUM item 3 (in repo, docs/reviews/height-replacement/descent/ADDENDUM.md) records
  Berger's published/author version numbering: Theorem 0.7 and Corollary 5.22 (arXiv v3: 0.6, 5.19).
  h-trust C4 / §2.5 item 8 call the journal number UNVERIFIED and do not cite this record.
  Astra item 6 also gives Milne AV Prop 10.20 for ℓ-independence (h-trust C10 cites Mumford §19 Thm 4).

## Step 4. Model review here of the N5-only text (N5 L10938-11000; L564-570)
- lem:de-rham-descent: read line by line. Holds as an argument given Scholze Cor 1.8, Thms 9.1/9.3
  (UNVERIFIED locators). Weight step: (V⊗C)⊗_{C,τ}Q̄_ℓ = V⊗Q̄_ℓ has weights {0,0,-1,-1} = 2×wt(r⊗_τ),
  so wt(r⊗_τ) = {0,-1}; HT weights are unchanged by restriction to G_F. Descent paragraph correct
  (Hilbert 90 for B_dR-semilinear Gal(F'/K)-action). VERIFIED as an argument.
- A9 Milne paragraph: σ∈Aut(C/Q̄) fixes torsion points, so σφ=φ on a dense set, so φ is defined over Q̄.
  Centralizer: rational elements of B⊗B^op commuting with right mult. by J are B⊗Z_B(J), Z_B(J)=ℚ or
  imaginary quadratic k ⊂ B, B⊗k ≅ M_2(k). VERIFIED as an argument.
