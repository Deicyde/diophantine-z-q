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
