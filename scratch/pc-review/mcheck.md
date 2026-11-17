# Manuscript check draft (tex L1019-1121), pc-review

Columns: step | tex lines | S12 lines | round 2 (R2) | cloud (C) | agree? | verdict | rests on

| # | tex | S12 | step | R2 Lean | cloud Lean | agree | verdict | rests on |
|---|---|---|---|---|---|---|---|---|
| 1 | 1020-1024 | — | divisors of 2730 realize all signatures; 5,7,13 basis; choose m | `bookkeeping` (round 1, shared) | same (shared) | shared | OK | tex |
| 2 | 1025-1032 | 172-178 | β≡17, θ≡1 (24), disjoint supports, mutual local squares | `bookkeeping` (shared) | shared | shared | OK | tex |
| 3 | 1033-1035 | 543-552 | "simultaneous construction in S11-S12" gives n, nθ | `PoleS12.simultaneousConstruction` | `Simul.simultaneousConstruction_of_dimThree dimThreeCount` | same Prop | gap filled | S12 (tex delegates) |
| 4 | 1036-1040 | 267-279, 301-315 | s_i, λ_i, K; target ker K=<1,1_B>, λ∉im K | `MatrixConditions` (round 1, shared) | shared | shared | OK | tex |
| 5 | 1041-1043 | 567-571 | d-1 slots (0,0), one q0 (1,1), mod 12 residues 1, 7 | `matrixRealization` | `exists_Iprimes`, q0≡7 | both | OK | tex (+S12 residues) |
| 6 | 1044 | 621-628 | cross-block columns e_i+e_d | `block_injOn` | `exists_Iprimes` symbols e_b+e_{b_d} | yes | OK | tex |
| 7 | 1045 | 581-616 | K♯=K+λaᵗ; a undefined in tex | `sharp_targets`, a=e_{q0}+e_{b*} | `sharp`, `sharp_T`, `target_of_sharp_ker`, a=e_{q0}+e_{b_d} | yes, same a | gap filled | S12 only (a, K1_B=0, T factorization) |
| 8 | 1045-1051 | 617-652 | deleting q0 leaves [[D1,C1],[C1ᵗ,0]], 1ᵗD1 1=1, nonsingular | `sharp_ker_of_deleted`, `block_injOn` | `sharp_ker_of_deleted`, `deleted_of_nonsing`, `block_nonsing` | yes | OK (D1 not diagonal) | tex for nonsingularity; S12 for the symbol prescription making K1_B=0 and the q0 reduction |
| 9 | 1052 | 654-658 (674-678) | adding supp θ preserves the block | `hblockJ` | inside `matrixRealization` | yes | gap filled | S12 (cross row sums, I-J symbols 0) |
| 10 | 1053-1055 | 674-688 | free q0-J bits toggle J-diagonal; full-product coeff 1; one assignment for both | `exists_toggle_injOn` (ON THE SPOT kernel induction) | `toggle_one`, `toggle` (kernel argument, check) | yes | gap filled | S12 (L686-688: chosen bits do not affect smaller matrix) |
| 11 | 1056 | 690-703 | reciprocity, CRT, Dirichlet realize symbols by distinct primes | `exists_prime_lsym` | `exists_prime_lsym` (SimulArith) | yes | OK | tex |
| 12 | 1058-1059 | 381-394 | shape (3^δ∏q^u, ∏q^v) | `necAt_S12` | `necAt_of_local localTwo localThree localBad localGood` | yes | gap filled | S12 |
| 13 | 1060-1064 | 396-407 | Ku+D_λv=δλ, (K+D_s)v=0, (λ+s)ᵗv=0 | `eqs_of_localBad`, `e4_of_mod3` (round 1 shared) | shared | shared | OK | tex |
| 14 | 1065-1066 | 409-433 | matrix properties force v=0, δ=0, u∈ker K | `kmat_forces` (round 1), `e3_of_e2` | shared round 1 | shared | gap filled | S12 |
| 15 | 1066-1071 | 436-454 | (β,1) local everywhere incl. 2; independent of torsion | `cand_mem_S12`, `localGoodUnram` | `sel_sufficient` with the four local images | yes | gap filled | S12 |
| 16 | 1073-1086 | — | Lemma 5.4 | leaf `Lemma54` (+ glue `KummerSelmerM`) | interface `Lemma54At P` | R2 stronger fidelity | OK (cited, Poonen-Stoll) | tex + citation |
| 17 | 1088-1110 | — | Lemma 5.5 | `BCDTThmA`, `KolyvaginThm1` | `KolyvaginRankOne` | composed (step 3) | unverified (preprint) | citation |
| 18 | 1111-1113 | — | rank one + finite Ш ⇒ Ш[2]=0 ⇒ class is a point | `descentGlueM` (counting) | `descentGlueM` + `mordellWeilM` | yes | OK (finiteness of Ш not needed; ON THE SPOT, round 1/2) | tex |
| 19 | 1113-1121 | — | abscissa class β; rescaling; w=(eHz)⁻¹; θ=1 | `point_of_locM`, `witnesses_of_points` (round 1 shared) | shared | shared | OK | tex |
| MW | implicit | — | Mordell-Weil for E_ℓ | hypothesis `MordellWeil` | proved `mordellWeil_curve` | C stronger | OK | textbook, proved |
