# r17-bypass results log

Base 9a100aa7 (leaf-fold22). Field `HDec.HSyn.OpenResearchLeaves21.r17 : _root_.LadicCond.CarayolR17'`
(ZInQKernel/HDecomp/Conductor/LadicCond.lean:456), kinds.tsv row: research / consequence / GLUE / GLUE.

## 1. Uses of the field (VERIFIED: grep of `.r17`, `hCar` in ZInQKernel/OneProof/H, read)

* Every `r17 := r.r17` / `n.r17` in TailX, TailZ4 … TailZ34 is a pass-through between bundle generations
  (TailN:118 `carayolR17_ofK5 r.r17` changes only the `GaloisRep` copy).
* The single consumer: TailK.lean:333, inside the G0 term, `G0AssembleMod.afterG7_of3 … r.r17 …`
  (TailD.lean:156) → `newformLeaves_of3 r t hCar` (TailD:150) puts it in
  `G0ModNewform.NewformLeaves.r17` (TailA:3703) → `modularConstituent_tail_G` (TailA:4038) →
  `modularConstituent_tail` (TailA:3747) → `g13_g16_ram` → `g13_g16` (TailA:3712) →
  `g15 lv.r17 hSw …` (TailA:3537), the only theorem that applies it:
  `carayolR17_of_R17' hSw hCar` then `factorization_eq_condAt` (TailA:3522) at
  - ℓ = 5, every prime p ≠ 5, ρ = the R14 representation attached to `f` isomorphic to `D.r5`;
  - ℓ = 3, p = 5, ρ = the R14 representation isomorphic to `D.r3`.
  `f` = the newform of `newform_of_pan` (Pan–Berger's eigenform, twisted by T24, newform by T25), level N
  arbitrary: the instances are a general weight-2 newform attached to a 2-dimensional constituent of
  `V_ℓ(A)` for the manuscript's model `A/L'` (QM abelian surface), at every prime p. Not special, not vacuous.
* What g15 does with the equality `v_p(N) = c` (c = condAt at an adapted level): only `v_p(N) ≤ c`
  (c ≤ E₀ ⇒ v_p(N) ≤ E₀; c ≤ 2 ⇒ v_p(N) ≤ 2; c = 0 ⇒ p ∤ N). VERIFIED by reading TailA:3537-3576.

## 2. Weakest Prop the consumer needs

`v_p(N) ≤ a(ρ|G_{ℚ_p})` for p ≠ ℓ (nontrivial only for p ∣ N), ℓ ∈ {3, 5}: the "level divides the
prime-to-ℓ conductor" half of Carayol's equality. Stated as `CarayolLevel.CarayolLevelLe`.

## 3. Provable from the bundles? No (argument, SPECULATIVE-free: lists what each field says)

The inequality needs information on ρ_f|G_{ℚ_p} at p ∣ N. No bundle field speaks about it:
R16 (Eichler–Shimura on J₁(N)) gives traces only at p ∤ Nℓ; R14/DS 9.6.5 only p ∤ Nℓ; NOS (r7a)
turns "ρ_f unramified at p" into "A_f good reduction at p", but "A_f (new) has bad reduction at p ∣ N"
is Deligne–Rapoport/Carayol, not in any bundle; Faltings (r9a/b), de Rham (r10), Raynaud (r6), the
Tate-module and CM leaves concern A, not f. The consumer cannot avoid the level: G16Out needs a
bounded N with A a constituent of J₁(N), and Pan's theorem gives no level.

## 4. Lean (all VERIFIED: compiled at base 9a100aa7)

* Build tree: copied p1-quot2's .lake/build and lean/.lake/build (same base plus Contrib files), then
  `lake build ZInQKernel.OneProof.H.TailZ34`: success, 31 min 53 s (rebuilt LPrefix … TailZ34).
* `ZInQKernel/Contrib/OneProof/CarayolLevel.lean`: `lake build ZInQKernel.Contrib.OneProof.CarayolLevel`
  success (17 s); after replacing deprecated `dif_pos`/`dif_neg` by `dite_eq_left`/`dite_eq_right`, no
  warning in the file. Declarations: `condExp_eq_of_intertwine` (no SwanIndependent), `iso_of_attached`,
  `NewformRepConductor` (new leaf), `carayolR17'_of_newformRepConductor : NewformRepConductor →
  LadicCond.CarayolR17'`, `newformRepConductor_of_R17'`, `CarayolLevelLe`, `carayolLevelLe_of_R17'`.
* `scratch/r17-bypass/Bypass.lean`: compiles (11 s), lint warnings only; `afterG7_of3_levelLe` standard axioms.
* `#discharges` (scratch/r17-bypass/DischargesCheck.lean): `DISCHARGES [OpenResearchLeaves21.r17] by
  CarayolLevel.carayolR17'_of_newformRepConductor; still assumes: [CarayolLevel.NewformRepConductor];
  axioms: [propext, Classical.choice, Quot.sound]`; 63 open hypotheses, 1630 theorems checked.
* autofold dry run: `strict count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11`;
  FoldDryRun.lean (`sixContactMin_of_open29`) compiles, standard axioms (71 s).

## 5. Ratings

* `NewformRepConductor`: published form pending reading (conductor packaging of ρ_{f,λ}; DDT 1997 §3.1,
  Carayol 1986 §0, UNVERIFIED); equivalent to r17 modulo proved glue (both directions in Lean, the
  converse with R14's existence). Counts GLUE until read; −1 strict GLUE if a reading confirms.
* `CarayolLevelLe` (weakest needed form): consequence, not printed as such; not used by the fold.
