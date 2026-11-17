# r17-print log (results only)

Base: wip/integrate-w82 5e235a40 (frozenTarget sixContactMin_of_open38, TailZ45, strict 16 LEAF / 21 GLUE on 37).
Merged: e9683dac (newform-dict: NewformDict.lean) and origin/wip/r17-bypass 3e6e5017 (CarayolLevel.lean). Both build (VERIFIED, lake build, 2026-11-16).

Field: `r17 : LadicCond.CarayolR17'` (ZInQKernel/HDecomp/Conductor/LadicCond.lean:456; verbatim copy in R17Statement.lean.txt), kinds.tsv row: research r17 consequence GLUE/GLUE.

## Statements
* New leaf `CarayolPrinted.CarayolThmA` (ZInQKernel/Contrib/OneProof/CarayolPrinted.lean:396): over Tau Ceti `Newform N 2`, `[NumberField K_f]`, `λ ∣ ℓ` in `HeightOneSpectrum (𝓞 K_f)`: ∃ continuous `ρ : G_ℚ →* GL₂(K_{f,λ})`, Burnside-absolutely irreducible, unramified at p ∤ Nℓ with arithmetic-Frobenius trace a_p, and `condExp (ρ ∘ decomp p) = v_p(N)` for every prime p ≠ ℓ.
* Discharge `CarayolPrinted.carayolR17'_of_printed : CarayolThmA → DSCoeffExt.EigenformCoeffFieldFinite → LadicCond.CarayolR17'` (the second hypothesis is an existing bundle field).
* New glue lemmas (proved): `condExp_map` (conductor invariant under scalar extension along a field hom), `finrank_ann_map`, `codimInv_map`, `isAdapted_map_iff`, `adjoin_map_eq_top`, `eq_bot_or_top_of_adjoin`, `isSemisimple_of_adjoin`.

## Compile outcomes (all VERIFIED, Lean 4.35.0 / Mathlib v4.35.0)
* scratch/r17-print/CarayolPrinted.lean: compiles, no warnings.
* ZInQKernel/Contrib/OneProof/CarayolPrinted.lean: `lake build ZInQKernel.Contrib.OneProof.CarayolPrinted` success; `lake env lean` on it: no output (no warnings).
* Axioms (axioms.txt): carayolR17'_of_printed, condExp_map: [propext, Classical.choice, Quot.sound].
* #discharges (discharges.txt): `DISCHARGES [OpenResearchLeaves28.r17] by CarayolPrinted.carayolR17'_of_printed / still assumes: [CarayolPrinted.CarayolThmA, DSCoeffExt.EigenformCoeffFieldFinite] / axioms standard`.
* autofold dry run (autofold-dryrun.txt): `strict count: 16/21 on 37 -> 17/20 on 37; strictest 16/21 -> 17/20` (flag "unread", kind published). AutofoldDryRun.lean (line 1 stripped) compiles: `sixContactMin_of_open39` standard axioms (autofold-dryrun-compile.txt).

## Findings
* r17 is not the printed statement for three reasons, now all proved in Lean: (1) IsNewform vs printed newform (NewformDict); (2) coefficients ℚ̄_ℓ via ιL,ιC vs K_{f,λ} (DSCoeffExt place/τhat + condExp_map); (3) every semisimple attached ρ vs the constructed ρ_{f,λ} (Brauer–Nesbitt+T18 from CarayolLevel, semisimplicity from absolute irreducibility).
* The leaf needs absolute irreducibility of ρ_{f,λ} (Ribet 1977, UNVERIFIED locator): without semisimplicity of the leaf's ρ the transport fails (conductor is not invariant under semisimplification). SPECULATIVE-free: this is a mathematical necessity of the transport, not a Lean artifact.
* Reading risk (rated in report): Carayol's Théorème (A) is local-global compatibility through π_p; the conductor clause needs Casselman 1973. Packaged form believed printed (DDT 1997 Thm 3.1), UNVERIFIED.
