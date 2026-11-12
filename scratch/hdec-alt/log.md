# hdec-alt log

## Step 1. Sources read
- h-trust.md (A1-F4), HeightMin.lean (SixContactMin), N5 L377-445 (constants, Thm 4.1 statement).
- h-leaves.md §§2.2, 4.5: vK (arXiv:1310.7263) read there; Pan → KW+Kisin route assessed "no reduction in depth".
- rs-height R4/R5; nt-h §3.3-3.6: Baker/S-unit Shafarevich routes for genus-2 curves fail (fibres have bad
  stable reduction at every contact prime, even valuation too); only modularity routes give polynomial bounds.
- docs/revision-2.md, README: 11/5 replaced an earlier "von Känel–Kret height argument" by Pan + CM argument.
  No record of the vK–Kret citation in the audit (grep: none).

## Step 2. Map + alternative-route findings (reasoning; no Lean)
- wk-h (Tier1/Tier2, vacuity §4.3), rv-lit §4 (JHeightBound = A1-F3), prereq-survey §1 read.
- JHeight.olean, HeightMin.olean present in .lake/build: Leaves.lean can import ZInQKernel.Hypotheses.JHeight.
- Mathlib has `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` (Group/Abelian.lean):
  GrpObj in Over (Spec K) + IsProper + GeometricallyIntegral exist → cheap genuine `AbelianVariety K`.
- Algebra VERIFIED by hand: for j = J(u) = -57600F²/G⁶: -6j = 6·(240F/G³)² (57600·6 = 6·240²);
  27j+16 = 16H²/G⁶ (from h-trust A5: J+16/27 = 16H²/(27G⁶)). So the classes of -6j and 27j+16 in
  ℚ*/ℚ*² are constant (6 and 1) along the family.
- Finding (route M-KW): Pan + C3,C4,C5,C7,C8 (Scholze/Faltings-Tsuji, Fontaine, Berger, Saito/Kato,
  Deligne-Serre, de Rham descent lemma, determinant argument) can be replaced by Ribet's building-block
  theorem + Khare-Wintenberger modularity of GL2-type abelian varieties over ℚ + an elementary twist
  lemma (r|G_K ≅ ρ|G_K abs. irreducible ⇒ r ≅ ρ⊗ψ, ψ finite) + Kronecker-Weber. Building-block
  hypotheses = A10 (End⁰ = B) + B1 (B-linear μ_σ). Weight 2 automatic; C8 disappears; C10 stays.
- Finding (vK route): effective Shafarevich for GL2-type over ℚ needs a GL2-type B₀/ℚ ⊇ A; dim B₀ =
  [E:ℚ] ⊇ ℚ(nebentypus), which must be odd at each p in T₋ (local invariant 1/2 of [ε]); T₋ ∩ supp M
  not controlled ⇒ dim B₀ unbounded in M. Route viable only if vK's constant is polynomial in dim
  (UNVERIFIED; theorem text not on host). Not adopted; recorded as the top open alternative.
- Baker/S-unit genus-2 Shafarevich (Smart, vK 2014): excluded by nt-h §3.3 (curves C_{J(u)} have bad
  stable reduction at every positive contact valuation).

## Step 3. Lean probe (scratch/hdec-alt/Probe.lean) — compiles (lake env lean, no errors)
- `import ZInQKernel.Hypotheses.JHeight` FAILS: unknown module prefix 'ZInQ' (HeightMin → Multiplication
  → upstream package `lean/` not built here; same as wk-h). Use `import ZInQKernel.Hypotheses.Height`
  and restate JHeightBound at a prime set S (as wk-h did).
- Compiles: `AbelianVariety K` (Over (Spec K) + GrpObj + IsProper + GeometricallyIntegral + Smooth);
  `GalRep K E` (continuous G_K →* GL_n(E)); `intertwiners` as Submodule of linear maps (rectangular
  Matrix `*` hits a CStarMatrix HMul instance clash: avoid); `homDim`; `IsSemisimple`;
  Hasse principle for `QuaternionAlgebra ℚ a 0 b` (notation ℍ[..] is scoped; use the constant);
  Kronecker–Weber; `absLogHeightVec := Height.logHeight x / [K:ℚ]`.

## Step 4. scratch/hdec-alt/Leaves.lean — compiles (`lake env lean`), one `sorry` (G-top)
- §1 target: JHeightBoundAt S / SixContactMinAt S / Admissible S; F4 block copied verbatim from
  ZInQKernel/Hypotheses/JHeight.lean L30-232; `sixContactMinAt_of_jHeightBoundAt` PROVED (no sorry).
- §2 genuine defs: AbelianVariety, dim (sInf of SmoothOfRelativeDimension), GalRep, act, intertwiners,
  homDim, IsStable, IsSemisimple, IsIrreducible, absLogHeightVec.
- §3 leaves statable now: Hasse (quaternion), Hilbert reciprocity (needs `open Classical in` before
  the docstring), Kronecker–Weber.
- §4 opaque placeholders (17) with cost tiers; §5 leaves over them (16): Raynaud, NOS, MumfordRank,
  FaltingsTate, Ribet, KW, NewformTwist, ShimuraAf, Carayol, Javanpeykar, GR14, FaltingsIsogenyHeight,
  HeightAdditive, Bost, Pazuki, IgusaLinYang. StatedLeaves bundles 19 Props.
- §6 GeometricInput (output of G1-G5), `jHeightBoundAt_of_leaves` (sorry), `sixContactMinAt_of_leaves`.

## Step 5. Leaves.lean: + Skolem–Noether (Algebra.IsCentral + IsSimpleRing + FiniteDimensional),
  + GalRep.Iso, + Brauer–Nesbitt (charpoly with reindex). Compiles; 21 Props in StatedLeaves; one sorry
  (jHeightBoundAt_of_leaves). `#print axioms sixContactMinAt_of_jHeightBoundAt`:
  [propext, Classical.choice, Quot.sound] (VERIFIED).

## Step 6. Deliverables
- docs/research/hdec-alt.md written (§§1-7). Counts VERIFIED from its tables: 30 leaves (18 deep,
  7 library, 5 textbook); R*: C3-C5 removed, C7-C8 replaced by G13; 31 kept nodes = 11 LIT, 13 NEW, 7 BK.
- Leaves.lean docstrings updated; recompiled: one sorry (jHeightBoundAt_of_leaves); axioms of
  sixContactMinAt_of_jHeightBoundAt = [propext, Classical.choice, Quot.sound]. 22 opaque placeholders.
- Self-check of §1.2 (Ribet + KW): building-block hypotheses (End⁰ = B central division over ℚ, t=2,
  μ_σ B-linear); V_ℓ(A)⊗Ē ≅ W⊕W with W abs. irreducible on G_K for K ⊇ L' (Faltings End);
  ρ_τ|G_K ⊂ W^{2n} semisimple ⇒ ρ_τ|G_K ≅ W; Schur ⇒ r ≅ ρ_τ⊗ψ, ψ through Gal(K/ℚ). No gap found.
- .fleet/hdec-alt.md written.
