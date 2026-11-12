/-! ## §2. Leaves that need definitions Mathlib lacks: placeholders (no content)

Each docstring gives the statement in the form the proof uses, the reference (UNVERIFIED unless
the note says otherwise), and the missing definitions with their cost tier. -/

/-- **R1. Shimura–Deligne: canonical model and moduli interpretation of the level-3 QM curve.**
`B = (2,−3)/ℚ`, `𝒪` maximal, `μ = 2j + ij`, `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`. (a) The functor on
`ℚ`-schemes of `(A, ι, λ, η)` (abelian scheme of relative dimension 2, `ι : 𝒪 → End A`, principal
polarization with Rosati involution `a ↦ μ⁻¹āμ`, `𝒪`-linear `η : 𝒪/3𝒪 ≅ A[3]`) is represented by
a smooth projective curve `Y₃/ℚ`; (b) complex uniformization compatible with the universal
family; (c) the finite-adelic normalizer acts over `ℚ`; (d) Shimura reciprocity at CM points.
Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21,
Cor. 5.7, Ex. 5.8, §§4.8-4.17; Kottwitz, JAMS 5 (1992), §5 (UNVERIFIED). Consequence (the PEL
theorem specialized to this datum). Missing: abelian schemes over a base with PEL structure,
moduli functors, representability (very large). -/
opaque R01_ShimuraDeligne : Prop

/-- **R2. Baba–Granath.** `X₆/W ≅ P¹_j`, branched over `0, ∞, −16/27` with indices 4, 6, 2 at the
CM points of discriminants −4, −3, −24; two QM surfaces with principal polarization of the fixed
type have the same polarized moduli point iff their points of `X₆` are `W`-conjugate. Canad. J.
Math. 60 (2008), Thm 2.1, Lemma 3.1 (journal numbering UNVERIFIED; 2005 preprint read by a model).
Exact. Missing: `X₆` and its Atkin–Lehner group (very large, via R1). -/
opaque R02_BabaGranath : Prop

/-- **R3. Lin–Yang.** On the finite nonzero `j`-locus the QM surface over `j` is the Jacobian of a
genus-2 curve with `[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.
Math. Z. 295 (2020), Example 30, eqs. (13)-(14) (VERIFIED in arXiv v1 by a repository note;
journal numbering UNVERIFIED). Exact. Missing: the QM locus (very large). -/
opaque R03_LinYang : Prop

/-- **R4. Igusa: `ψ₄`, `χ₁₀` in theta constants.** `ψ₄ = 2⁻² Σ_{m even} θ_m⁸`,
`χ₁₀ = −2⁻¹⁴ Π_{m even} θ_m²`, with the conversion to `J₂, …, J₁₀`. Amer. J. Math. 89 (1967),
pp. 833-834, 848 (UNVERIFIED). Exact. Missing: theta constants with characteristics on `𝔥₂`,
Siegel modular forms of degree 2 (large). -/
opaque R04_IgusaTheta : Prop

/-- **R5. González–Rotger.** For an order `R` of conductor `f`, `(f,6) = 1`, in an imaginary
quadratic `k` embeddable in `𝒪`, `#CM(R) = h(R)` on `X₆` and `ℚ(x)` is the ring class field `H_R`
or has index 2 in it (according as some prime dividing 6 is inert in `k` or not). J. Math. Soc.
Japan 58 (2006), Thm 5.12, Prop. 5.6 (VERIFIED in arXiv:math/0612732 by a repository note;
journal numbering UNVERIFIED). Exact. Missing: as R2. -/
opaque R05_GonzalezRotger : Prop

/-- **R8. Grothendieck's semistable reduction theorem** (Néron-model form). An abelian variety over
the fraction field of a henselian DVR acquires semistable reduction over a finite extension. SGA 7
I, Exp. IX, Thm 3.6 (UNVERIFIED). Exact. Needed only on the reviewed route for A6 (Lemma PR(ii));
the Raynaud route of the reduction-theory report avoids it. Missing: Néron models (large). The
Galois consequence is stated as `PkgI2.GrothendieckMonodromy`. -/
opaque R08_SemistableReduction : Prop

/-- **R9. Faltings 1983, Satz 3, Satz 4, Korollar 1.** For abelian varieties `A, B` over a number
field `F`: `V_ℓ(A)` is a semisimple `G_F`-module and
`Hom_F(A, B) ⊗ ℚ_ℓ ≅ Hom_{G_F}(V_ℓA, V_ℓB)`. Invent. Math. 73 (1983), pp. 360-361 (read by a
model). Exact. Missing: Tate modules `V_ℓ` with Galois action, Hom groups (medium). -/
opaque R09_FaltingsTate : Prop

/-- **R10. de Rham comparison.** For `F/ℚ_ℓ` finite and `A/F` an abelian variety of dimension `g`,
`H¹_et(A_F̄, ℚ_ℓ)` is de Rham with `D_dR ≅ H¹_dR(A/F)`; hence `V_ℓ(A)` is de Rham with Hodge–Tate
weights `0, −1`, each of multiplicity `g`. Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with
Thms 9.1, 9.3, corrigendum 2016; or Faltings 1989, Tsuji 1999 (UNVERIFIED). Exact (first clause).
Missing: `B_dR` with Galois action and filtration, de Rham representations (large). -/
opaque R10_DeRhamComparison : Prop

/-- **R11. Berger's p-adic monodromy theorem.** A de Rham representation of `G_K`, `K/ℚ_p` finite,
is potentially semistable. Invent. Math. 148 (2002), Thm 0.7 = Cor. 5.22 (read by a model).
Exact. Missing: `B_st`, potentially semistable representations (very large). -/
opaque R11_Berger : Prop

/-- **R12. Pan's Fontaine–Mazur theorem.** For an odd prime `p` and a continuous irreducible
`ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially semistable at `p`, odd, with
distinct Hodge–Tate weights (and, if `p = 3`, the residual clause): there are a normalized
eigenform `g` and a continuous character `ψ` with `tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))` for almost
all `v` (the trace reading of "comes from a cuspidal eigenform up to twist", implied by every
reading in the literature). JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by a
repository note; JAMS numbering UNVERIFIED). Consequence. Expressible now except "potentially
semistable" (very large) and "Hodge–Tate weights" (large). -/
opaque R12_Pan : Prop

/-- **R13. Hodge–Tate weights of eigenform representations at every level.** For a normalized
eigenform `g` of weight `k ≥ 2`, any level and nebentypus, `ρ_{g,ι}` (Tate normalization) is
Hodge–Tate at `ℓ` with weights `{0, 1−k}`. Saito, Invent. Math. 129 (1997); or Kato, Astérisque
295 (2004), §9.4; or Scholl 1990 with R10 and T23 (UNVERIFIED). Consequence (normalization).
Missing: Hodge–Tate representations (large). -/
opaque R13_EigenformHT : Prop

/-- **R16. Eichler–Shimura in `J₁(N)`.** For a weight-2 newform `f` of level `N`,
`V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a `G_ℚ`-stable two-dimensional subquotient on which
`tr(Frob_p) = ι(a_p(f))` for `p ∤ Nℓ`. Shimura 1971, Thm 7.9, §7; Shimura, J. Math. Soc. Japan 25
(1973), Thm 1 (UNVERIFIED). Consequence. Missing: `X₁(N)`, `J₁(N)` over `ℚ` (very large). -/
opaque R16_EichlerShimuraJ1 : Prop

/-- **R17. Carayol's local–global compatibility.** For a weight-2 newform of level `N` and `p ≠ ℓ`,
the Artin conductor exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986),
Théorème (A) (UNVERIFIED; that it covers `F = ℚ` at `p | N` is an open check). Consequence.
Missing: conductors of ℓ-adic representations, newforms (medium). -/
opaque R17_Carayol : Prop

/-- **R18. Javanpeykar.** A smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1` with a Belyi
map of degree `d` has `h_F(Jac X) ≤ 13·10⁶ · g · d⁵`. Algebra Number Theory 8 (2014), Thm 1.1.1
(read by a model). Exact. Missing: Faltings height (very large), Belyi maps, Jacobians. -/
opaque R18_Javanpeykar : Prop

/-- **R19. Gaudron–Rémond isogeny theorem.** Isogenous abelian varieties `A, B` of dimension `g`
over a number field `K` admit an isogeny `A → B` of degree at most
`((14g)^{64g²}[K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`. Duke Math. J. 163 (2014), Thm 1.4 (read
by a model). Exact. Missing: Faltings height (very large). -/
opaque R19_GaudronRemond : Prop

/-- **R20. Faltings' height lemma.** For an isogeny `φ : A → B` over a number field,
`|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Faltings 1983, Lemma 5; Raynaud, Astérisque 127 (1985),
Exp. VII, Cor. 2.1.3 (UNVERIFIED). Exact. Missing: Faltings height. -/
opaque R20_FaltingsHeightLemma : Prop

/-- **R21. Bost's lower bound.** `h_F(A) ≥ −(3/2)·dim A` (Bost: `≥ −log(π√2)·dim A`). Bost,
Sém. Bourbaki 795 (1996), as recorded in Gaudron–Rémond 2014, §9 (read by a model). Consequence.
Missing: Faltings height. -/
opaque R21_Bost : Prop

/-- **R22. Pazuki.** For a principally polarized abelian surface over a number field,
`h_Θ(A) ≤ ½X_D + C₂ log(X_D + 2)`, `X_D = max(1, h_F(A) + log π)`, `C₂ = 1000·2⁴(log 2⁴)⁵`,
`h_Θ` the height of the level-2 theta constants. Bull. Soc. Math. France 140 (2012), Cor. 1.3(2)
(read by a model). Exact. Missing: Faltings height, theta constants. -/
opaque R22_Pazuki : Prop

/-- **T8. Poincaré reducibility** (Mumford, *Abelian varieties*, §19 Thm 1, UNVERIFIED). Missing:
abelian subvarieties and isogenies (medium). -/
opaque T08_Poincare : Prop

/-- **T9. Weil pairing.** The Weil pairing of a polarization is Galois-equivariant with values in
`ℤ_ℓ(1)`, so `G_K` acts on `V_ℓ(A)` through `GSp` with cyclotomic multiplier (Mumford §§20, 23,
UNVERIFIED). Missing: polarizations, Tate modules (medium). -/
opaque T09_WeilPairing : Prop

/-- **T10. `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`**, Galois-equivariantly (Milne in Cornell–Silverman 1986,
Thm 15.1(a), UNVERIFIED). Missing: ℓ-adic étale cohomology (large). -/
opaque T10_TateDuality : Prop

/-- **T11. Riemann's theorem, GAGA, rigidity.** `End⁰(A_ℂ)` is the algebra of endomorphisms of
the rational Hodge structure `H₁(A(ℂ), ℚ)`, and `Hom(A, B) = Hom(A_ℂ, B_ℂ)` over `ℚ̄` (Mumford
§§1-3; Serre 1956; Conrad 2006, §3; UNVERIFIED). Missing: analytification (large). -/
opaque T11_RiemannGAGA : Prop

/-- **T12. Artin comparison.** `V_ℓ(A) ≅ H₁(A(ℂ), ℚ) ⊗ ℚ_ℓ`, compatibly with complex conjugation
(SGA 4 XI 4.4, UNVERIFIED; elementary for abelian varieties via `ℂ²/Λ`). Missing: as T11. -/
opaque T12_ArtinComparison : Prop

/-- **T15. `H²(G_ℚ, ±1) ≅ Br(ℚ)[2]`**, compatibly with restriction to `G_{ℚ_v}` (Milne, *ADT*,
Ch. I; Tate in Cassels–Fröhlich VII; UNVERIFIED). Missing: crossed products, local invariants
(medium; Tau Ceti has the local-global sequence). -/
opaque T15_BrauerCohomology : Prop

/-- **T16. Local class field theory** for finite extensions of `ℚ_p`: the local Artin map, its
compatibility with norms, the upper numbering theorem (Serre, *Local fields*; UNVERIFIED). Missing:
local Artin map (medium; Tau Ceti). -/
opaque T16_LocalCFT : Prop

/-- **T22. Upper numbering and conductors.** Herbrand's theorem, the subgroup formula
`G^u ∩ H = H^{ψ(u)}` for absolute groups, Artin and Swan conductors of a representation with
finite wild image (Serre, *Corps locaux*, IV §§1-3, VI §2; UNVERIFIED). Missing: upper numbering
on `G_{ℚ_p}`, conductors of ℓ-adic representations (medium; Tau Ceti has finite levels). -/
opaque T22_UpperNumbering : Prop

/-- **T23. Fontaine's closure properties.** de Rham representations are closed under duals,
tensor products, sums and subquotients (Astérisque 223 (1994), Thm 3.8, UNVERIFIED). Missing: as
R10 (large). -/
opaque T23_FontaineClosure : Prop

/-- **T25. Newforms** (Atkin–Lehner–Li; Li, Math. Ann. 212 (1975), Thm 5; UNVERIFIED): each system
of Hecke eigenvalues of a normalized eigenform away from the level is that of a unique newform of
level dividing it; Galois conjugates of newforms are newforms. Missing: old space and newforms
(medium; Tau Ceti). -/
opaque T25_Newforms : Prop

/-! ## §3. Glue -/

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are uninterpreted.
`R6`, `R7` are the reduction-theory report's genuine statements; `R14`, `R15` are stated over §0. -/
structure ResearchLeaves : Prop where
  r1 : R01_ShimuraDeligne
  r2 : R02_BabaGranath
  r3 : R03_LinYang
  r4 : R04_IgusaTheta
  r5 : R05_GonzalezRotger
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : R08_SemistableReduction
  r9 : R09_FaltingsTate
  r10 : R10_DeRhamComparison
  r11 : R11_Berger
  r12 : R12_Pan
  r13 : R13_EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : R16_EichlerShimuraJ1
  r17 : R17_Carayol
  r18 : R18_Javanpeykar
  r19 : R19_GaudronRemond
  r20 : R20_FaltingsHeightLemma
  r21 : R21_Bost
  r22 : R22_Pazuki

/-- **The textbook foundations** (note §2.2), bundled. -/
structure TextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t2 : PkgI2.AbhyankarDVR.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI2.HomRankBound.{0}
  t7 : PkgI2.CharpolyIndependentOfEll.{0}
  t8 : T08_Poincare
  t9 : T09_WeilPairing
  t10 : T10_TateDuality
  t11 : T11_RiemannGAGA
  t12 : T12_ArtinComparison
  t13 : SkolemNoether
  t14 : HasseBrauerQ
  t15 : T15_BrauerCohomology
  t16 : T16_LocalCFT
  t17 : KroneckerWeber
  t18 : FrobeniusDense
  t19 : BrauerNesbitt
  t20 : GlueConductor.HilbertDifferentFormula
  t21 : GlueConductor.SerreDifferentBound
  t22 : T22_UpperNumbering
  t23 : T23_FontaineClosure
  t24 : EigenformTwist
  t25 : T25_Newforms

/-- **G0 without G20: the glue G1-G19.** The leaves imply the `j`-form of H,
`JHeightBound Mult.S_mul` (steps A1-F3). Not proved: the glue needs the definitions of §4 of the
note, and most leaves are placeholders. -/
theorem jHeightBound_of_leaves (_r : ResearchLeaves) (_t : TextbookLeaves) :
    ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul := by
  sorry

/-- **G0. The leaves imply `SixContactMin`**, through G20, the existing Lean proof
`ZInQ.JHeight.sixContactMin_of_jHeightBound` (`ZInQKernel/Hypotheses/JHeight.lean`). -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) :
    ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound (jHeightBound_of_leaves r t)

end HSyn

end

#print axioms HSyn.weight_match
#print axioms PkgI2.inertiaTrivial_of_goodReduction
#print axioms PkgI2.D2_fixed_of_raynaud
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.level_le
#print axioms GlueConductor.fourth_pow_mem
#print axioms HSyn.sixContactMin_of_leaves
