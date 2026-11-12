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

/-- **T23. Fontaine's closure properties.** de Rham representations are closed under duals,
tensor products, sums and subquotients (Astérisque 223 (1994), Thm 3.8, UNVERIFIED). Missing: as
R10 (large). -/
opaque T23_FontaineClosure : Prop

/-- **T29. Local normalizers of maximal orders.** For a quaternion algebra `B_p` over `ℚ_p` and a
maximal order `𝒪_p`, the group `N(𝒪_p)/ℚ_p^×𝒪_p^×` has order 2 if `B_p` is a division algebra
(generated by a uniformizer of `B_p`) and order 1 if `B_p ≅ M₂(ℚ_p)` (`N(M₂(ℤ_p)) = ℚ_p^×GL₂(ℤ_p)`);
for `B = (2,−3)` (ramified at 2, 3) this gives the normalizer index 4 of A3 (Vignéras, LNM 800,
Ch. II, UNVERIFIED). Statable over Mathlib's quaternion algebras (pkg-I1 I1-f), not drafted. -/
opaque T29_LocalNormalizers : Prop

/-- **T32. Tame inertia and quadratic characters** (glue-descent L-B3a, L-B3b). (a) The tame
inertia group of `ℚ_p`, `p` odd, has a unique continuous character of order 2; (b) a quadratic
Dirichlet character is ramified exactly at the primes dividing its conductor (Serre, *Local fields*
IV §2; Neukirch; UNVERIFIED). Used only for the unramifiedness of `L'`. Missing: inertia subgroups
of `G_ℚ` as subgroups of `Field.absoluteGaloisGroup ℚ` (cheap). -/
opaque T32_TameQuadratic : Prop

/-! ## §3. Glue -/

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are
uninterpreted. Genuine statements: `R4` (pkg-I1), `R6`, `R7` (pkg-I2), `R9` (pkg-I3), `R10`,
`R11`+`R12`, `R13` (pkg-I4), `R14`, `R15` (§1 here). -/
structure ResearchLeaves : Prop where
  r1 : R01_ShimuraDeligne
  r2 : R02_BabaGranath
  r3 : R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : R05_GonzalezRotger
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : R08_SemistableReduction
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  r10 : PkgI4.DeRhamComparison
  /-- R11 (Berger) and R12 (Pan) enter through their joint consequence: Pan's theorem with "de Rham
  at `p`" in place of "potentially semistable at `p`" (pkg-I4). `B_st` is not needed by the glue.
  Both theorems remain separate leaves in the count. -/
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
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
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : T09_WeilPairing
  t10 : T10_TateDuality
  t11 : T11_RiemannGAGA
  t12 : T12_ArtinComparison
  t13 : SkolemNoether
  t14a : PkgI6.BrauerHasse2
  t14b : PkgI6.BrauerReciprocity2
  t15 : PkgI6.LocalH2Card
  t16a : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p
  t16b : PkgI6.LocalReciprocityUpper
  t17 : KroneckerWeber
  t18 : FrobeniusDense
  t19 : BrauerNesbitt
  t20 : GlueConductor.HilbertDifferentFormula
  t21 : GlueConductor.SerreDifferentBound
  t22a : PkgI6.HerbrandQuotient
  t22b : PkgI6.HerbrandTransitivity
  t23 : T23_FontaineClosure
  t24 : EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomy
  t28 : PkgI1.IgusaClebschSeparation
  t29 : T29_LocalNormalizers
  t30 : GlueDescent.B2Q.LeafSqrtCrit
  t31 : GlueDescent.B2Q.LeafUnramified
  t32 : T32_TameQuadratic

/-- **The glue G1-G17 and G19 (non-Arakelov part).** The leaves give glue-assembly's interface
`GlueOutputs` at `S = Mult.S_mul`: for each `u ∉ 𝒞`, the theta point `z` of the QM surface over
`J(u)`, a real `h_A` (the Faltings height of `A`) with Pazuki's bound, and the numerical outputs of
the non-CM transfer. Not proved: the glue needs the definitions of §4 of the note, and most leaves
are placeholders. `GlueOutputs` is an intermediate contract, not a leaf. -/
theorem glueOutputs_of_leaves (_r : ResearchLeaves) (_t : TextbookLeaves) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  sorry

/-- **G18-G20, proved** (glue-assembly): `GlueOutputs Mult.S_mul → SixContactMin`, through F2
over Mathlib's Weil heights, the E2-E4 and F3 arithmetic, the final constant, and F4.
`GlueAssembly.SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin` by definition. -/
theorem sixContactMin_of_glueOutputs (h : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul) :
    ZInQ.SixContactMin :=
  GlueAssembly.sixContactMinAt_of_glueOutputs h

/-- The scratch copy of `JHeightBound` in glue-assembly is the repository's. -/
theorem jHeightBound_copy_iff :
    GlueAssembly.JHeightBound ZInQ.Mult.S_mul ↔ ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul :=
  Iff.rfl

/-- **G0. The leaves imply `SixContactMin`**: G1-G17, G19 (`sorry`) then G18-G20 (proved). -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves r t)

/-- **G20 alone** (the existing proof in `ZInQKernel`), for reference. -/
example (h : ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul) : ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound h

end HSyn

end

#print axioms HSyn.weight_match
#print axioms PkgI2.inertiaTrivial_of_goodReduction
#print axioms PkgI2.D2_fixed_of_raynaud
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.level_le
#print axioms GlueConductor.fourth_pow_mem
#print axioms HSyn.sixContactMin_of_glueOutputs
#print axioms PkgI1.f1_algebra
#print axioms PkgI1.equiv_of_lyVec
#print axioms PkgI3.exists_hom_ne_zero_of_equivariant
#print axioms PkgI3.finrank_equivEnd
#print axioms PkgI6.eq_of_same_finite_support
#print axioms GlueAssembly.twist_finite
#print axioms GlueAssembly.index_Gamma1_le
#print axioms GlueAssembly.mulHeight_le_mulHeightL2
#print axioms GlueAssembly.invariants_ne_bot_of_baseChange
#print axioms GlueDescent.B3Q.b3_degree_le_QM
#print axioms GlueRepo.PR.inertia_orders_eq_one_iff
#print axioms GlueRepo.PR.fibre_free
#print axioms HSyn.sixContactMin_of_leaves
