# y3-x6 report notes (working file)

## HeckeSqrtBranchAny on the Y3 route: why the manuscript cannot supply it verbatim

* Statement (SGRDirectNV.lean:1143): for every triple (Y, Φ, π) with R1fp, R1hecke, R2fp, every finite Galois
  E/ℚ(X) with the normalization chart (Spec of the integral closure of ℚ[X] in E is an open of Y with π = X),
  ∃ c ∈ ℚ^×, s ∈ E, s² = c(27X + 16). No X6 in the statement.
* Consumer: SGRDirect.heckeVertWitness_of_nvSqrtAny (Lemma NV route of sgr-direct) -> HeckeVertWitness -> PropTSAll.
* Old source: Elkies' model of X6 (ℚ(X6) = ℚ(X)(√X, √(−(27X+16)))) through Y3 -> X6 dominant.
* The manuscript's route (L481-526): stable model, tame action at p > 324, integral model of the quotient, pullback by
  J(u), tame normalization, local equation u − c = z² at the six contacts. It is a LOCAL statement at primes
  p > 324 after unramified extension; it never asserts a global square root in the Galois closure of Y3 -> P¹_j.
  Re-routing HeckeSqrtBranchAny "to the tame local equation" therefore means replacing the NV route's consumer
  (HeckeVertWitness), not HeckeSqrtBranchAny itself; that is the integral-model route the tree replaced by NV
  (sgr-direct), and it needs the stable-model / tame-quotient steps L481-509, which are not in Lean.
* Y3-only argument for HeckeSqrtBranchAny (ON THE SPOT, glue, not proved):
  1. The Hecke automorphisms (twists α ∈ Aut 𝒪, rightMul u ∈ 𝒪^×; R1heckeProps) are ℚ-automorphisms of Y preserving
     π (fibres = Aut 𝒪-twist classes, Y3ToP1jAt), and act transitively on every geometric fibre; so the image Γ of
     the group they generate in Aut(ℚ(Y)/ℚ(X)) has ℚ(Y)^Γ = ℚ(X), i.e. ℚ(Y)/ℚ(X) is Galois with group Γ (a quotient
     of N/(A_f^× K3), order ≤ 144).
  2. Inertia: the branch values are 0, ∞, −16/27 with indices 4, 6, 2 (L421-422, L500); the inertia generators
     σ0, σ∞, σ_{-16/27} (orders 4, 6, 2) with σ0 σ∞ σ_{-16/27} = 1 generate the geometric monodromy.
  3. The character χ : Γ -> Γ/Γ_{(Aut 𝒪-inner, O^1 part)} -> W ≅ (ℤ/2)² -> ℤ/2 that kills the class of w for which
     X6/<w> -> P¹ is unramified over 0 (Baba–Granath's table: the CM(−4) points are fixed by w2, CM(−3) by w3 ... ;
     cf. the ALFixedPoints leaf) has χ(σ0) = 0, χ(σ∞) = χ(σ_{-16/27}) = 1.
  4. The fixed field of ker χ is a quadratic extension of ℚ(X), geometrically ramified exactly over ∞ and −16/27,
     hence ℚ(X)(√(c(27X+16))) with c ∈ ℚ^× (a quadratic extension ℚ(X)(√f), f squarefree in ℚ[X] up to ℚ^×
     constants, is ramified exactly at the roots of f and at ∞ iff deg f is odd).
  Step 3 is where X6/W (the AL group) enters in group-theoretic form only; the manuscript's N/(A_f^× K0) = W
  (L425-429) supplies W without X6. Not formalized (Galois theory of function fields + monodromy).
