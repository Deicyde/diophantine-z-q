# Separately authored mathematical review of the derivative-switch packet

### 1) Verification target

- **Reviewer and role:** non-author model reviewer, Codex (GPT-6 family; no more specific backend model identifier is exposed to this agent), task `/root/packet_math_review`. This review was authored by this agent, separately from the ingestion author. Different agent identities do not establish uncorrelated reasoning or human independence.
- **Date and frozen target:** 2026-11-08; repository `/Users/chey/Coding_Projects/diophantinezq/derivative-switch-review`, commit `dbef6c581abd407e03f0729f6462dc86d2e5f4c2`. The worktree was clean at both source inspections.
- **Scope:** the six declarations in `lean/Research/DerivativeSwitchBoundary.lean`, their mathematical statements and elementary proofs, the ordinary-algebra bridges in `research/determinant-switch/CONTRACT.md`, and the mathematical interpretation of `check_local_model.py`. I read the source and re-derived the inference before reading the existing verification verdicts. The saved elaborated-statement log was subsequently compared with the source; it is historical output, not a fresh elaboration by this reviewer.
- **Permitted work:** read-only repository inspection and independent finite sanity checks; this new report is the only file written by this reviewer. No Lean build, original packet checker invocation, repository edit, external-checker execution, push, or publication was performed.
- **Source lookup:** the supplied packet, `AGENTS.md`, its linked `docs/audit-history/PROTOCOL.md`, `docs/research-review/PROTOCOL.md`, and the owning V13 passages at `manuscripts/quartic_v13.tex:4014–4029`, `5020–5093`, together with the adjacent consumer at `5095–5145`. The paired-functional statement at `3842–3868` was inspected solely to identify the distinct arithmetic object. This is not a review of Nekovar, H19–H22, the manuscript's arithmetic proof, or the completeness of its historical audit inventory.
- **Claimed new coverage assessed:** four conditional boundary lemmas over fields and two polynomial area identities over commutative rings. The occurrence of `AxesKernel` in the arithmetic setting and transport of the actual class-functional tensor remain outside this acceptance.

SHA-256 binds the raw file bytes, without normalization:

| Source | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitchBoundary.lean` | `63a9215fa55568069d2d1a7b2c3a7345ec21c7ad6a82203f42c5451ee4b8bbea` |
| `research/determinant-switch/CONTRACT.md` | `33e6ff462a61dac95afc27a016efc118cb75a0d550e33a206daca66055da96cb` |
| `research/determinant-switch/check_local_model.py` | `2bdf4fa6ead8c8e656f9b49d9d745a7274f7d3daf81915eb88727271d8988ef1` |
| `research/determinant-switch/evidence/statements-compact.log` | `905f1ff38d1853402a1304f52ea5437e8f57f064f87213469ce61d734bc59bca` |
| `research/determinant-switch/README.md` | `61564eac3f34fd083fc7f091178be1a1598bdfcae35170a74d6234915806454e` |
| `research/determinant-switch/VERIFICATION.md` | `eaf4ae005d943d64a009419bf73bcf6a680bd0c443fe6ac5d13f745e4fa8d285` |
| `research/determinant-switch/PROVENANCE.json` | `09b4743868b2f394cece113ae8cc57097520642ef9465e5a1baaf01d51d7408b` |
| `manuscripts/quartic_v13.tex` | `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` |
| `AGENTS.md` | `8962f442f897f69d6f001a589eeae22881bda75b77f1b77e7f30f3b7d50e0bfb` |
| `docs/audit-history/PROTOCOL.md` | `c0b9834a75e64bfd66183b06d1e26019f957a38468ce41b10ce290f8c5c44816` |
| `docs/research-review/PROTOCOL.md` | `b5365b3d9cd9a782bf7fd0b6020403d5d400eac13dc7e60875484a8769d3d925` |

For the manuscript, inclusive line slices retain their original line endings: `4014–4029` has SHA-256 `94dc4307df0b9cce6a6f878d58a744cbd5dd08c447cad72e1f79085cba1e920e`; `5020–5093` has SHA-256 `2f23916a10a7bf9724f702d575fd6cf620023d811730b77f4cbcc7a460d57680`.

### 2) Independent re-derivation (outline)

Write `L(x,y)=dF(x)+dS(y)`. `AxesKernel` says exactly that `ker L=Kv × K(Jv)`, including both implications. This is stronger than separately specifying the two kernels: it also excludes cancellation between nonzero images.

| Declaration and source lines | Independent derivation and disposition |
| --- | --- |
| `finite_kernel_line`, 43–56 | Intersect `ker L` with `F × {0}`. Its first-coordinate projection is exactly `Kv`, hence `ker dF=Kv`. The zero singular coordinate has the scalar representation `0·Jv`. **Accepted as stated.** |
| `singular_kernel_line`, 59–72 | Intersect `ker L` with `{0} × S`; project to the second coordinate. The result is exactly `K(Jv)`. **Accepted as stated.** |
| `boundary_images_meet_zero`, 76–88 | If `h=dF(x)=dS(y)`, then `(x,−y)∈ker L`, so `x∈Kv` and `dF(x)=0`. Thus `h=0` and both images vanish. This proves the stated elementwise form of `im dF∩im dS={0}`. **Accepted as stated.** |
| `no_identity_strict_square`, 94–108 | If the boundary square commuted, every `dF(x)` would belong to both images and hence vanish. The first lemma would then put every `x` in `Kv`, contradicting `hout`. **Accepted as stated, with `hout` essential.** |
| `Volume.area_action`, 125–129 | Expanding gives `(av₁+bv₂)(cw₁+dw₂)−(cv₁+dv₂)(aw₁+bw₂)`. Commutativity cancels the diagonal terms; the remaining expression is `(ad−bc)(v₁w₂−v₂w₁)`. **Accepted over the declared arbitrary commutative ring.** |
| `Volume.area_neg_one`, 133–139 | Substitute determinant `−1` and original area `1` into the preceding identity. **Accepted as stated.** |

The first four proofs use additive inverses, linearity, and scalar-span membership; none uses division, finite dimension, characteristic zero, or nonzero `v`. They are stated only over fields in this file; possible weakening of that typeclass is not a claimed additional formal result. The last two explicitly cover rings with zero divisors and the zero ring.

For the intended two-dimensional nonzero case, an `x` outside `Kv` exists. The image vectors `a=dF(x)` and `b=dS(Jx)` are nonzero and independent: their separate kernels are the prescribed lines, and their images have zero intersection. Consequently, if `H` is two-dimensional, the linear map `T(a)=b`, `T(b)=−a` has determinant one and satisfies `T∘dF=dS∘J` because `(v,x)` is a basis. This confirms the ordinary generic boundary observation in contract lines 79–82. It proves no lift to an integral complex automorphism. At the separately posited outer test with `dF=0` and injective `dS∘J` on a nonzero plane, `T∘dF=dS∘J` is impossible for every `T`. The occurrence of that outer test is not established here.

For the DVR volume bridge, if `v=π^k v₀` with primitive `v₀=(r,s)`, choose `αr+βs=1`. Then `x₀=(−β,α)` has area one, and `x=π^(−k)x₀` gives `area(v,x)=1` over the fraction field. An integral matrix of determinant `−1` gives `area(Jv,Jx)=−1`. Its inverse is integral, so, for explicitly chosen integral lattices `F_R,S_R`, it induces `F_R/Rv ≅ S_R/RJv`, and therefore an isomorphism of their finitely generated torsion submodules and equality of their Fitting ideals. This is ordinary algebra, absent from the six declarations.

For the Python cofactor model, let the complex have degrees one and two, with ordered domain and codomain bases and differential `D`. The displayed matrices have rank two over the fraction field. Their adjugates are

```text
adj(D_F) = [[0,0,0],[0,a,0],[0,0,0]],
adj(D_S) = [[0,0,0],[0,0,−a],[0,0,0]].
```

The implementation's deleted row is `j` and deleted column is `i`; that is the correct transpose for `adj(D)[i,j]`. With `s=2^k`, `z=s e₂`, `λ_F=s f₂*`, and `λ_S=s f₃*`, the equation `zλ=u·adj(D)` therefore gives `u_F=s²/a` and `u_S=−s²/a`. All other matrix entries must be zero and the code checks them. Since `a=2^m≠0`, the adjugate is nonzero and this determines `u` uniquely.

The determinant-line interpretation is justified by a basis calculation, rather than merely defining a ratio to obtain the desired answer. In the finite complex, use kernel basis `e₂`, complement `e₁,e₃`, image basis `a f₁,f₃`, and cokernel basis `f₂`; the alternating domain and codomain basis signs cancel, giving the inverse-determinant coordinate `s²/a`. In the singular complex use the same kernel and complement, image basis `a f₁,f₂`, and cokernel basis `f₃`; the relative sign reverses, giving `−s²/a`. This matches the manuscript convention `det⁻¹C ≅ H¹(C)⊗H²(C)*` in the inspected definition.

The shared strict complex is `[R e₁ → R³]`, `e₁↦a f₁`. Its degree-two cohomology is `R/(a) ⊕ R²`; each plane complex retains the same `R/(a)` torsion summand. Its inverse determinant contributes the `1/a` factor. Each quotient by the strict complex is the degree-one plane with basis `e₂,e₃`. The chosen classes have quotient coordinates `(s,0)`, fixed by `J=diag(1,−1)`. Thus this example has the promised common strict factor and actual local coordinate relation. The determinant map induced by `J` also has sign `−1`, consistent with the two computed coordinates. Replacing only `λ_S` by `2λ_S` changes the coordinate to `−2s²/a`; the comparison has gained a nonunit at the prime two while all those local data remain unchanged. This validates the negative control and does not identify either functional with an arithmetic duality-defined functional.

### 3) Checks

- **Plug-back checks:** the formulas for the two kernels, vanishing common image, and determinant action match all quantifiers in the source and saved elaborated statements. No extra hypothesis is supplied by a comment or theorem name.
- **Zero-vector boundary:** when `v=0`, `AxesKernel` asserts that the combined map is injective. Both individual kernels are zero. No dimension-one conclusion follows. This case is consistent, for example with `H=F⊕S` and the two inclusions. If `F≠0`, `hout` holds and the no-go conclusion is correct.
- **Necessity of `hout`:** take `F=S=K`, `v=1`, `J=id`, `H=0`, and zero boundary maps. Every pair is on the prescribed axes, so `AxesKernel` holds and the boundary square commutes. The omitted `hout` would make the theorem false. More generally, under `AxesKernel`, if `F=Kv`, both boundary maps vanish because `J` is surjective. The excluded degenerate case is therefore real.
- **Characteristic and ring boundaries:** in characteristic two the minus signs equal plus signs; the arguments remain valid, including the no-go witness. In the zero ring the area conclusions are valid identities without a nontrivial-volume conclusion. No division is used by the two formal volume lemmas.
- **Python domains:** the default generic countermodel uses `a=3≠0`; its exact rank and kernel claims follow directly from its matrices. The normalized torsion examples use `m=1,…,11`, `k=0,…,11`, so all denominators are nonzero. Scaling a closed functional preserves closedness. `Fraction` performs exact rational arithmetic. The script's `__debug__` guard rejects disabled assertions. The finite randomized integer volume checks are illustrative regressions, not a proof of their universal statement.
- **Independent computation:** this reviewer ran a separate ephemeral Python program, without writing files. It checked the nonzero-axis model and the zero-vector direct-sum model over fields of orders 2, 3, and 5; checked 65,792 area identities exhaustively over `Z/2` and `Z/4`; and checked the numerical cofactor instance `a=8,s=4`, yielding `2`, `−2`, and `−4` after functional rescaling. All passed. These sanity checks neither replay the packet's recorded run nor replace the derivations above.
- **Extraneous-solution checks:** no division occurs in the boundary proofs. The cofactor and fractional-complement calculations occur only over the fraction field with their nonzero denominators stated. The ring-level volume identity needs no invertibility premise.

The nine application obligations, within this review's limited scope:

| Obligation | Assessment |
| --- | --- |
| Source hypotheses | The six declarations match their explicit algebraic hypotheses; `AxesKernel` remains assumed. The cohomology-dimension bridge needs the additional source hypothesis recorded in finding M1. |
| Constructed objects | Abstract modules, two maps, a linear equivalence and a vector are explicit. Python matrices, cycles and functionals are explicit. Actual arithmetic complexes/functionals are not constructed. |
| Domain and index coverage | All field/module elements are quantified in the formal statements; no arithmetic family or height-one coverage follows. The Python parameter ranges are finite and stated. |
| Transition/comparison maps | The prohibited square is precisely `dF=dS∘J`. The allowed generic `T` is only a boundary-space construction. The model's determinant sign agrees with its `J`. |
| Consumed-object identity | The six outputs are kernel/image and area identities. They are not the integral Selmer tensor equality. The model's chosen functional is identified explicitly and is not substituted for the arithmetic one. |
| Coefficients/normalization | Any field for the first four, any commutative ring for the last two, and exact rational/DVR interpretation for the model. Integral lattice notation needs clarification M2. |
| Local conditions | Actual Selmer local conditions and homotopies are outside this target. The displayed common-strict model and its degree-one quotients are identified above. |
| Exceptional cases | Zero vector, missing outside vector, characteristic two, zero ring, divisible vector, nonzero cofactor denominator, and strict torsion have been checked. |
| Downstream consumption | The packet labels arithmetic compatibility open, and the owning manuscript/consumers are unchanged. No application to those consumers is accepted by this report. |

### 4) Discrepancy report (if any)

**M1 — Explicitly condition the generic `H¹` dimension statement.** Target: contract lines 51–52 and 98–99; the parallel explanation in `VERIFICATION.md` also mentions actual exact sequences without explicitly naming strict `H¹` vanishing.

The six abstract lemmas imply one-dimensional *boundary kernels* when `v≠0`. Even after supplying the two triangles, exactness gives

```text
0 → H¹(C_str) → H¹(C_F) → Kv → 0,
0 → H¹(C_str) → H¹(C_S) → K(Jv) → 0.
```

Thus generic `H¹` dimension one additionally needs `H¹(C_str)=0`. A counterexample to the implication without this premise is obtained by adding a nonzero zero-differential degree-one summand to the strict complex and both plane complexes: the boundary data and `AxesKernel` are unchanged, but both `H¹` dimensions increase.

This is a **located source justification / incomplete local statement of premises**, not a newly discovered arithmetic gap. V13 lines 5030–5035 and 5076–5079 assume that the old class spans the old generic `H¹` and has nonzero localization. In the first exact sequence, the localization is injective on that old line, hence strict `H¹=0`; the second sequence then identifies the new `H¹` with `K(Jv)`. Make this premise/bridge explicit in the packet, or describe only the dimensions of `ker dF` and `ker dS`. No Lean statement or proof needs alteration. The arithmetic occurrence of those source assumptions remains unreviewed here.

**M2 — Name the lattices in the quotient/Fitting-ideal bridge.** Target: contract lines 67–69 and 105–108.

Earlier `F,S` denote vector spaces over the generic field. The claimed torsion/Fitting comparison is correct for integral free rank-two lattices `F_R,S_R` and an integral isomorphism `J_R`, as shown above. Literal vector-space quotients `F/Rv` over `R` need not be finitely generated and can have torsion such as `L/R`; that reading does not justify the stated finite-module Fitting-ideal claim. Explicitly use `F_R/Rv → S_R/R(J_Rv)` and identify the lattices. This is a **notation/domain clarification of the existing intended ordinary-algebra bridge**, not a counterexample to the six lemmas.

No defect was found in the six formal statements, their displayed elementary proofs, or the cofactor-model inference. No prior PASS label is used to resolve either finding. These two proposed clarifications affect the packet's explanatory contract, not the unchanged arithmetic manuscript. Final acceptance of revised documentation requires a new reviewer-authored binding to its actual bytes.

### 5) Certification result

**CERTIFIED under their exact stated algebraic assumptions:** the six abstract statements and the mathematical cofactor interpretation inspected at the frozen commit. Repository protocol decision: **Accepted within stated scope** for this algebraic core.

**Changes required for unqualified acceptance of the full explanatory contract:** clarify M1's strict-`H¹` premise and M2's integral lattices, or narrow the corresponding prose. These are bounded statement-precision corrections; no change to the six theorem bodies is requested. This report does not accept any future edited bytes in advance.

This is a separately authored model mathematical review, not a fresh kernel replay, external-checker result, human review, whole-manuscript validation, arithmetic integration, release acceptance, or proof of Selmer tensor compatibility. The actual `Phi_det([A]⊗[lambda_A])=epsilon([B]⊗[lambda_B])` for the exact arithmetic functionals remains open and was not attempted.
