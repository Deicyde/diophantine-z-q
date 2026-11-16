# pel-hodge (2026-11-16)

**Result.** holfam's leaf `HolFamilyPrinted.PELHolFamily` (Deligne's PEL curve M_K3/Q, universal QM abelian scheme,
holomorphic τ ↦ [τ,1] with fibre ℂ²/ι(𝒪)(τ,1)ᵀ) is proved in Lean from a new leaf `PELHodge.PELHolFamilyHodge`
stated in the print's Hodge / H₁ form, plus the textbook field `uniformizationLeafAll` (gagaMorphism not needed):
`PELHodge.pelHolFamily_of_hodge`. The converse is proved too (`pelHolFamilyHodge_iff`), so the new leaf is not
stronger. File `ZInQKernel/Contrib/OneProof/PELHodge.lean` (imports HolFamilyPrinted and UniformizationPrinted).

**The H₁ form, over Mathlib.** H₁(A(ℂ),ℤ) := π₁(A(ℂ),0)ᵃᵇ (Mathlib `FundamentalGroup`, `Abelianization`) for
unif-printed's classical topology (= analytic topology, unif-topology). The fibre clause `IsHodgeFibre τ P`: a
holomorphic ι-compatible homomorphism e = exp∘L : ℂ² → P.A(ℂ) killing Λ_τ with v ↦ [t ↦ e(tv)] a bijection
Λ_τ ≃ H₁, i.e. (H₁, 𝒪, Hodge structure) ≅ (𝒪, left mult., h_τ). The glue `h1Form_iff` identifies H₁(A(ℂ),ℤ) with
the period lattice: the uniformization is a homeomorphism for the classical topology, φ∘proj is a quotient covering
map, Mathlib's monodromy `fundamentalGroupToMulOpposite` is injective, plus a rank count (`ZLattice.rank`).

**Rating.** `pelHolFamilyHodge`: published, printed form (the fibre clause is now the print's H₁/Hodge
description; dictionary H₁ = π₁ᵃᵇ, Lie A via holomorphic homs, ker exp ≅ π₁). Flag "unread"; holfam's analytic
clause (M_K(ℂ) ≅ Sh_K as complex spaces) to be checked in the same reading (if not printed: pending reading).
Count with mtcm-polar's MainTheoremCM: composite out, −1 strict GLUE (SPECULATIVE until folded).

**Compiles (VERIFIED; first on holfam's fold25 build tree, then on fold28b, below):** the file (0 errors/warnings); `#discharges` (no field matched, as expected before holfam's fold;
18 theorems standard axioms; scratch/pel-hodge/Discharges-output.txt); bypass dry runs `BypassFold.lean`
(frozenTarget_pelHodge) and `BypassFoldPi0.lean` (consumers via `gonzalezRotgerX6Ab`, no
deligneComponentsX6PrintedAb; for pi0-prune). Specs: scratch/pel-hodge/autofold.json (after holfam's fold),
autofold-bypass.json (in place of holfam's spec, with pi0 consumer terms). autofold.py cannot dry-run either
(pelHolFamily is not yet a field; the bypass is a hand fold).

**fold28b (VERIFIED):** `lake build` of PELHodge on the merged fold28b tree (12904 jobs, FLT port included) and of
Main + Discharges (13667 jobs) succeed; `#discharges` there: 61 open, 8 discharge one, no PELHodge match, 18 axiom
checks standard; both dry runs compile on fold28b too. A read-only model review found no soundness issue.

**Remains.** The reading (Deligne 389 §§4.9–4.17, Ex. 5.8; Milne ISV §§8, 14; locators UNVERIFIED); the fold (after holfam's, or in its place);
pi0-prune itself is not merged here. Report: docs/research/pel-hodge.md.
