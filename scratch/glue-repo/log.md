# glue-repo results log

Task: steps A1, A3, A5-A8, A10 of docs/research/h-trust.md. Marks: VERIFIED (read, computed or
compiled), STANDARD (published, reference), SPECULATIVE. Locators from memory are UNVERIFIED.

## Computations (scratch/glue-repo/compute.py, ~/pyenv/bin/python -I)
- VERIFIED: Trd(a μ⁻¹ ā μ) = 2x0²+4x1²+18x2²−48x2x3+36x3² (a = x0+x1 i+x2 j+x3 ij); leading
  minors 2, 8, 144, 576: positive definite (Rosati involution positive).
- VERIFIED: Res(F,G), Res(F,H), Res(G,H) supported on {2,3,5}; Bezout denominators on {2,3,5}.
- VERIFIED: structure constants of 𝒪 in the basis (1,i,(1+j)/2,(i+ij)/2) are integer
  polynomials (§4); Rosati involution in 𝒪-coordinates is integral (§5).
- VERIFIED (box |coord| ≤ 12, and proved by parity in general, see PRArith): every x ∈ 𝒪 with
  trd 0, nrd 3 has (1+x)/2 ∈ 𝒪.

## A1Quaternion.lean — COMPILED (lake env lean, no errors, no sorry)
B = ℍ[ℚ,2,0,-3] (Mathlib QuaternionAlgebra); 𝒪 = Set.range comb as a genuine `Subring B`.
Theorems: μ_mul_μ (μ²=-6), μ_mul_μinv, comb_mul (integral structure constants), O (subring),
e_mem, star_mem, ros_mem (𝒪 stable under †), trace_form / det_trace_form (det Trd(eₐe_b) = -36,
reduced disc 6), gram_E (N5 L414-416 matrix), det_gram_E (= 1), E_comb (E integral on 𝒪),
E_self, E_antisymm (alternating), E_ros (E(ax,y)=E(x,a†y)), ros_ros, ros_mul, ros_add
(anti-involution), trd_mul_ros, trd_mul_ros_pos (Trd(a a†) > 0 for a ≠ 0: † positive).
