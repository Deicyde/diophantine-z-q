# leaf-push (fleet report)

**Result.** 5 of the 19 placeholders of h-decomposition.md now have concrete Lean statements
over genuine definitions, each the published theorem or a consequence of it: R8 (Grothendieck,
monodromy form, = pkg-I2's `GrothendieckMonodromy`), T9 (Weil pairing, finite-level Galois form
valid for every invertible `n`, nondegenerate up to the polarization degree `d`: enough for
`GSp` on `V_ℓ` at `ℓ = 5`), T29 (local normalizers of maximal quaternion orders: division case
index exactly 2, split case `ℚ_p^×GL₂(ℤ_p)`), T32 (inertia subgroups of `G_ℚ` via Mathlib's
`ValuationSubring.inertiaSubgroup`: unique quadratic character of tame inertia for odd `p`;
`√d` moved by inertia iff `p | d`), T23 (Fontaine's closure: basis change, dual, subquotient,
sum, tensor, over pkg-I4's `IsDeRham`). Count: 40 of 54 leaves concrete (was 35).

**Compiles (VERIFIED).** `scratch/leaf-push/Push.lean` (R8, T9, T29a/b, T32a/b) and
`scratch/leaf-push/PushDR.lean` (T23), no errors; they contain verbatim copies of pkg-I2's
abelian-variety layer and pkg-I4's B_dR layer (to be replaced by imports on integration).
Statements only; no glue consuming them yet.

**Remaining (14), with the missing definition.** R1 (polarizations/dual abelian scheme, PEL
moduli); R2, R5 (canonical model of `X₆`; ring class fields; the analytic form of R2 is empty up
to Möbius, the analytic form of R5 needs R2+R3+R4); R3 (genus-2 Jacobians); R16 (`X₁(N)`,
`J₁(N)` over ℚ); R17 (absolute upper ramification filtration of `G_{ℚ_p}` and the Artin conductor
of an ℓ-adic representation; medium, pkg-I6 has the finite-level `upperRam`); R18-R22 (Faltings
height; theta height); T10 (étale cohomology); T11, T12 (analytification).

Report: docs/research/leaf-push.md. Log: scratch/leaf-push/log.md.
