import Mathlib

/-!
# rv-loc-leaves: repaired placeholders (paste-ready for `HSyn` §2 of Leaves.lean)

These replace the docstrings of the `opaque` placeholders R02, R05, R16, R17, R22 in
`scratch/h-decomposition/Leaves.lean`. A placeholder has no content (it is an uninterpreted
`Prop`); only its recorded statement changes. Each repair follows docs/research/locators.md and is
discussed in docs/research/rv-loc-leaves.md. A small exact check of the R5 counterexample
(discriminant −19) is proved at the end.
-/

namespace HSyn

/-- **R2. Baba–Granath** (repaired after the locator audit). For the fixed principally polarized
maximal-order datum of discriminant 6: the polarized moduli space is `X₆/W` (`W` the
Atkin–Lehner group, `W ≅ (ℤ/2)²`), and `X₆/W ≅ P¹_ℚ` with the three distinguished images
rational (Canad. J. Math. 60 (2008), Thm 2.1 p. 737, Lemma 3.1 pp. 739-740: YES per the audit);
two QM surfaces with principal polarization of the fixed type have the same polarized moduli
point iff their points of `X₆` are `W`-conjugate. **Orbifold data** (§3.1 elliptic-order table,
p. 740; Prop. 3.9/Thm 3.10, p. 744; Cor. 3.11, p. 745): the group `Γ*` uniformizing `X₆/W` has
exactly three elliptic classes, of orders `4, 6, 2`, at the CM points of discriminants `−4, −3, −24`,
whose images are `j = 0, ∞, −16/27` in the normalization of Lin–Yang/N5 (the numerical
`j`-normalization is not located by Thm 2.1/Lemma 3.1; it enters through `PkgI1.QMHauptmodul`).
**Not** asserted: ramification indices `4, 6, 2` of the degree-4 map `X₆ → X₆/W`, which has
index `2` at each of the three branch values (`RvLocLeaves.fibre_t_one`, `fibre_t_zero`). The
indices `(4, 6, 2)` used by Prop. TS for `Y₃ → P¹_j` follow as glue from the orbifold orders and
the torsion-freeness of the level-3 group (`GlueRepo.TorsionFree`). Missing: `X₆`, `Γ*` acting on
`ℍ` as a curve over `ℚ`, the Atkin–Lehner group (very large, via R1). -/
opaque R02_BabaGranath : Prop

/-- **R5. González–Rotger** (repaired after the locator audit). On `X₆ = X₀(6, 1)`, for an order
`R` of conductor `f` with `(f, 6) = 1` in an imaginary quadratic field `k` that embeds optimally
in `𝒪` (so no prime dividing 6 splits in `k`): `#CM(R) = 2^b · h(R)` with
`b = #{p ∣ 6 : p inert in k}`, the group `W(R) × Gal(H_R/k)`, `W(R) = ⟨w_p : p ∣ 6 inert in k⟩`,
acting simply transitively; and `ℚ(x) = H_R` if some prime dividing 6 is inert in `k`
(`D(R) ≠ 1`), otherwise `ℚ(x)` has index 2 in `H_R`. J. Math. Soc. Japan 58 (2006), Prop. 5.6
(p. 943), Thm 5.8 (pp. 943-944), Thm 5.12 (p. 946) (YES for `X₀(D, N)` per the audit). The old
text "`#CM(R) = h(R)`" was wrong: the maximal order of discriminant −19 has `h = 1` and four CM
points (`b = 2`, `cm_count_factor_disc_neg19`). These statements are about `X₆`, not about `Y₃`
or the image in `X₆/W`. Missing: as R2. -/
opaque R05_GonzalezRotger : Prop

/-- **R16. Eichler–Shimura in `J₁(N)`** (repaired after the locator audit). For a weight-2 newform
`f` of level `N` and character `χ`, a prime `ℓ` and embeddings `ι`: `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a
`G_ℚ`-stable two-dimensional subquotient on which every arithmetic Frobenius at `p ∤ Nℓ` has trace
`ι(a_p(f))`. Assembled from three statements, none of which is the zeta clause: (i) Shimura,
J. Math. Soc. Japan 25 (1973), Thm 1 (pp. 526-527), **unconditional clauses only**: the
`ℚ`-rational quotient `A_f` of `J₁(N)` with `K_f = ℚ(a_n)` acting, `dim A_f = [K_f : ℚ]` (the
final Euler-factor clause of Thm 1 carries an extra `Γ₀`/Fricke-stability condition and is not
used); (ii) `V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ` (Shimura 1971 §7.4 / Ribet 1977;
UNVERIFIED locator); (iii) the Eichler–Shimura congruence relation `T_p = Frob_p + p⟨p⟩Frob_p⁻¹`
on `J₁(N)` mod `p ∤ N` (Shimura 1971 Thm 7.9; UNVERIFIED), which gives on each
`V_λ(A_f) = V_ℓ(A_f) ⊗_{K_f ⊗ ℚ_ℓ, ι} ℚ̄_ℓ` the characteristic polynomial `X² − ι(a_p) X + ι(χ(p)) p`.
(With the other Hecke convention on `J₁(N)` the trace is `ι(conj a_p)`, which is the case of the
conjugate newform `f^ρ`; the statement over all newforms is unaffected.) Missing: `X₁(N)`,
`J₁(N)` over `ℚ`, Hecke correspondences (very large). -/
opaque R16_EichlerShimuraJ1 : Prop

/-- **R17. Carayol's local–global compatibility** (repaired docstring; the concrete statement is
`LadicCond.CarayolR17'` of scratch/def-ladic-cond, unchanged). For a weight-2 newform of level `N`,
any prime `ℓ` (including `ℓ = 2`) and any prime `p ≠ ℓ` (including `p ∣ N`), the Artin conductor
exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411,
§0.8 p. 411 (coverage of `p ∣ N` and `ℓ = 2` YES per the audit; the extra discrete-series
hypothesis concerns only totally real `F` of even degree, not `ℚ`), with the newform conductor
`a(π_p) = v_p(N)` (Casselman 1973; UNVERIFIED locator). Duals and unramified twists do not change
the conductor. Do not replace by Théorème (B) or by the `Γ₀` elliptic-curve corollary. -/
opaque R17_Carayol : Prop

/-- **R22. Pazuki** (repaired after the locator audit). For a principally polarized abelian
surface `A` over a number field, with `H_Θ = max(1, h_Θ(A))` (`h_Θ` the level-2 theta height of
the paper, Euclidean norms at infinite places) and `H_D = max(1, h_D(A))`, `h_D` the Faltings
height in **Deligne's** metric: `|H_Θ − H_D/2| ≤ C₂ log(min(H_Θ, H_D) + 2)`, `C₂ = 1000·2⁴(log 2⁴)⁵`.
Bull. Soc. Math. France 140 (2012), Cor. 1.3(2), p. 21-22 (`g = r = 2`), metric p. 26, theta
height p. 30. In the original Faltings normalization `h_F`, `h_D = h_F + log π` (`g = 2`), so
for any `X ≥ max(1, h_F + log π)` (in particular `X = max(1, h_F + 3)`):
`h_Θ ≤ X/2 + C₂ log(X + 2)` (proved: `ZInQ.PkgI5.pazuki_upper_of_literal`,
`pazukiGoodGenus2'_of_literal` in scratch/rv-loc-leaves/PazukiR22.lean). Consequence, not the
literal corollary. Missing: Faltings height and theta height of abelian surfaces (very large;
special case statable now: `ZInQ.PkgI5.PazukiGoodGenus2Literal`). -/
opaque R22_Pazuki : Prop

end HSyn

namespace RvLocLeaves

/-- The local factor of González–Rotger's count at discriminant `−19`: `2` and `3` are both inert
in `ℚ(√−19)` (`(−19/3) = −1`, and `−19 ≡ 5 mod 8`), so `b = 2` and `#CM = 4·h = 4`. -/
theorem cm_count_factor_disc_neg19 :
    jacobiSym (-19) 3 = -1 ∧ (-19 : ℤ) % 8 = 5 := by
  refine ⟨by norm_num, by decide⟩

/-- At discriminants `−4` and `−3` the factor is `2` (`(−4/3) = −1`, `−3 ≡ 5 mod 8`), matching the
two elliptic points of each order 2 and 3 of `X₆` (`h = 1`). -/
theorem cm_count_factor_disc_neg4_neg3 :
    jacobiSym (-4) 3 = -1 ∧ (-3 : ℤ) % 8 = 5 := by
  refine ⟨by norm_num, by decide⟩

end RvLocLeaves

#print axioms RvLocLeaves.cm_count_factor_disc_neg19
#print axioms RvLocLeaves.cm_count_factor_disc_neg4_neg3
