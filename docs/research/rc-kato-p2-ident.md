# Cohomology and coefficient identifications for the dyadic Kato reroute

**Scoped stop.** The real sign (tex 7222) is a consequence of the
actual elliptic Tate representation. The remaining arithmetic
identifications cannot be supplied from this base without further GLUE
beyond `FixedKatoFiniteComparison`. In particular the geometric odd
support triangle has no supplier on the actual integral tower, and
the project does not yet have the original regulator classes or their
comparison with the de Rham and Betti elements. The separate Appendix E
assembly after (K15) is also still an input. The corrected reroute remains
conditional; issue #168 is not ready to close.

**Known manuscript issue (carried forward):** tex 1884–1893 and
7206–7241 apply Kato 2004 at two using a hypothesis check that does not
justify the application. In particular the cyclotomic fixed-space argument
does not itself give a witness over the maximal abelian extension.
The [corrected reroute](rc-kato-p2-reroute2.md) uses Kato, *Kodai Math.
J.* 22 (1999), Thm. 0.8 (locator from the reading desk, not reread here),
with that stronger witness, full local support, inverse-Frobenius
purity, and primewise torsion. No new manuscript error is established here.

## What the Lean files supply

| Declaration | Discharge |
| --- | --- |
| `KatoP2.realConj_sq`, `KatoP2.realConj_tate_det` (private) | The actual Galois element is an involution because its complex action is conjugation. Its integral Tate determinant therefore squares to one. The value `1` would fix the dyadic roots of unity by the existing Weil pairing proof, but conjugation moves a square root of `-1`. |
| `KatoP2.finrank_ker_add_one_of_involution` (private) | In dimension two, if `A² = 1` and `det A = -1`, then `A(A+1) = A+1` forces `det(A+1) = 0`. The kernel of `A+1` is proper because `A = -1` would give determinant `1`. Thus its dimension is one. This is a linear algebra lemma, with no cohomology or class assumption. |
| `KatoP2.rationalTwist_realSigns` | Provides both sign lines of actual complex conjugation on `rationalTwist E χ`, with only ellipticity and the given quadratic character. The determinant comes from the existing Tate calculation. Base change preserves it, and twisting by `±1` has determinant multiplier `(±1)²`. Applying the lemma to `A` and `-A` gives both lines. The negative line is exactly the field used by the corrected draft. |
| `KatoP2.Checked.KodaiConstituent.ofArithmetic` | Builds the existing constituent with the real sign proof filled in. It accepts its other existing object and arithmetic fields and keeps `d = |h|` and `D = d * 2^a` with the full odd filter. It introduces no new structure or Prop assumption. |

Construct each `KodaiFamilyData.part` with `ofArithmetic`. The result
already has the type used by `AppEFromKatoP2`,
`appEOutputs_of_katoP2`, `evenScalar32_of_katoP2`, both `_fixed`
wrappers, and the `_ecurve` scalar and lower bound wrappers. These
consumers retain their existing types and can now be supplied with
constituents without a real sign premise. No unconditional substitute
for them is claimed. The finite anchor is a separate consumer:
`exists_nonzero_image_of_anchored_weightedSum_p2` still uses
`RetainedReciprocity` and `KatoFiniteComparison`; its fixed comparison
is the existing `FixedKatoFiniteComparison`.

**Count delta:** one previously supplied field is proved and filled by
the constructor; four Lean theorems (three private) and one constructor
are added. Δ new LEAF = 0; Δ new GLUE assumptions = 0;
Δ registered/frozen hypotheses = 0. The corrected Kodai draft and fixed
finite comparison remain. The original registry and consumers are untouched.

**Verification (VERIFIED):** both [RealSign.lean](../../ZInQKernel/Contrib/OneProof/RC/KatoP2/RealSign.lean)
and [RealSignBridge.lean](../../ZInQKernel/Contrib/OneProof/RC/KatoP2/RealSignBridge.lean)
elaborate individually with `lake env lean`. The
[axioms audit](../../scratch/rc-kato-p2-ident/axioms.txt) covers all four
theorems and the constructor and finds only `propext`, `Classical.choice`
and `Quot.sound`. The checked import closure contains no frozen main module.

## Remaining hypotheses and where to work

Exact Lean signatures, source pointers, and estimates are in the
[sizing log](../../scratch/rc-kato-p2-ident/log.md). These items are
existing obligations; they make no claim about the final scalar or
kernel length unless already stated as a consumer premise.

| Obligation | Tex | Owner and next step |
| --- | --- | --- |
| Actual `RetainedZeta`, `TwistTransfer`, `KodaiFullOpen`, `KodaiJStar`, `KodaiTower`, `IsClass07`, finite generation of full H², and Frobenius polynomial identification | 6904–7034, 7223–7225, 7243–7244 | Project étale and Iwasawa comparison. Build the finite coefficient groups with the fixed lattice, deck action and trace, then prove the limit identifications. The current polynomial purity proof alone does not identify it with Frobenius acting on the same twist. |
| `KatoOddSupportCone` | 6953–6987, 7257–7278 | Project étale and local cohomology. Show that the cone of restriction from the integral `j_*` system to the full open is represented after localization by the odd Frobenius complexes, that their degree-one cohomology vanishes, and that their H² is the odd part of actual localization. The existing `KatoOddSupportCone.toComparison` then supplies the kernel isomorphism. In particular a support change of two presentations of the *same* Selmer condition is insufficient to prove the result for the two different local conditions here. |
| `KatoH1Comparison` | 6953–6987, 7025–7034, 7243–7269, 7316–7317 | Project comparison. Identify the finite projections of the same class under restriction. The support cone concentrated in degrees one and two with H¹ zero after localization yields the localized H¹ isomorphism; prove finite presentation and clear the denominator on the localized dual. The existing Mackey and index transport lemmas already handle their respective algebraic steps. |
| `RetainedReciprocity` | 6904–6946, 7118–7205, 7215–7217 | Project construction of the regulator and period maps; the reading desk for the primary normalization. Kato 2004, Thm. 9.7 (p. 189, UNVERIFIED here) sends the actual étale class under the local dual exponential to the corresponding de Rham modular element. Thm. 6.6(1) (p. 163, UNVERIFIED here) evaluates the signed full character sum of that modular element, with the character dependent smoothing factors and symbol. They are the two candidate literature inputs. There is no genuine statement of either on the current abstract modules; supplying these as statements about `es` would be new GLUE. No such replacement is proposed. |
| `GenericNonzero` | 7025–7034, 7210–7221 | Project specialization. Start with the actual class of §0.7 and identify its character specialization with the original class tested by reciprocity at `χρ`. The existing `KatoThm13_5_2` gives the finite exceptional set. Prove that a sign annihilator can vanish at only finitely many cyclotomic points in the matching sign; both signs are needed. Finite nonvanishing without a scalar compatible specialization does not suffice. |
| `RetainedFiniteComparison` / `FixedKatoFiniteComparison` | 6953–6987, 7118–7142 | Project fixed finite comparison, admitted in the requested cut. Compare with the actual finite cochain reductions, trace and deck action, and prove detection up to a power of two. |
| `AppEFromKatoP2` | 7280–7315, 7353–7365, 7367–7787 | Project Appendix E. Use (K15) at all constituents to construct the uniformly corrected positive complex and its centrally calibrated output. This premise is separate from the cohomology identifications in the consumer signature. |

The first priority is the degree-one finite-coefficient comparison. The
manuscript cites the higher direct image stalk formula and Leray (Stacks
Tags 03Q9 and 03QA, not reread here) to identify the appropriate subgroup
of (H^1(K,T/2^i)). The [earlier audit](../theorem-application-audit/evidence/parallel-forward-modularity-a080-report.md)
records the argument and the separate inverse-limit input. The tree
already proves the Galois Mackey vanishing in
`RC/SelmerComplex/MackeyGeneral.lean`. The next step is to identify that
subgroup with the étale (j_*) group, with its reduction and transfer maps.
Degree two then needs the actual odd inertia cone and its comparison with
local cohomology. The finite Galois support comparison does not construct
either étale system or pass to the localized Iwasawa coefficients.

The scalar compatibility in the nonvanishing row is essential. The
projection fields in `KodaiTower` are additive, so they cannot detect a
change of the `Λ`-action on H¹ by themselves. For example, keeping only
the `ℤ₂`-action and then pulling it back along the trivial character
`Λ → ℤ₂` leaves the additive projections unchanged but makes
the power series variable annihilate H¹. The variable is regular in
`Λ`, so under this action the class is zero after localization at
every minimal prime. This illustrates why finite nonvanishing plus
the additive projection equations cannot prove `GenericNonzero`.

## Known issues

The existing reciprocity interface uses a fixed `s` and a free nonzero
function `b χ`. For nonquadratic auxiliary characters the printed
smoothing scalar is character dependent. A genuine supplier must account
for this in `b χ` (or use a formula with the smoothing factors explicit);
the central scalar of (K6) applies as stated to the central quadratic
character. Earlier audits of Kato 6.6 present the analytic character and
its inverse with different conventions. Keep the deck and Dirichlet
conventions explicit before identifying this formula for `χρ`. This
distinction disappears for (K13)'s quadratic character. No new primary
source reading was made here.

The old 1999 transcription had three errors: dyadic-only localization,
omitted purity, and global torsion asserted as printed. These were fixed
in the base. The corrected Lean statement is still a draft for abstract
modules. It is not a registered published leaf.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict |
| --- | --- |
| 1884–1893, 7206–7214, 7226–7241, application at two | **error** — the existing dyadic 2004 application gap; the corrected 1999 route is conditional on the proper objects. |
| 6904–6929, (K4) and the symbol | **unverified** — the original étale regulator classes and lattice are not constructed here. |
| 6931–6951, (K5)–(K6) | **OK** — retain the existing smoother choice; the central character is trivial there and the full odd support is kept. |
| 6953–6987, (K7) | **unverified** — tree proves Mackey on Galois cohomology, not the integral étale comparison with it. |
| 6990–7023, (K8)–(K9) | **unverified** — the base supplies norm transport on the abstract system; the actual transfer and arithmetic Frobenius comparison remain. |
| 7025–7034, cofinal dyadic levels | **unverified** — projected equality is proved once the actual restriction and finite projections are identified. |
| 7036–7106, (K10) and (E.1) | **unverified** — finite algebraic wiring is available, but it does not supply derived specialization of the same class. |
| 7108–7142, (K12)–(K13) | **unverified** — no local dual exponential, Betti period map and finite comparison on the retained classes. |
| 7143–7205, (K14) and central comparison | **unverified** — genuine period and local-lattice comparison still needed. |
| 7215–7221, generic nonvanishing | **unverified** — the available finiteness theorem needs the character specialization and reciprocity comparison. |
| 7222, real eigenspaces | **OK** — both dimensions are one for the actual rational twist; the negative dimension is the corrected input. |
| 7223–7225, purity | **unverified** — the chosen polynomial has the correct weight by the base proof; its identification on the lattice is still separate. |
| 7243–7255, H¹ and the index | **unverified** — no localized comparison on the actual H¹ and no finite presentation proof for these towers. |
| 7257–7278, (K16) | **unverified** — the transport in Lean assumes the geometric exact fragment on the odd places. |
| 7280–7359, local corrections and (K2) | **unverified** — local control and the same-class determinants are outside the proved transport. |
| 7367–7787, positive complex and central calibration | **unverified** — existing Appendix E assembly remains a premise. |
