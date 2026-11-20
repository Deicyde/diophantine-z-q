# Dyadic Kato identifications: sizing and verification

Base: `52476d1ac627af42e77f272931445416f4baaaa5`. Paths are relative to the
repository root. VERIFIED means read in the tree or checked by Lean;
SPECULATIVE marks estimates. Source locators below refer to manuscript
citations or prior audits; no new primary source was read.

| Input and exact cut | What the tree has (VERIFIED) | Missing / size (SPECULATIVE) |
| --- | --- | --- |
| `KatoOddSupportCone full retained` (`KatoP2/Kodai08Support.lean`): `2 ∈ NK.primeFactors`, an equivalence between the full local summand at two and the retained local target, a restriction `res : H²_j →ₗ[Λ] H²_S` commuting with restriction at two, and, for `p.height = 1` and `2 ∉ p`, injectivity of `localMap p res` and exactness of `localMap p res` followed by the localized odd projection of `full.iw.loc`. | `KatoOddSupportCone.toComparison` derives the localized kernel isomorphism. `RC/SelmerComplex/{Cochains,Galois,UnramifiedCondition,UnramifiedFactorization,SupportChange}.lean` has continuous cochains, unramified local conditions and a support change comparison on Galois complexes. `RC/KatoP2/Abelian.lean` has the actual rational twist. Mathlib has étale sites and a constant sheaf pro-étale ℓ-adic cohomology definition. | Build the integral `RΓ(X,j_* T/2^i)` and full-open systems, then compare with those Galois complexes, traces and deck maps on both limits. Identify the odd cone with the degree-(1,2) Frobenius complex of `H¹(I_q,Vχ)` and its H² with the local restriction at each odd prime; show injectivity at each tested localization and compatibility at two. Foundational project plus several hundred lines on top of it. Tex 6953–6987, 7257–7278. |
| `KatoH1Comparison es NK full small t` (`KatoP2/Comparison.lean`): `res : H¹_j →ₗ[Λ] H¹_S`, `retainedProj n : H¹_j →+ es.H (2^n)`, `t.proj n (res x) = retainedProj n x` and `retainedProj n small.zIw = es.z (2^n)` for `1 ≤ n`, and, for every tested `p` and `h : H¹_j →ₗ[Λ] Λ`, `∃ a : p.primeCompl, ∃ g : H¹_S →ₗ[Λ] Λ, g.comp res = (a : Λ) • h`. | `retained_norm_to_dyadic`, `kodai07_eq_retained`, `map_J_le_of_extend` already prove descent and index transport from these data. Mathlib has localization of linear maps and Hom from finitely presented modules. | Compare the integral projections and corestriction, prove localized H¹ restriction is an isomorphism via (K16) and finite presentation (or a suitable annihilator). Several hundred lines after the cohomology systems; the denominator argument alone is small. Tex 6953–6987, 7025–7034, 7243–7269. |
| `RetainedReciprocity E Sig Sbad es` (`KatoP2/FiniteAnchor.lean`): `per m : es.H m →+ ℂ`, `s ≠ 0`, `b χ ≠ 0`, entire `Lcont χ` agreeing on `3/2 < Re(s)` with the partial twisted L-series omitting `Sbad ∪ prime(m)`, and for `KatoXi 2 Sig m`, `∑ g, χ(g) * per m ([g] • es.z m) = s * b χ * Lcont χ 1`. | `PrintsArith.KatoZetaInterface.recip` already has this formula as a field, tied to the old (2004) divisibility bundle. `RetainedReciprocity.z_ne_zero_of_L_ne_zero` and `anchored_weightedSum_nsmul_ne_zero_p2` use it for the finite anchor. Kato 2004, 9.7 and 6.6 are cited at pp. 189 and 163 (locators UNVERIFIED in this task); no separate genuine print for either was found on this cut. `KatoProp812Print` is the abstract norm input only. | The original modular zeta classes/regulators, dual exponential, de Rham to Betti comparison, same symbol at all levels and the retained smoothing factors. The base's `PrintsArith/Kato.lean` estimates tens of thousands of lines for the zeta construction and a separate substantial period-ring project. The expected two source results cannot be stated on the supplied abstract `es` and counted as genuine leaves. Tex 6904–6946, 7118–7205. |
| `RetainedFiniteComparison es fam μ nested` (`KatoP2/FiniteAnchor.lean`): there are additive maps `J m i : es.H m →+ subgroupH1 (cyclotomicKernel (μ m)) (Lev ℚ (familyPlaces fam) E i)` that commute with reduction, corestriction for every nested pair and right transversal, and deck action, and detect a class up to a power of two (`(∀ i, J m i z = 0) → ∃ c, (2^c : ℕ) • z = 0`). Fixed specialization: `Checked.FixedKatoFiniteComparison`. | Already available as the one admitted fixed comparison; `FixedComparisonChecked.lean` and `AppEK1/Comparison.lean` wire the comparison into finite detection. | Identify the finite étale `j_*` lattice classes and their maps to the genuine Galois groups at the specified `familyPlaces`; enough for finite detection only. Substantial; retained by instruction. Tex 6953–6987, 7118–7142. |
| `GenericNonzero full` (`KatoP2/KodaiPrint.lean`): `∀ (q : Ideal KatoLambda2) [q.IsPrime], q.height = 0 → LocalizedModule.mk full.zIw (1 : q.primeCompl) ≠ 0`. | `KodaiTower.IsClass07` and `kodai07_eq_retained` specify the projections and identify the class once the comparison is supplied. `PrintsArith.KatoThm13_5_2` states Rohrlich finiteness of the distinct zero partial central values on a fixed prime support (Kato 2004, p. 227, manuscript locator, UNVERIFIED here). The two sign quotient maps of `KatoLambda2` are in `KodaiLambdaTorsion.lean` (used there for torsion); `RC/Central/CentralSpecialization.lean` treats central specialization of a cohomology class on a different cut. | Need the equivariant finite-character specialization (including scalar action), same-system reciprocity for `χρ`, and zero finiteness for each nonzero integral sign power series evaluated at the cyclotomic points. Nonzero finite classes by themselves are insufficient. Several hundred lines after arithmetic comparisons; no replacement input that asserts these specializations are nonzero is licensed. Tex 7025–7034, 7210–7221. |
| `Checked.KodaiConstituent.realSign`: `Module.finrank ℚ_[2] (LinearMap.ker (rationalTwist E charGalois OpenImage.complexConj + 1)) = 1`. | `Stages.complexConj_sq`, `Stages.det_complexConj`, `tateBasis E`, `rationalTwist`. | Small: determinant is still `-1` after base change and scalar twist; split an involution over `ℚ₂` to get the two lines. No leaf needed. Tex 7222. |
| Objects around the cut: `RetainedZeta`, `TwistTransfer`, `KodaiJStar`, `KodaiFullOpen`, `KodaiTower`, `IsClass07`, `Module.Finite KatoLambda2 full.iw.H2`, and the Frobenius polynomial identification. | `ExtendedNorm`, `Comparison` and `Kodai08Purity` prove the transition, descent and weight computations. The structures still give abstract modules; `Checked.KatoKodai99Thm08Print` does not build these data. | Actual arithmetic objects, maps and finite generation. In particular the `P` argument of the draft is not definitionally a Frobenius polynomial of `ρ`. This is distinct from proving weight −1 for the chosen polynomial. Tex 6904–7034, 7223–7225, 7243–7244. |
| `Checked.AppEFromKatoP2 E N L e Nodd K`: uniform constants and nonnegative bounds, then for each family, `RetainedK15` on every constituent implies `Nonempty (EvenFamilyOutput … fam)`. | `appEOutputs_of_katoP2`, `evenScalar32_of_katoP2` and fixed/curve adapters already use this conditional assembly. It is independent of `RetainedReciprocity` and `FixedKatoFiniteComparison` in their actual signatures; those are used in the separate finite anchor. | Even supplying the four named identifications leaves this separate existing assembly obligation: local factors, positive complex and central calibration. Tex 7280–7315, 7519–7787. |

Throughout `d = |h|`, `D = d * 2^a` and `NK = 2 * N * d` include the full
odd filter, including odd conductor primes that divide the fixed level.

**Stop criterion met for the full cut.** The existing support-change print
has finite coefficient hypotheses and compares Galois Selmer complexes;
it does not furnish the geometric `j_*` comparison at localized Iwasawa
coefficients. Even granting both reciprocity citations would still require
new arithmetic comparison GLUE beyond `FixedKatoFiniteComparison`. The
real sign can be proved within the cut. No new arithmetic assumptions are
introduced for it.

- **VERIFIED** (base): `SelmerComplex.res_cor_eq_zero_of_forall_conj'`
  in `ZInQKernel/Contrib/OneProof/RC/SelmerComplex/MackeyGeneral.lean`
  already handles inertia vanishing under finite transfer on Galois
  cohomology. The finite étale identification remains separate; the
  prior audit in `docs/theorem-application-audit/evidence/parallel-forward-modularity-a080-report.md`
  gives the Leray argument and the degree-one inverse-limit justification.
- **VERIFIED** (base): `KodaiTower.proj` and `corestrict` are additive
  maps. Their types do not identify the action of `Λ` on the limit with
  finite deck actions. This scalar compatibility is necessary before
  finite nonvanishing can test a minimal-prime localization.
- **VERIFIED** (Lean 4.35.0): `RealSign.lean` and
  `RealSignBridge.lean` both elaborate with `lake env lean` and
  emit their object files. The sign proof uses the existing
  Weil pairing consequence from `DetTateCyclotomic.Basic` and the
  genuine conjugation from `OpenImage.Basic`. The constructor fills the
  real sign field of the existing checked constituent.
- **VERIFIED** (build): used one Lean invocation at a time with
  `LEAN_NUM_THREADS=4` and checked load and available memory.
  The broader build for the initial conjugation import was stopped
  after the proof was narrowed to existing Weil pairing and open-image
  imports. Reused the compiled reroute artifacts from the same base
  with matching manifest and toolchain; no missing import was left
  unchecked.
- **VERIFIED** (axioms): `lake env lean scratch/rc-kato-p2-ident/Check.lean`
  passes. All four new theorems and the constructor use only
  `propext`, `Classical.choice` and `Quot.sound`. The bridge does not
  import the frozen main module. See [axioms.txt](axioms.txt).
