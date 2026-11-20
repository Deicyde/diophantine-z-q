# Base consumer inventory

VERIFIED with:

```sh
git grep -n -E 'Thm13_4Conclusion|KatoZetaLeaf|iw_thm13_4|AppEFromKato|evenScalar32_of_kato|KatoXi'
git grep -n -E 'appEOutputs_of_kato_fixed|evenScalar32_of_kato_(fixed|ecurve)|evenLowerBound_of_kato_ecurve|KatoZetaInterface(812)?' -- '*.lean'
```

Lean paths below are relative to `ZInQKernel/Contrib/OneProof/RC/`.

| Location | Exact cut / use |
| --- | --- |
| `PrintsArith/Kato.lean:139,178` | `KatoXi p Sig m` is `1 ≤ m ∧ p ∣ m ∧ (∀ q, q.Prime → q ∣ m → q ∈ Sig → q = p)`. `EulerSystemData.IsEulerSystem` requires it at both ends of `m ∣ m'` and gives the product on `prime(m') ∖ prime(m)`. |
| `PrintsArith/Kato.lean:236,295` | `IwasawaData.Thm13_4Conclusion D p` is torsion of `D.H2` and the height-one-away-`p` inequality for `LocalizedModule 𝔭.primeCompl D.H2zero` and `Λ𝔭 / J𝔭`. `KatoZetaInterface.iw_thm13_4 : iw.Thm13_4Conclusion 2`. |
| `PrintsArith/Kato.lean:283–325` | The rest of `KatoZetaInterface E Sig Sbad`: classes, old norm, cyclotomic limit and projections, periods, nonzero smoothing and period scalars, analytic continuation, and `recip` on `KatoXi`. `z_ne_zero_of_L_ne_zero` uses only the anchor: at `m ∈ Ξ` and `Lcont χ 1 ≠ 0`, `es.z m ≠ 0`. |
| `PrintsArith/Kato.lean:339` | `KatoZetaLeaf`: for every elliptic non-CM curve `E/ℚ`, every `Sbad ∋ 2` outside which each prime avoids the five coefficient denominators and Δ numerator, supplies `∃ Sig, Sbad ⊆ Sig ∧ Nonempty (KatoZetaInterface E Sig Sbad)`. |
| `Kato812/Kato812Interface.lean:18–45,114–167` | Widened structure still requires `iw_thm13_4`; its `recip` takes `KatoXi 2 (oldSigma Sbad c ds) m`. `smooth_disjoint_of_katoXi` derives avoidance of smoother primes; `isEulerSystem` restricts the full norm to `KatoXi 2 Sig` for `oldSigma ⊆ Sig`. `toOld` copies the old bound and narrows the reciprocity domain; this is the only direct projection of the bound. |
| `Kato812/Kato812Interface.lean:174–214` | `norm_at_twisted_indices` needs `KatoXi 2 (twistedSigma E d c ds)` at both ends. Its output is the untwisted corestriction on levels `d*2^a*m ∣ d*2^a*m'`, with precisely the new primes of `m'`. It does not use the bound field. |
| `AppEK1/FiniteIdentity.lean:68,120–149,200–211` | `katoXi_support_iff` identifies `KatoXi` for `F*2^n` with disjointness of family support and `Sig` for `n ≠ 0`; `finiteNorm_of_isEulerSystem` restricts from the upper level to `d*2^n`; `dyadicNorm_of_isEulerSystem` takes old-domain proofs at `d*2^n,d*2^n'` and gives factor 1. `anchored_weightedSum_nsmul_ne_zero` takes the old interface, `m ∈ Ξ`, a signed character sum and `Lcont χ 1 ≠ 0`; concludes no positive natural scalar kills that sum. |
| `AppEK1/Comparison.lean:137–193` | `KatoFiniteComparison` and its fixed-curve specialization take the old interface for its finite modules and maps. The conclusion of `exists_nonzero_image_of_anchored_weightedSum` is a nonzero image of that same signed deck sum at some finite coefficient precision, assuming comparison, `m ∈ Ξ`, and `Lcont χ 1 ≠ 0`. |
| `Kato812/Kato812Finite.lean:39,61,93` | Indirect bundle users: `dyadicNorm_812`, `finiteNorm_of_kato812`, and `finite_e1_812` take the widened bundle. Only its finite norm data is used. Conclusions: factor 1 on a positive dyadic tail; `FiniteNorm` respectively finite weighted (E.1) on the admissible family. |
| `Even/KatoBridge.lean:39–54` | `AppEFromKato E N L`: the old leaf's support supply at a fixed elliptic `E` implies `AppEOutputs E N L`. `evenScalar32_of_kato`: old leaf, `HasNoCM E`, `N ≠ 0`, and that construction give `EvenScalar32 E N L`. |
| `AppE32Fixed/Fixed.lean:16–36` | `appEOutputs_of_kato_fixed`: old leaf, `CMjInteger`, `0 < ℓ`, normalization `C`, and the old construction at `Ecurve ℓ, N₀ ℓ` give `AppEOutputs` at those parameters. `evenScalar32_of_kato_fixed`: also `BCDTThmA` and `C.Lstar = W.Lstar`; gives `EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C ∧ Scalar32 W`. |
| `GlueSweep/EvenKato.lean:31–50` | `evenScalar32_of_kato_ecurve`: old leaf, `CMjInteger`, `0 < ℓ`, `N ≠ 0`, and the old construction imply `EvenScalar32 (Ecurve ℓ) N L`. `evenLowerBound_of_kato_ecurve`: additionally `Prints` and `HasseConvergence` imply `EvenLowerBound (Ecurve ℓ) L`. Neither result has another Lean caller beyond the displayed chain. |
| `Even/EvenSource.lean:498–501`, `PrintsArith/Bundle.lean:14` | Documentation mentions. `Prints` does not contain `KatoZetaLeaf`. |

The remaining grep hits are documentary: `.fleet/rc-appE-32-fixed.md`,
`docs/research/rc-appE-32-fixed.md`, `docs/research/rc-appE-k1.md`, and
the logs under `scratch/rc-appE-32-fixed/`, `scratch/rc-appE-k1/`,
and `scratch/rc-kato812/`. None consume a Lean field.

Consumers already taking the output type alone keep their signatures:
`Even.evenScalar32_of_appE`, the App E entry points in
`EvenUpperCubes/Application.lean`, and the App E entry points in
`GlueSweep/EvenLowerBound.lean` and `GlueSweep/EvenPhaseBridge.lean`.

## Follow-up to the conditional route at the base

The base's `KatoP2/KodaiPrint.lean` used global torsion of `full.H2`
and the abstract dyadic localization kernel in `Kodai08AwayTwo`.
`KatoP2/Comparison.lean` used that conclusion in
`retainedK15_of_kodai08`. It also contained an optional lemma taking a
length bound on the whole `full.H2`; no base adapter calls that lemma.

`KatoP2/EvenBridge.lean` has one direct caller of
`KatoKodai99Thm08Print` (`KodaiConstituent.retainedK15`), then one caller
of that result (`appEOutputs_of_katoP2`). Its other adapters specialize
that output, or call `evenScalar32_of_katoP2`. All are replaced by the
same names under `KatoP2.Checked` with the corrected input; all output
types are the same. The active exactness hypothesis is
`KatoOddSupportCone`, which supplies the corrected `onKernel`.

`KatoP2/FiniteAnchor.lean` and `AppEK1/Comparison.lean` ask for the
same reduction, trace, deck and finite detection conditions. The corrected
fixed-family cut uses `FixedKatoFiniteComparison` by passing the finite
system itself. `FiniteAppE`, the extended norms, the Serre inputs and
the tower-class descent are reused as they stand.
