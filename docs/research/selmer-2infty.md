# selmer-2infty: the 2-primary Selmer group of E/ℚ and its ℤ₂-corank (fork issue #83, first item)

**Result (compiled).** `ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean` defines, over Tau Ceti's Galois
cohomology of elliptic curves (vendored, commit 5a01f5fe), for `E : WeierstrassCurve ℚ`:

* `TwoPowerCoeff E` = `E(ℚˢ)[2^∞]` (the 2-primary component of `E(ℚˢ)`), a discrete `G_ℚ`-module, with the
  inclusion `twoPowerCoeffIncl E : E[2^∞] → E(ℚˢ)`;
* `sha E` = `Sha(E/ℚ)`: classes of `H¹(G_ℚ, E(ℚˢ))` restricting to zero at every place (Tau Ceti's
  `shafarevichTateGroup` for the completions `ℚ_p`, meet the one for `ℝ`);
* `selmerTwoPower E` = `Sel_{2^∞}(E/ℚ)`: classes of `H¹(G_ℚ, E[2^∞])` whose image in `H¹(G_ℚ, E(ℚˢ))` lies
  in `Sha(E/ℚ)` (Silverman X.4 with `E[m]` replaced by `E[2^∞]`); `mem_selmerTwoPower_iff` unfolds it to
  local triviality at every `ℚ_p` and at `ℝ`;
* `selmerAt E n` = `Sel_{2^n}(E/ℚ)` (Tau Ceti's `selmerGroup` at all places) and
  `selmerAtToTwoPower E n : Sel_{2^n} → Sel_{2^∞}`, induced by `E[2^n] ⊆ E[2^∞]` (proved well defined);
* `Z2Corank M r`: `M ≅ (ℚ₂/ℤ₂)^r × F` with `F` finite (the structure theorem for cofinitely generated
  `ℤ₂`-modules; `ℚ₂/ℤ₂` is `ℚ_[2] ⧸ ℤ_[2]`), and `SelmerCorankOne E := Z2Corank (selmerTwoPower E) 1`;
* `RestrictedConverseGenuine := ZInQ.Manuscript.RestrictedConverse SelmerCorankOne`: Theorem 5.3
  (`hyp:RC`, manuscript lines 1005–1011) over the genuine Selmer condition (`restrictedConverseGenuine_iff`
  spells it out).

Nothing in the main theorem uses these; nothing is assumed. Theorem 5.3 is not proved.

**Vendoring.** 152 Tau Ceti modules at commit 5a01f5fe (list: `scratch/selmer-2infty/vendor-new.txt`), the
closure of `GaloisCohomology.{Selmer, EtaleTwoDescent, Finiteness}` not vendored before, unmodified except
the provenance line and the import prefix; `MordellWeil/XSubT.lean` imports the Backport/ copy of
`Algebra.Group.MapMulMulEqOne` (task t40-tate) instead of the commit-5a01f5fe module, which is not vendored
(the two declare the same names). `ThirdParty/TauCeti/NOTICE` updated.

**Checks.** `lake build ZInQKernel.Contrib.AllContrib` with the 153 new modules appended: builds (every
Contrib module coexists in one environment). The first attempt failed only on the duplicate
`MonoidHom.ofMapMulMulEqOne` (resolved as above).

**Descent and Lemma 5.4 (compiled, standard axioms).**

* One family of completions at all places (`Place := Nat.Primes ⊕ Unit`, `Completion` = `ℚ_p` / `ℝ`), so
  Tau Ceti's `m`-descent sequence applies to `Sel_{2ⁿ}(E/ℚ)` directly.
* `twoPowerShortExact`: `0 → E[2ⁿ] → E[2^∞] → E[2^∞] → 0`; `range_selmerAtToTwoPower`: the image of
  `Sel_{2ⁿ} → Sel_{2^∞}` is `Sel_{2^∞}[2ⁿ]`.
* `ZInQKernel/Contrib/OneProof/CofinitePrimary.lean` (Mathlib only): the structure theorem — a `p`-primary
  abelian group with finite `p`-torsion is `≅ (ℚ_p/ℤ_p)^t × F`, `F` finite (`exists_addEquiv_of_isPPrimary`);
  `#(ℚ_p/ℤ_p)[pⁿ] = pⁿ`; `#(A/mA) = m^r · #T[m]` for `A ≅ ℤ^r × T`; a growth-rate comparison lemma.
* `ZInQKernel/Contrib/OneProof/SelmerCorank.lean`: **Lemma 5.4** (`lem:corank`, lines 1072–1084),
  `selmerCorankOne_of_card_selmerAt_one : MordellWeilQ E → CasselsTateSquare E → FullTwoTorsion E →
  Nat.card (selmerAt E 1) = 8 → SelmerCorankOne E`. Inputs: Mordell–Weil (`E(ℚ)` finitely generated) and
  the Cassels–Tate square property (the finite part of `Sha(E/ℚ)[2^∞]` has `#F[2]` a square; Cassels 1962,
  Poonen–Stoll 1999 §§4–5), both printed. Proved: `Sel_{2^∞}` is `2`-primary; `#ker(Sel_{2ⁿ} → Sel_{2^∞})
  ≤ #E(ℚ)[2^∞]` (through `δ⁰`); `Sel_{2ⁿ}` finite; `#Sel_{2ⁿ} = #(E(ℚ)/2ⁿ) · #Sha[2ⁿ]`; the corank by
  comparing growth in `n`, with `r + t' = 1` from `#Sel₂ = 8`.

**The curves `E_ℓ`, and the manuscript's lines 1107–1110 (compiled, standard axioms).**
`ZInQKernel/Contrib/OneProof/SelmerKummer.lean`: `isElliptic_curve` and `fullTwoTorsion_curve` (for
`ℓ ≠ 0`, `E_ℓ` is elliptic and `#E_ℓ(ℚ)[2] = 4`: the points `O, (0,0), (ℓ,0), (-3ℓ,0)`);
`kummerSelmerMap_surjective_of_rank_one` (full two-torsion, `#Sel₂ = 8`, `rank E(ℚ) = 1`: the Kummer map
`E(ℚ)/2E(ℚ) → Sel₂` is onto, both having 8 elements); `KolyvaginRankOne` (the rank half of Lemma 5.5, a
printed input); `kummerSelmerMap_surjective_of_restrictedConverse`: for positive squarefree `ℓ ≡ 11 (mod 12)`
with `#Sel₂(E_ℓ/ℚ) = 8`, Theorem 5.3 over the genuine Selmer condition, Lemma 5.4 and the printed inputs
(Mordell–Weil, Cassels–Tate, Kolyvagin) make every class of `Sel₂(E_ℓ/ℚ)` a Kummer class of a rational
point — the step "the Kummer class is then represented by actual rational points".

**Mordell–Weil proved.** Tau Ceti 5a01f5fe proves the Mordell–Weil theorem for elliptic curves over
number fields (`WeierstrassCurve.Affine.fg_point_of_numberField`, `MordellWeil/FinitelyGenerated.lean`,
after M. Stoll's `EllipticCurves`); its 7 missing modules are vendored (`scratch/selmer-2infty/vendor-mw.txt`).
`mordellWeilQ` discharges `MordellWeilQ E` for every elliptic `E/ℚ`; `selmerCorankOne_of_card_selmerAt_one'`
(Lemma 5.4) and `kummerSelmerMap_surjective_of_restrictedConverse'` drop it as a hypothesis. Lemma 5.4's
remaining printed input is the Cassels–Tate square property.

**Cohomological = explicit `Sel₂`, and the manuscript's `SelM` (compiled).** Tau Ceti main (commit
0642eae2) proves that the cohomological descent map identifies the cohomological `2`-Selmer group with the
explicit one of the étale algebra (`WeierstrassCurve.selmerGroupTwoMulEquivSelmerGroup₂`); it is backported
under `ZInQKernel/Contrib/TauCeti/Backport/Main0642/` (`scratch/selmer-2infty/backport/`). The places of `ℚ`
are now `HeightOneSpectrum ℤ ⊕ Unit` with the `v`-adic completions (Mathlib's
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv` identifies them with `ℚ_p`), so that comparison applies
verbatim:

* `ZInQKernel/Contrib/OneProof/SelmerExplicit.lean`: `selmerGroup_emb_eq_inf` (`Sel₂` is the meet of the
  conditions at the finite places and at `ℝ`), `selmerTwoMulEquivSelmerGroup₂` and `card_selmerAt_one_eq`
  (`#Sel₂(E/ℚ) = #selmerGroup₂ ℤ ℝ` for every elliptic `E/ℚ` in the form `y² = f(x)`).
* `ZInQKernel/Contrib/OneProof/SelmerSplit.lean`: for `E_ℓ` over a field of characteristic zero, the étale
  algebra is `K³` (evaluation at the roots `−3ℓ, ℓ, 0`; `coord_injective`, `coord_surjective`), the norm is
  the product of the coordinates, restriction is coordinatewise, the `x − T` map is `x ↦ (x + 3ℓ, x − ℓ, x)`
  with the corrected values at the roots, and the class with coordinates `(a, b, ab)` is a local image
  exactly when the manuscript's x-form condition `LocM K ℓ a b` holds (`exists_coord_μ_iff_locM`). Over
  `ℚ`, square classes are squarefree integers and the condition at `v = (p)` is the one over `ℚ_p`; this
  gives `selMEquiv : SelM ℓ ≃ selmerGroup₂ ℤ ℝ` and `ncard_selM`, where `SelM` and `LocM` have the same
  definitions as the descent lane's `ZInQ.Manuscript.PoleRC.SelM` and `PoleRC.LocM`.
* Consequences (`SelmerExplicit.lean`): `card_selmerAt_curve_eq_ncard_selM` (`#Sel₂(E_ℓ/ℚ) = #SelM ℓ`);
  `lemma54At_selmerCorankOne` (the descent lane's `Lemma54At SelmerCorankOne` with the genuine predicate,
  from the Cassels–Tate square property); `locM_of_restrictedConverse` (Theorem 5.3 over the genuine
  Selmer condition, Lemma 5.4, Mordell–Weil (proved) and the printed Cassels–Tate and Kolyvagin inputs give
  `LocM ℚ ℓ a b` for every `(a, b) ∈ SelM ℓ` when `#SelM ℓ = 8`: the descent lane's `CR_M`, for every
  class).

**The place family (compiled, standard axioms).** `ZInQKernel/Contrib/OneProof/SelmerPlaces.lean` proves
that the change of the finite places from the primes `p` with `ℚ_p` (main at 4a063a7f: two families,
`ℚ_p` and `ℝ`; and the single family over `Nat.Primes ⊕ Unit`) to the height-one primes `v` of `ℤ` with
the `v`-adic completions changes nothing: `sha_eq_shaQp`, `selmerAt_eq_selmerAtQp`,
`selmerTwoPower_eq_comap_shaQp`, `sha_eq_shaP`, `selmerAt_eq_selmerAtP` (same subgroups of the same
`H¹`). The proof reindexes the places along `Rat.HeightOneSpectrum.primesEquiv` and transports the
local condition along the ring isomorphism of `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`
(`pointRes_eq_zero_iff_of_algEquiv`, from Tau Ceti's `pointRes_pointRes_eq_zero_iff`; the two maps from
`ℚ` agree by `eq_ratCast`/`map_ratCast`). The earlier families are kept there as comparison data only.

**Remaining inputs of this lane.** Theorem 5.3 itself (`RestrictedConverseGenuine`), the Cassels–Tate square
property (`CasselsTateSquare`) and the rank half of Lemma 5.5 (`KolyvaginRankOne`) are hypotheses; nothing
here proves them.
