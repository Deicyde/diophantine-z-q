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

**Next (not done).**
1. Connect `ZInQ.Manuscript.PoleRC.SelM` (explicit `2`-Selmer system, `wip/pc-from-rc`) with `selmerAt E 1`
   (Tau Ceti's `EtaleTwoDescent`, Silverman X.1.4): then that lane's `Lemma54At SelmerCorankOne` follows
   from this Lemma 5.4.
2. Discharge `MordellWeilQ` from Tau Ceti's `MordellWeil/FinitelyGenerated` (Tau Ceti main; needs a
   backport to this toolchain).
