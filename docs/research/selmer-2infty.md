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

**Next (not done).**
1. `Sel_{2^n} → Sel_{2^∞}[2^n]` is onto with kernel `E(ℚ)[2^∞]/2^n` (needs the long exact sequence of
   `0 → E[2^n] → E[2^∞] → E[2^∞] → 0`, multiplication by `2^n` being onto on `E(ℚˢ)[2^∞]`).
2. Lemma 5.4 (`lem:corank`) for curves with full rational 2-torsion: `dim Sel₂ = 3 ⇒ corank 1`, from
   Mordell–Weil and Cassels–Tate (Poonen–Stoll) as stated printed inputs.
3. The explicit system `ZInQ.Manuscript.PoleRC.SelM` of `wip/pc-from-rc` against Tau Ceti's cohomological
   `Sel₂` (Silverman X.1.4; Tau Ceti's `EtaleTwoDescent`), which turns that lane's interface `Lemma54At P` into
   Lemma 5.4 at `P = SelmerCorankOne`.
