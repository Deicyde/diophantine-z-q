# tyz-chain: the TYZ side in one importable module

**Result.** The TYZ side is now one Lean module, `ZInQKernel/Contrib/TYZChain/Main.lean`. Its theorem is

    ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves
      (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
      (h33 : ∀ ℓ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ) :
      ZInQ.Literature.TYZThm35ReadingA

So reading A of TYZ Theorem 3.5 rests on **four leaves and no glue**:

| hypothesis | kind | source |
|---|---|---|
| `TYZThm11Integral` | LEAF | TYZ Theorem 1.1 (`𝓛(m) ∈ ℤ`) |
| `TYZLemma29Mod2` | LEAF | TYZ Lemma 2.9 with Proposition 2.3, mod 2 |
| `ShimuraReciprocityModFn` | LEAF (textbook) | main theorem of CM on `X₀(N)` (Shimura 1971, Gross 1984) |
| `TYZThm33Pinned` | LEAF | TYZ Theorem 3.3 with Lemma 3.14, for the pinned CM points |

Proved inside the chain (no longer hypotheses):

| statement | proved by |
|---|---|
| `TYZLcalOne` | tyz-lcal |
| `Lemma321Five` | tyz-321 |
| `Thm35First`, from `h33` | tyz-35 |
| `Lemma318Literal HHprime` (TYZ Lemma 3.18), with no hypotheses | tyz-318, plus sqrt2-glue's `SqrtTwoNotInHHprime` |

sqrt2-glue reported at 01:20 and is merged; the theorem for Lemma 3.18 is `package_lemma318Literal_HHprime`.

`TYZChain/Headline.lean` adds two declarations:
* `TYZChainLeaves`, a structure whose fields are the four leaves;
* `frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves : SixContactMin → GrossZagier →
  TYZChainLeaves → FrozenTarget`, which fills in the proved providers for `HeckeContinuation` and
  `FunctionalEquation5`.

**What compiles (VERIFIED).** Ten new modules under `ZInQKernel/Contrib/TYZChain/`: Bridge, L321,
Thm35, Lemma318, Sqrt2Glue, Lcal, ModFn, SSExponent, Main and Headline. `lake build` succeeds for each
one, with no `sorry`. The audit `scratch/tyz-chain/Check.lean` runs 89 `#print axioms`; every one gives
`[propext, Classical.choice, Quot.sound]`. Output is in `scratch/tyz-chain/Check.out`, which also has
the `#check` of the main theorem.

**Copies removed.**
* The three copies of cm-bridge's file are gone: L321 and Thm35 import Bridge.
* Copies of declarations that already existed elsewhere are replaced by imports:
  * Chebotarev/FrobeniusDenseOfExists (in L321);
  * tyz-cm's ShimuraRecip and ShimuraZn (in Bridge);
  * ShimuraModFn (in ModFn);
  * tyz-318's §S (in SSExponent);
  * tyz-318's §0 (in Sqrt2Glue).
* The modules total 11.4k lines, against 18.3k in the source files.
* One side effect: `Main` now imports all of Mathlib, through FrobeniusDenseOfExists.

**What remains.**
* Formalize or accept the four leaves. Leaf `TYZThm33Pinned` still needs a HUMAN CHECK of how it
  passes from the printed theorem to the pinned form. `Period7.tex` is not on this host, so no TYZ line
  number was re-read in this task.
* I did not review the sqrt2-glue and tyz-321 proofs independently. Both compile, and both prove the
  verbatim Props.
* Integration: add `import ZInQKernel.Contrib.TYZChain.Headline` (plus `ModFn` and `SSExponent`) to
  `AllContrib.lean`. I did not edit it, because the task forbids editing existing files.

Report: `docs/research/tyz-chain.md`. The hypothesis list comes first there, and an appendix gives
the Lean text of each hypothesis.
