# eichler-bound: `gonzalezRotgerProp56X6` removed with no new leaf

Task eichler-bound (2026-11-16). Base: wip/gr-dict 48db1227 with origin/main (0caafe66) and wip/gr56-prove
(90b817cb) merged. Marks: VERIFIED (compiled, computed, or read in the tree), STANDARD (published, exact
reference), SPECULATIVE, UNVERIFIED (theorem numbers from memory; no network on this host).

## 1. Result

**`GR56.R5fpCountLe` is proved from the three textbook fields alone. The bound the chain reads from
`gonzalezRotgerProp56X6` therefore needs no leaf, and Eichler's formula (`GRCountX6.EichlerOptEmbCount6`) is not
used.** VERIFIED: everything compiles with only the standard axioms `[propext, Classical.choice, Quot.sound]`.

```lean
-- ZInQKernel/Contrib/OneProof/R5fpCountLe.lean (imports GR56Lattice, never Main)
theorem EichlerBound.eichlerOptEmbBound6 (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2)
    (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (LeafQM.AV.conductor R) 6) (hh : Nat.card (CommRing.Pic R) ≠ 0) :
    Finite (Quot (GRCountX6.ConjRel R)) ∧
      Nat.card (Quot (GRCountX6.ConjRel R)) ≤ 2 ^ LeafQM.AV.inertCount6 k * Nat.card (CommRing.Pic R)

theorem EichlerBound.r5fpCountLe_proof (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : GR56.R5fpCountLe
```

* `eichlerOptEmbBound6` is the upper half of Eichler's count for the maximal order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩`
  of `B = (2, −3 | ℚ)`, for every order `R` of conductor prime to 6 in a quadratic field. It is a theorem, with no
  hypothesis beyond the statement's. It replaces the leaf `EichlerOptEmbCount6` (rated GLUE: a composite of the
  trace formula and the local embedding numbers).
* `r5fpCountLe_proof` combines it with gr56-prove's `GR56.card_cmSet_le` (`#CM(R) ≤ #(Emb(R,𝒪)/𝒪^×)`, from
  `uniformizationLeafAll`, `gagaMorphism` and `mumfordTorsionAlgClosed`, all already in `OpenTextbookLeaves12`).

**Count** (`autofold.py --dry-run` with the count-only spec of §5, VERIFIED).
* gr-dict's bypass replaced `gonzalezRotgerProp56X6` by the leaf `eichlerOptEmbCount6`, which is neutral in the
  count. This task's bypass (§4) replaces it by nothing.
* Against the tree's kinds.tsv (prop56 rated LEAF): `34/11 on 45 -> 33/11 on 44`, the same under the
  strictest column.
* Against the 11-16 re-rating of this row as GLUE (simulated on a copy in `/tmp/ebsim`; the tree's file is
  untouched): `33/12 on 45 -> 33/11 on 44`. **−1 GLUE, no new leaf.**

## 2. The mathematics (an explicit injection, no trace formula)

Notation: `Emb = OptEmb k R` (algebra maps `Φ : k → B` with `Φ⁻¹(𝒪) = R`), `~` = `ConjRel R` (conjugacy by
`𝒪^×`), `b = inertCount6 k`. The proof builds an injection `Emb/~ ↪ Pic(R) × T` with `#T = 2^b`.

1. **`R = ℤ + ℤω`** (`exists_basis`). The `a₁`-coordinates of `R` lie in `D⁻¹ℤ`, where `D = disc(a₁)`, so they
   form a cyclic group. `ω` is a generator, with `ω² = tω − n`.
2. **Types at `ℓ ∈ {2, 3}`.** `P₂ = i𝒪 = {x ∈ 𝒪 : 2 ∣ nrd x}` and `P₃ = j𝒪 = {3 ∣ nrd}` are two-sided primes,
   and `𝒪/P_ℓ` is commutative (`PP_comm`). Two embeddings have the same type at `ℓ` iff `Φ(ω) − Φ'(ω) ∈ P_ℓ`.
   * Dichotomy (`type_dichotomy`): `(β − β₀)(β − β̄₀) = [β, β₀] ∈ P_ℓ`, so `Φ(ω) ≡ Ψ(ω)` or `Φ(ω) ≡ Ψ(ω)‾`.
   * If `ℓ` is not inert in `k` (`ℓ𝒪_k` not prime), there is only one type (`same_type_of_not_inert`, through
     `inert_of_noint`). If `Ψ(ω)` is never congruent to an integer mod `P_ℓ`, then `ℓ𝒪_k` is prime. This uses
     the conductor (`f·𝒪_k ⊆ R`, `(f, ℓ) = 1`).
   * Hence the types form a set `T` of size `2^b`.
3. **Intertwiners.** For `Ψ, Φ ∈ Emb` set `J = {c ∈ B : cΨ(a) = Φ(a)c}`.
   * `J ≠ 0` (`exists_Jo`): `c = Φ(ω)s − sΨ(ω)‾` for some `s ∈ {1, i, j}`.
   * `J = c₀Ψ(k)` (`J_param`): the centralizer of `Ψ(ω)` is `Ψ(k)`, by a cross-product computation.
4. **Bad primes.** Call `ℓ` bad if `c̄d ∈ ℓ𝒪` for all `c, d ∈ J ∩ 𝒪`.
   * The conjugation trick (`bad'_of_bad`) gives `cd̄ ∈ ℓ𝒪` as well, by optimality of both embeddings and
     stability of `R` under conjugation.
   * **No prime is bad for two embeddings of the same type:**
     * **`ℓ ∤ 6`** (`not_bad_coprime`). Every `2×2` minor of the coordinates of `c, d` satisfies `6·minor ∈`
       the ℤ-span of the 8 coordinates of `c̄d` and `cd̄`. This polynomial certificate was found with sympy
       (`scratch/eichler-bound/cert2.py`) and is checked by `ring` (`minor_dvd`). A descent on the sum of the
       minors of two ℚ-independent elements `c, cΨ(ω)` of `J ∩ 𝒪` then gives a contradiction.
     * **`ℓ ∣ 6`, ramified** (`ram_contra`). `exists_l` gives an element of `R` with norm exactly divisible by
       `ℓ`. With `π̄π = ±ℓ`, it divides `J ∩ 𝒪` by `ℓ` arbitrarily often, which is impossible.
     * **`ℓ ∣ 6`, unramified** (`unram_dvd`). Conjugation by `π_ℓ ∈ {i, j}` is the quaternion conjugation
       mod `P_ℓ` (`frob`). Write `c = πc₁`. Then the same type forces `ℓ ∣ Δ`.
5. **Unit criterion** (`unitCrit_of`, `unitCrit'_of`). `𝒪J̄ = 𝒪α` by class number one, which is the
   norm-Euclidean algorithm copied from `TailU`. A prime dividing `nrd α` is bad, so with no bad prime
   `J𝒪 = 𝒪 = 𝒪J`.
6. **The class in `Pic R`.** Let `𝔞 = {a : c₀Ψ(a) ∈ 𝒪}` and `𝔟 = {b : Ψ(b)c₀⁻¹ ∈ 𝒪}`.
   * Then `𝔞𝔟 = R` (`latA_isUnit`). `𝔞𝔟 ⊆ R` by optimality. For `1 ∈ 𝔞𝔟`, the unit criteria give
     `Ψ(𝔞𝔟)𝒪 = 𝒪`, and Lemma D (`lemmaD`) gives a prime `ℓ` with `𝔫𝔫 ⊆ ℓR` whenever `1 ∉ 𝔫`. At `ℓ = 2`,
     Lemma D is a coordinate check (`two_mul_cond`, by `decide` over `ZMod 2`).
   * The class is `Submodule.unitsToPic R k 𝔞 ∈ CommRing.Pic R`. This is Mathlib's map, and its kernel
     `ker_unitsToPic` consists of the principal submodules.
7. **Injectivity** (`conj_of_pcp`, `conj_of_lat`). Equal classes give `𝔞' = x𝔞`. Then
   `u = c'Ψ(x)c⁻¹ ∈ J(Φ, Φ')`, and both `u` and `u⁻¹` lie in `𝒪` by the unit criteria. So `Φ' = uΦu⁻¹`.
8. **Assembly** (`conjRel_card_le`).
   * Fix a base embedding and, for each type, a representative `Ψ` of that type.
   * Map `Φ ↦ (class of 𝔞(Ψ_{type Φ}, Φ), type Φ)`, and read the map on `Quot` through `Quot.out`.
   * The result is `Finite` and has `#Emb/~ ≤ #Pic(R) · #T = 2^b h(R)` (`card_types`).

Statement fidelity: `R5fpCountLe` and the definitions it uses (`OptEmb`, `ConjRel`, `conductor`,
`inertCount6`, `CommRing.Pic`) are unchanged. The final module imports `GR56Lattice`, which defines them.
VERIFIED: the definitions come from `GRCountX6`, and the development copy was removed before the final build.

## 3. Files (VERIFIED: compiled)

| file | content |
|---|---|
| `ZInQKernel/Contrib/OneProof/R5fpCountLe.lean` | the two final theorems (imports `GR56Lattice`) |
| `…/EichlerBound/Order.lean` | arithmetic of `𝒪`: `nrd`, `ℓ𝒪`, `P₂`, `P₃`, `frob`, the minor certificate, the Euclidean algorithm |
| `…/EichlerBound/Quadratic.lean` | `R = ℤ + ℤω`, the ramified element, Lemma D at 2 |
| `…/EichlerBound/Defs.lean` | imports `GRCountX6` (`OptEmb`, `ConjRel`) |
| `…/EichlerBound/Embed.lean` | embeddings, conjugation `sk`, centralizer, intertwiners, Skolem–Noether |
| `…/EichlerBound/Unit.lean`, `Crit.lean` | bad primes, the conjugation trick, the unit criteria |
| `…/EichlerBound/Key.lean`, `Key6.lean` | no bad prime (`ℓ ∤ 6`; `ℓ ∣ 6` with types) |
| `…/EichlerBound/Inv.lean`, `Count.lean`, `Bound.lean` | invertibility, injectivity, `Pic`, the count |
| `scratch/eichler-bound/` | `log.md`, sympy and python checks (`cert_L.py`, `cert2.py`, `checkP.py`, `fac.py`), `gen_bypass.py` and `BypassFold.lean`, `autofold.json`, `Discharges.lean` |

Every finite check is kernel-checked: `decide` (residues mod 2 and 3), `ring` / `linear_combination` (the
certificate identities) and `omega`. None uses `native_decide`.

## 4. The fold (bypass)

autofold.py cannot fill `gonzalezRotgerProp56X6` with the weaker `R5fpCountLe`. As in gr-dict §2.2, the reroute
is a bypass:

* `scratch/eichler-bound/gen_bypass.py` is gr-dict's generator with two changes:
  * `OpenResearchLeaves26E` is `OpenResearchLeaves26` minus `gonzalezRotgerProp56X6`, with no replacement field.
  * `r5le := EichlerBound.r5fpCountLe_proof t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`.
* The generator writes `scratch/eichler-bound/BypassFold.lean` with `sixContactMin_of_open35E` and
  `ZInQ.Contrib.TYZChain.frozenTarget_E`: Main's `frozenTarget` over `OpenResearchLeaves26E`, which has neither
  `gonzalezRotgerProp56X6` nor an Eichler leaf. gr-dict's `F` variant (its `gonzalezRotgerX6Ab` replacement) is
  left out, so that the module does not import `GRDict`; the two reroutes are independent and combine as in
  gr-dict's generator.
* For the integrator: landing it is the same as gr-dict's (a) or (b). Rerun the generator against the top that is
  current at fold time, and add its output as the next `TailZ` module.
* Compile status: see §6.

## 5. Autofold spec and rating

* `scratch/eichler-bound/autofold.json` is a count-only spec for the field `gonzalezRotgerProp56X6`, with no
  new leaf.
  * Its proof text names the bypass, because a weaker statement cannot fill the old field.
  * The dry-run against the tree's kinds.tsv, and against a simulated re-rating, is in §6.
* **New leaves: none.** `eichlerOptEmbBound6` is proved, so nothing needs a print rating. For comparison, the
  printed form of Eichler's count (gr-dict §2.3) is Voight, *Quaternion Algebras*, Thm 30.4.7 (UNVERIFIED).
  The theorem here is its upper half at `𝒪 ⊂ (2, −3)`, never stronger.

## 6. Checks

* `lake build ZInQKernel.Contrib.OneProof.R5fpCountLe`: builds (12938 jobs), with GRCountX6's own definitions.
  VERIFIED, log `scratch/eichler-bound/build-final.log`.
* `#print axioms` (in `scratch/eichler-bound/Discharges.lean`): `EichlerBound.eichlerOptEmbBound6` and
  `EichlerBound.r5fpCountLe_proof` use `[propext, Classical.choice, Quot.sound]`. VERIFIED.
* `#discharges` (`scratch/eichler-bound/discharges.txt`): 56 open hypotheses, 3322 theorems checked.
  * No theorem of this task discharges a field outright, because `R5fpCountLe` is weaker than
    `gonzalezRotgerProp56X6`. The reroute is the bypass of §4.
  * The ten listed discharges come from imported modules: GR56's three `gonzalezRotgerProp56X6_of_*` (with the
    Eichler leaf), `GRCountX6.prop56X6_of_r5fpCount` and six others.
* `autofold.py --dry-run`: `scratch/eichler-bound/autofold-dryrun.txt` (tree) and
  `autofold-dryrun-rerated.txt` (simulated GLUE rating of the row). The counts are in §1. VERIFIED.
* `BypassFold.lean`: see `scratch/eichler-bound/bypass-compile.txt` (status recorded in §7).

## 7. Status of the bypass compile

`lake env lean scratch/eichler-bound/BypassFold.lean` compiles. VERIFIED, output in
`scratch/eichler-bound/bypass-compile.txt`:

```
'HDec.HSyn.sixContactMin_of_open35E' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZChain.frozenTarget_E' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `frozenTarget_E` is Main's `frozenTarget` with `OpenResearchLeaves26E`, the research bundle minus
  `gonzalezRotgerProp56X6`, with nothing added.
* The module never mentions `EichlerOptEmbCount6` (`grep` count 0). Its only use of the count is
  `r5le := EichlerBound.r5fpCountLe_proof t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`.
* To compile it, the build tree was taken from a sibling worktree, the deps were rebuilt with
  `lake build <the 10 imports>` (13709 jobs), and `lean/.lake/build` was copied.

## 8. What remains

* Folding the bypass, which is the integrator's step (§4).
* Optionally, the lower half of Eichler's count, which would give equality and `R5fpCount` itself. The chain does
  not need it. The injection of §2 is in fact a bijection onto `Pic(R) × {occurring types}`, but surjectivity
  (the twist action `Φ ↦ Φ^𝔞`) is not formalized.
