# glue-d1-local: the local form of D1's degree bound `e ≤ a!`

Status: research note (task glue-d1-local, 2026-11-11).
- Lean file: `scratch/glue-d1-local/Local.lean`. It copies glue-conductor's `Breaks.lean` verbatim (minus its `#print` lines) and adds the namespace `GlueD1Local`.
- Results log: `scratch/glue-d1-local/log.md`.
- No file under `ZInQKernel/`, `blueprint/`, or another task's directory was edited.

Marks:
- **VERIFIED**: compiled, or read in a source.
- **STANDARD**: a published theorem. Locators given from memory are marked UNVERIFIED.
- **SPECULATIVE**: an assessment.

## Main result

**D1's degree bound is proved in its local form, through the decomposition group, and connected to `D1_genuine`.** No `sorry`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every theorem below. VERIFIED: `lake env lean scratch/glue-d1-local/Local.lean`, 23:49 PST, no errors and no warnings.

Setting:
- `L/ℚ` is a finite Galois number field and `G = Gal(L/ℚ)`.
- `P` is a prime of `𝓞 L` over `p`, and `D_P = MulAction.stabilizer G P` is its decomposition group.
- `K` is an intermediate field, `H = K.fixingSubgroup = Gal(L/K)`, and `w = P.under (𝓞 K)`.

Under the completion dictionary (§2), `D_P = Gal(L_P/ℚ_p)` and `D_P ∩ H = Gal(L_P/K_w)`. So Glazer's hypotheses become conditions on groups and ideals:
- "`L_P` is the Galois closure `F̃` of `F = K_w`" becomes: `D_P ∩ H` has trivial normal core in `D_P`.
- "`[F:ℚ_p] ≤ a`" becomes: `e(w|p)·f(w|p) ≤ a`.

| Lean name | Statement | Status |
| --- | --- | --- |
| `card_le_factorial_index_of_normalCore_eq_bot` | `H ≤ D` finite with `core_D(H) = ⊥` ⇒ `\|D\| ≤ [D:H]!` | VERIFIED |
| `ramificationIdx_le_card_decompGroup` | `e(P\|p) = \|I_P\| ≤ \|D_P\|` | VERIFIED |
| `card_decompGroup` | `\|D_P\| = e(P\|p)·f(P\|p)` | VERIFIED |
| `index_localSub` | `[D_P : D_P ∩ Gal(L/K)] = e(w\|p)·f(w\|p)` (the local degree `[K_w:ℚ_p]`) | VERIFIED |
| `ramificationIdx_le_factorial_local` | trivial core and index `≤ a` ⇒ `e(P\|p) ≤ a!` | VERIFIED |
| `D1_local`, `D1_local'` | `D1_genuine` with `hea : e ≤ a!` replaced by the local hypotheses (index, or `e(w\|p) f(w\|p) ≤ a`); conclusion `φ(b) ≤ 4a²` for every lower index `b` with `G_b ≠ 1` | VERIFIED |
| `normalCore_subgroupOf_eq_bot` | `G = H·D` and `core_G(H) = ⊥` ⇒ `core_D(H ∩ D) = ⊥` | VERIFIED |
| `fixingSubgroup_mul_decompGroup` | `K` has a single prime over `p` ⇒ `G = Gal(L/K)·D_P` | VERIFIED |
| `normalCore_fixingSubgroup_eq_bot` | `normalClosure ℚ K L = ⊤` ⇒ `core_G(Gal(L/K)) = ⊥` | VERIFIED |
| `ramificationIdx_le_factorial_of_unique`, `D1_krasner`, `D1_krasner'` | `L` is the normal closure of `K`, `K` has one prime `w` over `p`, and `e(w\|p) f(w\|p) ≤ a` ⇒ `e(P\|p) ≤ a!` and `φ(b) ≤ 4a²` | VERIFIED |

The final statement, `D1_krasner'`, has these hypotheses:
- the two leaves of `D1_genuine`, `HilbertDifferentFormula` and `SerreDifferentBound`;
- `IntermediateField.normalClosure ℚ K L = ⊤`;
- every prime `v` of `𝓞 K` over `p` equals `w`;
- `1 ≤ a` and `(P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a`;
- `ramGroup L P b ≠ ⊥`.

Its conclusion is `phi (ramCard L P) b ≤ 4 * a ^ 2`. Every hypothesis is a Mathlib predicate; no structure was invented for the purpose.

## 1. Proofs (summary)

- **`e ≤ |D_P|`.**
  - `Ideal.card_inertia_eq_ramificationIdxIn` and `ramificationIdxIn_eq_ramificationIdx` identify `e(P|p)` with `|I_P|`.
  - `Ideal.inertia_le_stabilizer` gives `I_P ≤ D_P`.
- **`|D| ≤ [D:H]!` when the core is trivial.** Mathlib's `Subgroup.index_normalCore_dvd_factorial_index` (`D` acts on `D/H` with kernel `core_D(H)`), with `index ⊥ = |D|`.
- **The index is the local degree.**
  - `Ideal.card_stabilizer_eq` gives `|D_P| = e(P|p) f(P|p)` over `ℤ`.
  - The same lemma over `𝓞 K`, with `G = K.fixingSubgroup`, gives `|Stab_H(P)| = e(P|w) f(P|w)`. The equivalence `D_P ∩ H ≃ Stab_H(P)` is the identity on elements.
  - `Ideal.ramificationIdx_tower` and `Ideal.inertiaDeg_tower` give `e(P|p) = e(w|p) e(P|w)` and the same for `f`. Cancelling gives the index.
- **Instance note.** `IsGaloisGroup K.fixingSubgroup (𝓞 K) (𝓞 L)` is not synthesized automatically. It is built from `IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L K`, then `IsGaloisGroup.of_isFractionRing`.
- **Unique prime ⇒ `G = H·D_P`.**
  - Take `g ∈ G`. The prime `g•P` lies over `p` (`Ideal.under_smul`), so `(g•P) ∩ 𝓞 K = w`.
  - `Algebra.IsInvariant.exists_smul_of_under_eq` for `H` acting on `𝓞 L` over `𝓞 K` gives `h ∈ H` with `h•P = g•P`. Then `h⁻¹g ∈ D_P`.
- **Core in `D`.** Write `g = h·d`. Then `g x g⁻¹ = h (d x d⁻¹) h⁻¹ ∈ H`. So `core_D(H ∩ D) ≤ core_G(H) = ⊥`.
- **Normal closure ⇒ trivial core.**
  - `N = core_G(H)` is normal and fixes `K`, so `K ≤ fixedField N`.
  - `fixedField N` is normal over `ℚ`, by Mathlib's instance for the fixed field of a normal subgroup.
  - Hence `normalClosure ℚ K L ≤ fixedField N` (`normalClosure_le_iff_of_normal`), so `fixedField N = ⊤`.
  - By `fixingSubgroup_fixedField`, `N = fixingSubgroup ⊤ = ⊥`.

## 2. What connects this to Glazer's local D1 (not in Lean)

Glazer's D1 (N5 L796-812; glue-conductor §D1) is about a local field: `F/ℚ_p` of degree `≤ a`, with Galois closure `F̃`. The Lean statements are about a global `L`. Two transports connect them. Both are standard, and neither is in Mathlib.

1. **Krasner-type choice of `K` (STANDARD).** For a finite `F/ℚ_p` of degree `n`, write `F = ℚ_p(β)` with minimal polynomial `g`.
   - Krasner's lemma and the density of `ℚ[X]` give a monic `g₀ ∈ ℚ[X]`, `p`-adically close to `g`, with a root `α₀` such that `ℚ_p(α₀) = F`.
   - `g₀` is irreducible over `ℚ_p`, hence over `ℚ`. So `K = ℚ(α₀)` has degree `n` and exactly one prime `w` over `p`, with `K_w ≅ F`.
   - Reference: e.g. Lang, *Algebraic Number Theory*, II §2 (UNVERIFIED locator).
   - So the hypotheses `hunique` and `e(w|p) f(w|p) = n ≤ a` of `D1_krasner'` hold, and `L` is taken to be the normal closure of `K`.
2. **Decomposition group = local Galois group (STANDARD), with filtrations.**
   - `D_P ≅ Gal(L_P/ℚ_p)` by continuity, and this sends `D_P ∩ Gal(L/K)` onto `Gal(L_P/K_w)`.
   - The global groups `ramGroup L P i = (P^{i+1}).inertia G` go to the lower ramification groups `G_i(L_P/ℚ_p)`.
   - Reference: Serre, *Corps locaux*, II §3 and IV §1 (UNVERIFIED locators).
   - Given this, `normalCore_subgroupOf_eq_bot` shows that `L_P` is the Galois closure of `K_w = F`. So `L_P = F̃`, and `D1_krasner'`'s `φ(b) ≤ 4a²` is exactly Glazer's bound for `F̃/ℚ_p`.
   - `D1_genuine` already rests on the filtration part of this transport (its docstring). The new results add no transport beyond it.

So **D1 holds in the form N5 uses, granted the two STANDARD transports above**: `G_{ℚ_p}^u ⊆ G_{F̃}` for `u > 4a²`. This also needs Herbrand's theorem, glue-conductor's leaf L3, which is unchanged.

In the application (N5, D2(iii)):
- `F = L_v(A[n])` and `a = D·G₀` (glue-conductor §D2(i)). Only the local degree is bounded there.
- So the decomposition-group form is the right one. The global degree of a number field realizing `F` may be larger, unless one makes the Krasner choice of item 1. With that choice, `[K:ℚ] = [F:ℚ_p]`, and glue-I6-rest's global `ramificationIdx_le_factorial` would also apply.
- `D1_local'` needs no uniqueness. It applies to any `K ⊆ L` with `L_P = F̃`.

## 3. What remains

- **Not formalized:** the two transports of §2. They need `ℚ_p`-structures on Mathlib's `adicCompletion` and the Galois action on it, which Mathlib 4.35 does not provide (SPECULATIVE effort: weeks).
  - If they are adopted as leaves, the natural statement is: `D_P ≃* Gal(L_P/ℚ_p)` compatibly with the ramification filtrations, plus Krasner's lemma for `ℚ_p`.
- **Integration.** `Local.lean` contains a copy of `Breaks.lean`. At integration the `GlueD1Local` section should sit after `GlueConductor.D1_genuine`, with the copy dropped.
- **Unchanged:** D1's remaining leaves L1, L2 and L3 are as in glue-conductor.
