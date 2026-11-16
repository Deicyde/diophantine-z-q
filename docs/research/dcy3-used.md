# dcy3-used: `deligneComponentsY3PrintedAb` is used only as "Y₃ is connected", and that follows from fields already in the bundles

Task dcy3-used, 2026-11-15. Base `43513d87` (leaf-fold25, 56 H fields). Lean: `ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean`
(new, namespace `DCY3Used`). Scratch: `scratch/dcy3-used/`:

* `log.md`;
* `Part1.lean` to `Part6.lean` (the pieces) and `Y3Conn.lean` (the pieces together);
* `Discharges.lean` and `Discharges-output.txt`;
* `BypassFold.lean` and `BypassFold-output.txt`;
* `autofold.json`.

Marks: **VERIFIED** means read in a source, computed or compiled. **STANDARD** means published, with the reference
given. **SPECULATIVE** is marked as such. There was no network, so every theorem number recalled from memory is
**UNVERIFIED**.

## 1. Result

**The field can be removed with no new leaf.** The strict GLUE count drops by 1, and so does the strictest count.

1. *Used form.* The chain reads the field once, as `TSHecke.Y3Connected`: some fine witness `Y₃` is connected over
   `ℚ` (§2, VERIFIED by reading). It uses neither the bijection `π₀(Y₃,ℚ̄) ≃ ℚ^×_{>0}\𝔸_f^×/nrd(K₃)` nor the Galois action
   beyond that consequence. The weakest used form is `DCY3Used.Y3ConnectedAb`:
   `∃ Y Φ, R1fpPropsAb Y Φ ∧ ConnectedSpace Y.left`.
2. *Proved from the bundles (VERIFIED, compiled, standard axioms).*
   ```lean
   theorem DCY3Used.y3ConnectedAb_of_U :
       RayClassCFT.ShimuraMainThmIDeligneY3AbU → DCY3Used.Y3ConnectedAb
   theorem DCY3Used.y3ConnectedAb_of_field :
       ShimuraGlue.DeligneComponentsY3PrintedAb → DCY3Used.Y3ConnectedAb      -- the used form is not stronger
   theorem DCY3Used.y3Connected_of_leaves :
       ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw → RayClassCFT.ShimuraMainThmIDeligneY3AbU →
         HDec.TSHecke.Y3Connected                                             -- the chain's form
   ```
   - `shimuraMainThmIDeligneY3AbU` and `mumfordGroupLaw` are both fields of `OpenResearchLeaves22` already.
     `shimuraMainThmIDeligneY3AbU` is Shimura's Main Theorem I in Deligne's adelic form on `Y₃`, from gt-rayclass.
   - The rest of the proof uses only material already proved:
     - Eichler's class number one (`RayClassCFT.classNumberOneB_proof`, proved);
     - Tau Ceti's absolute Artin map;
     - Steinitz's extension of automorphisms to `ℂ` (`T5Glue.exists_ringEquiv_extend`, proved);
     - a 36-row `decide` table over `𝒪/3𝒪`.
3. *Fold.* The used form is weaker than the field, so `autofold.py` cannot fold it. A hand bypass straight to
   leaf-fold8's `OpenAddedLeaves8`, where `y3Connected` is a field, compiles. This includes a copy of `frozenTarget`
   on the new 14-field added bundle, with standard axioms (§5).
4. *What it does not do.* The field itself, Deligne's bijection with its Galois action, is **not** derived. Its lower
   bound, that `Y₃ ×_ℚ ℚ̄` has at least two components, needs one of two inputs, and neither is a field or a Lean
   object:
   - a regular function separating the two components (the Weil pairing value `e₃(η)`);
   - the open mapping theorem on the analytic space `Y₃(ℂ)`.

   The chain never needs this lower bound.

**Leaf rating.** No new leaf. Removing the field also removes its pending reading: does one display state that the PEL
moduli scheme with its uniformization is the canonical model at `B = (2,−3|ℚ)`, level `K₃`? That question does not
disappear. It now rests entirely on `shimuraMainThmIDeligneY3AbU`, a composite GLUE row whose docstring cites Shimura
1967 Main Thm I and Deligne 1971 §§3-4 for the same identification (moduli scheme = canonical model). That row was
already needed by `rayClassCMAb` and `shimuraFamilyAb`. §4 lists the clauses of it that this proof reads, for its
reviewers.

## 2. The consumers (VERIFIED, read)

| step | where | what is read |
|---|---|---|
| `OpenAddedLeaves17.deligneComponentsY3PrintedAb` | TailZ34 → Z31 → Z30 → Z26 → Z24 (`openAddedLeaves16_of_…` etc.) | copied unchanged down to `OpenAddedLeaves12` |
| `OpenAddedLeaves12` → leaf-fold10's `OpenAddedLeaves9` | `TailZ23.addedLeaves9_of_open14` | `deligneComponentsY3Printed := (deligneComponentsY3Printed_iff_ab_gl (qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr l.deligneComponentsY3PrintedAb` |
| `OpenAddedLeaves9` → `OpenAddedLeaves8` | `TailZ13.addedLeaves8_of_open9` | `y3Connected := y3Connected_of_deligne (deligneComponentsY3_of_printed l.deligneComponentsY3Printed)` |
| `y3Connected : TSHecke.Y3Connected` | `TailK` (`propTSAll_of_pieces3 … l.y3Connected …`) → `coverModelOfHecke_of_heckeRest` → `heckeIrreducible_of_connected` (TailG l. 8380) | `connectedSpace_of_R1fp`: every fine witness is connected; with proper + smooth of relative dimension 1 it is irreducible (`HeckeIrreducible`) |

No other reader. `git grep` lists the other files that mention the field or `y3Connected`. The older generations
(TailN, O, X, Z4) only copy the field, and route-a-fold's TailZ17, TailZ18 and TailZ22 are off the current path,
which TailZ23 bypasses. The decisive check is the dry run of §5: a `frozenTarget` without the field compiles.

`connected_of_heckeIrreducible` (TailG) shows the converse inside the chain: given the bundle leaf `R1R2fp`,
`HeckeIrreducible` implies `Y3Connected`. So connectedness is exactly what the consumer needs.

## 3. The used form

`DCY3Used.Y3ConnectedAb := ∃ Y Φ, LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ ConnectedSpace Y.left`. This is the
abelian-scheme clause list, as in the field. `y3Connected_of_ab_gl` turns it into the chain's
`HDec.TSHecke.Y3Connected` (stated on `R1fpProps`) by `r1fpProps_eq_ab_gl` under `QMFamilyGroupLaw`, the same step
TailZ23 applies to the field.

Not stronger than the field: `y3ConnectedAb_of_field` is shimura-glue's computation `ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×`
followed by shimura-split's orbit argument. The clause list is used only for its `ℚ̄`-point (`connected_of_delignePi0`).

## 4. The proof (paper; every step compiled)

Let `(Y, Φ, Ψ)` satisfy `DeligneBodyAt`. That gives:

* `Ψ : ℍ × (B ⊗ 𝔸_f)^× → Y(ℂ)` onto;
* `Ψ(τ,g) = Ψ(τ',g')` iff `(τ',g') = (γτ, γgk)` with `γ ∈ B`, `nrd γ > 0`, `k ∈ K₃`;
* `τ ↦ Ψ(τ,g)` holomorphic (`IsHolFamily`);
* the reciprocity law `σ(Ψ(z,g)) = Ψ(z, q̂(s)^ε g)` at CM points.

Fix a clopen `U ⊆ Y` and put `χ(g) = [Ψ(i,g) ∈ U]`.

1. **`χ` does not depend on `τ`.** `{τ : Ψ(τ,g) ∈ U}` and its complement are open: preimages of the Zariski opens
   `U` and `Uᶜ`, by the first clause of `IsHolFamily`. `ℍ` is connected.
2. **Invariance under `B^×_+` and `K₃`.** If `g' = γgk`, then `Ψ(i,g) = Ψ(γi, g')`, by the "←" direction of the
   uniformization clause, so `χ(g) = χ(g')`.
3. **Invariance under `h = q̂(s)`.** Set up the CM data as follows:
   - `K = ℚ(i)` (`ShimuraGlue.Ray.K4`);
   - `q : i ↦ β = i + j`, with `β² = −1`, `β ∈ 𝒪` and `q(𝒪_K) ⊆ 𝒪`;
   - CM point `τ₀ = √2 + i` (`ι(β)(τ₀,1)ᵀ = i·(τ₀,1)ᵀ`, `heig0`), reflex embedding `κ₀ : i ↦ i`.
     For either sign `δ`, take `κ = κ₀` or `κ = κ̄₀`, so that the hypothesis `IsCMPoint q (if δ then κ else κ̄) τ₀` holds.
   - `s` is the idele equal to `c = 1 + i` at the place above 3 and to `1` at every other place, finite or infinite.

   Every idele `s` is `[s, K]` for some `σ ∈ Aut(ℂ)` (`exists_sigma_artinCondC`). This is Tau Ceti's absolute Artin
   map composed with Steinitz's extension. For `ε = −1`, use `s⁻¹`. `σ` does not move the underlying point of a
   `ℂ`-point (`ptC_galPt`), and `U` is a subset of `Y` over `ℚ`, so `χ(hg) = χ(g)`.

   Two facts about `h`:
   - `s = c + 3b` with `b` integral (`u4_eq`, `b4_mem`):
     - at the place above 3, `b = 0`;
     - elsewhere, `b = −i/3`, which is integral because `3` is a unit there.
   - `s`, `s⁻¹` are integral, because `c` is a unit above 3 (`c c̄ = 2`). So `h = q̂(s) ∈ 𝒪̂^×` and
     `h ≡ q(c) = 1 + i + j (mod 3𝒪̂)` (`h4_eq`). Here `nrd(1+i+j) = 2 ≡ −1`.
4. **`χ` is constant** (`const_of_inv`).
   - Class number one with `1 + i` of norm `−1` gives `g = γu` with `nrd γ > 0` and `u ∈ 𝒪̂^×`
     (`exists_pos_decomp classNumberOneB_proof`).
   - Approximate `u ≡ x (mod 3𝒪̂)` with `x ∈ 𝒪`, using `exists_int_approx` on the four `ℤ̂`-coordinates. Then
     `N4(x) ≢ 0 mod 3`, because `u u⁻¹ = 1` (`unit3`).
   - The table `table3` (`decide` over `(ℤ/3)⁴`) gives `γ ∈ L36 ⊆ 𝒪¹` with `γ̄x ≡ 1` or `γ̄x ≡ 1+i+j`.
   - Hence `u = γk` or `u = γhk` with `k ∈ K₃` (`decomp3`).

   **Computation (VERIFIED, Python, then `decide`).** `𝒪/3𝒪` has 72 units, since `B` is ramified at 3 and
   `𝒪₃/π𝒪₃ = 𝔽₉`. They fall into 36 classes of reduced norm 1, all reached by `𝒪¹`. These 36 classes and their
   translates by `1+i+j` cover all 72 units.

   Then `χ(g) = χ(u) = χ(1)` or `χ(g) = χ(u) = χ(h) = χ(1)`.
5. **Conclusion.** A nonempty open subset of `Y` contains the point of a `ℂ`-point (`exists_C_point`). The argument
   goes through a closed point (`JacobsonSpace`), then a `ℚ̄`-point (`HDec.ModelGlue.exists_qbarPt`), then
   `ιC : ℚ̄ → ℂ`. Every `ℂ`-point is some `Ψ(τ,g)`. If `U` and `Uᶜ` were both nonempty, `χ` would take both values.

**Clauses of `shimuraMainThmIDeligneY3AbU` that are read** (for that row's reviewers):

| clause | used? |
|---|---|
| `Ψ` onto `Y(ℂ)` | used |
| uniformization: equal images ⇐ `DCRel` | used |
| uniformization: equal images ⇒ `DCRel` | not used |
| `IsHolFamily`: openness of preimages of Zariski opens | used |
| `IsHolFamily`: analyticity | not used |
| `IsShimuraHolFamily` | not used |
| `ModuliAtUnits` | not used |
| `R1fpPropsAb`: properness (for `LocallyOfFiniteType`) | used |
| reciprocity law: at `K = ℚ(i)`, `q : i ↦ i + j`, `z = √2 + i` and one idele | used |

**Sanity (STANDARD; not used in the proof).** The conclusion is true for the genuine `Y₃`. `Sh_{K₃}(B^×)` over `ℚ̄` has
`ℚ^×_{>0}\𝔸_f^×/nrd(K₃) = ℤ̂^×/(nrd K₃) = (ℤ/3)^×` components, two of them, and `Gal(ℚ(√−3)/ℚ)` swaps them (Deligne,
Sém. Bourbaki 389 (1971) §§2-3; Milne, *Introduction to Shimura varieties* (2005) Thm 5.17 and §13; numbers
UNVERIFIED). In the proof this is the class of `nrd h ≡ −1`. Over `ℚ(i)`, `σ = [s,K]` acts on `ζ₃` by
`N(c) = 2 ≡ −1`, which is consistent: the proof never needs to know `σ(ζ₃)`.

## 5. The fold (VERIFIED, compiled dry run)

`#discharges` (`scratch/dcy3-used/Discharges-output.txt`): `63 open hypotheses, 1895 theorems checked, 7 discharge one`.
The seven are other contributions already imported by `Main`. No open field is matched by `DCY3Used`, which is expected
because the used form is weaker than the field. sir-printed had the same situation.

`autofold.py` maps generation `k+1` to `k`, and every added bundle from `OpenAddedLeaves17` down to leaf-fold10's
`OpenAddedLeaves9` carries the field. So the fold is a bypass, following leaf-fold14's pattern (TailZ23 is itself one).
The dry run is `scratch/dcy3-used/BypassFold.lean`, and both `#print axioms` lines are `[propext, Classical.choice,
Quot.sound]`:

* `OpenAddedLeaves18`: `OpenAddedLeaves17` minus `deligneComponentsY3PrintedAb` (14 fields).
* `x6Rows_of18`, `ss1_ss3_of18`, `researchLeaves9_of18`: TailZ23's terms on the new bundle.
  `semistableAlmostAll_of10` is inlined; it reads only `egaIV_8_10_5_xii`.
* `addedLeaves8_of18 r22 r14 t10 l : OpenAddedLeaves8`:
  - built from the terms of the added maps of TailZ34, Z31, Z30, Z26, Z24, `TailZ23.addedLeaves9_of_open14` and
    `TailZ13.addedLeaves8_of_open9`;
  - `y3Connected := DCY3Used.y3Connected_of_leaves r22.mumfordGroupLaw r22.shimuraMainThmIDeligneY3AbU`.
* `sixContactMin_of_open30 r t l g`:
  - composes the research maps `22 → 14` and `openTextbookLeaves10_of_OpenTextbookLeaves11` unchanged;
  - calls `sixContactMin_of_open10` with leaf-fold14's `hF5` and the `hYu` of TailZ30.
* `frozenTarget_dcy3`: `Main.lean`'s `frozenTarget` with `l : OpenAddedLeaves18` and `sixContactMin_of_open30`.

`scratch/dcy3-used/autofold.json` records the bypass with no leaves. kinds.tsv loses the row
`deligneComponentsY3PrintedAb` (strict GLUE, strictest GLUE) and gains none.

## 6. What remains

* The integrator's hand fold (§5): a new `TailZ<k>` with the dry run's content, `Main.lean` switched, kinds.tsv and
  claims.tsv rows removed, then the hash check and OPEN.md regenerated. I did not edit anything under
  `ZInQKernel/` except the new Contrib file.
* The reading question moves to `shimuraMainThmIDeligneY3AbU`. Is Shimura's Main Theorem I with Deligne's adelic
  reciprocity, on the moduli scheme `Y₃` with level `K₃`, a printed display? See that row; it was already open.
* Deligne's bijection itself (the field as stated) stays unproved. It is not needed (§1, item 4).
