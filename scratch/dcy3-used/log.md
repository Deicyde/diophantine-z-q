# dcy3-used results log

Base 43513d87 (leaf-fold25). Build tree copied from ~/dzq-check2 (bc90deac, same Lean tree).

## Step 1: consumers (VERIFIED, read)

* `HDec.HSyn.OpenAddedLeaves17.deligneComponentsY3PrintedAb` is copied unchanged through the added bundles
  (TailZ34 -> Z31 -> Z30 -> Z26 -> Z24) to `OpenAddedLeaves12`; `TailZ23.addedLeaves9_of_open14` turns it into
  `deligneComponentsY3Printed` (non-Ab) by `deligneComponentsY3Printed_iff_ab_gl (qmFamilyGroupLaw_of_groupLaw
  r.mumfordGroupLaw)`; `TailZ13.addedLeaves8_of_open9` uses it once:
  `y3Connected := y3Connected_of_deligne (deligneComponentsY3_of_printed l.deligneComponentsY3Printed)`.
* `y3Connected : TSHecke.Y3Connected` (TailG l.8352: `∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left`) is used only
  as `hconn` in `propTSAll_of_pieces3` (TailK l.317) -> `coverModelOfHecke_of_heckeRest` ->
  `heckeIrreducible_of_connected` (TailG l.8380): every fine witness is irreducible.
* So the field is used only through "some fine witness Y3 is connected over Q". Neither the bijection
  pi0 = Q>0\Af^x/nrd(K3) nor the Galois action is used beyond that.

## Step 2: weakest used form

`Y3ConnectedAb : ∃ Y Φ, R1fpPropsAb Y Φ ∧ ConnectedSpace Y.left` (abelian-scheme clause list, as the field).

## Step 3: proof of the used form from fields already in the bundles (VERIFIED, compiled)

`ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean` (namespace `DCY3Used`; built with
`lake build +ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used`, 13 s; `#print axioms` of `y3ConnectedAb_of_U`:
propext, Classical.choice, Quot.sound):

* `y3ConnectedAb_of_U : RayClassCFT.ShimuraMainThmIDeligneY3AbU → Y3ConnectedAb` (research field of
  `OpenResearchLeaves22`); internally `y3ConnectedAb_of_mainThmI` from `ShimuraMainThmIDeligneY3Ab` (the moduli clause
  and `IsShimuraHolFamily` are not used).
* `y3ConnectedAb_of_field : ShimuraGlue.DeligneComponentsY3PrintedAb → Y3ConnectedAb` (not stronger).
* `y3Connected_of_leaves : MumfordGroupLaw → ShimuraMainThmIDeligneY3AbU → HDec.TSHecke.Y3Connected`.

Pieces (each compiled in scratch Part1-Part6, then together in Y3Conn.lean):
* `exists_sigma_artinCondC`: every idele s of a number field K is `[s, K]` for some σ ∈ Aut(ℂ) (Tau Ceti absolute
  Artin map + `T5Glue.exists_ringEquiv_extend`).
* `ptC_galPt`: σ does not move the underlying point.
* `table3` (`decide`, 17 s with imports): for every x ∈ 𝒪/3𝒪 with N4 x ≠ 0, some γ in the 36-element list `L36`
  (all of reduced norm 1, `L36_norm` by decide) has γ̄x ≡ 1 or γ̄x ≡ 1+i+j mod 3. Computed first in Python: 72 units
  mod 3, 36 norm-1 classes, all covered (VERIFIED).
* `approx3`, `unit3`, `decomp3`: every u ∈ 𝒪̂^× is γk or γhk (γ ∈ 𝒪¹, k ∈ K3) for any h ∈ 𝒪̂^× with
  h ≡ 1+i+j mod 3𝒪̂.
* K = ℚ(i) (`ShimuraGlue.Ray.K4`): q4 : i ↦ i+j, CM point τ0 = √2 + i, κ0 : i ↦ i (`isCMPoint0`), q4(𝒪_K) ⊆ 𝒪.
* idele s4 = (1+i above 3, 1 elsewhere), u = c + 3b with b integral (`u4_eq`, `b4_mem`); h = q̂(s4) ∈ 𝒪̂^×,
  h = bEmb(1+i+j) + 3 q̂(b).
* `const_of_inv`, `exists_C_point` (Jacobson closed point -> Q̄-point -> ℂ-point), `connected_of_body`.

## Step 4: #discharges (VERIFIED, output in Discharges-output.txt)

`#discharges: 63 open hypotheses, 1895 theorems checked, 7 discharge one` — the 7 are other contributions already
imported by Main; no open field is matched by DCY3Used (expected: the used form is weaker than the field).

## Step 5: fold (VERIFIED, compiled dry run)

`scratch/dcy3-used/BypassFold.lean`: `OpenAddedLeaves18` (14 fields), `sixContactMin_of_open30` mapping to
`sixContactMin_of_open10` (leaf-fold8 generation), and `frozenTarget_dcy3` (copy of frozenTarget on the new bundle);
both `#print axioms` standard (BypassFold-output.txt). Spec: `scratch/dcy3-used/autofold.json` (bypass, no leaves).
Effect on kinds.tsv: row `deligneComponentsY3PrintedAb` (GLUE/GLUE) removed, no row added: strict GLUE −1,
strictest GLUE −1.
