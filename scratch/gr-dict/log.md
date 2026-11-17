# gr-dict results log

Base: origin/main 2880fef1 (leaf-fold31, TailZ42, sixContactMin_of_open35). Marks: VERIFIED / STANDARD / SPECULATIVE / UNVERIFIED.

## Step 0 (2026-11-16 05:20 PST)
- Merged origin/wip/gr56-prove (90b817cb) into wip/gr-dict: clean merge (new files only).
- Build tree copied from ~/dzq-check2 (same base 2880fef1).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GR56Lattice`:
  success, GR56Lattice 118 s on the leaf-fold31 base (VERIFIED). frozenTarget axioms standard (VERIFIED).

## Step 1: bypass fold removing gonzalezRotgerProp56X6 (05:40)
- Consumers in the base (grep `\.gonzalezRotgerProp56X6`, VERIFIED): only TailZ27 L105
  (`gonzalezRotgerCountX6Ab := gonzalezRotgerCountX6Ab_of_printed n.gonzalezRotgerProp56X6 n.gonzalezRotgerX6Ab`),
  then TailZ23 L783 (`gonzalezRotgerCountX6`), TailZ9 L88 (`r5count := r5fpCount_of_points`), TailK L294
  (`FS5NoCM.fibreComTrivialFull_of_leaves'' … r.r5count`, whose only R5fpCount reader is `nocm_on_witness`).
  Agrees with gr56-prove's reach.txt over frozenTarget (97682 constants).
- `scratch/gr-dict/gen_bypass.py` (adapted from st-qbar) writes `BypassFold.lean`: research generations on the live
  path copied with suffix S (ResearchLeaves3, OpenResearchLeaves 2,5,7,8,9,14..26: 19 structures), count field
  replaced by `r5le : GR56.R5fpCountLe`; 71 theorems copied with suffix _S (incl. SGRFold.research14_of_open29,
  heckeSqrtBranchAny_of_open29, G0RevIsog.reverseIsogeny_of_leaves3); 18 forwarding lines replaced;
  TailK consumer → `FS5NoCM.fibreComTrivialFull_of_leaves''_le … r.r5le` (gr56-prove).
  New top: `OpenResearchLeaves26E` (field `eichlerOptEmbCount6 : GRCountX6.EichlerOptEmbCount6` in place of
  `gonzalezRotgerProp56X6`), `openResearchLeaves26S_of_26E` (`r5le := GR56.r5fpCountLe_of_eichler
  n.eichlerOptEmbCount6 t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`),
  `sixContactMin_of_open35E`, `ZInQ.Contrib.TYZChain.frozenTarget_E` (Main's frozenTarget with the new bundle).
- `lake env lean scratch/gr-dict/BypassFold.lean`: compiles; both top theorems
  `[propext, Classical.choice, Quot.sound]` (VERIFIED).
- `BypassReach.lean` (closure of frozenTarget_E, 112698 constants; output bypass-reach.txt, VERIFIED): no
  `R5fpCount`, `GonzalezRotgerProp56X6`, `GonzalezRotgerCountX6`, `GonzalezRotgerCountX6Ab`; the count enters only
  through `GR56.r5fpCountLe_of_eichler` (EichlerOptEmbCount6) and `nocm_on_witness_le`. `GonzalezRotgerX6Ab` is
  still read by `x6Rows_of_open14_S` (via `gonzalezRotgerX6_iff_ab_gl`), i.e. the r1r2 row and X6ConicModel.
- No `shimuraTaniyamaQbar`, no `shimuraMainThmIDeligneY3AbU` used by the reroute (VERIFIED: r5fpCountLe_of_eichler's
  hypotheses are EichlerOptEmbCount6, UniformizationLeafAll, GAGAMorphism, MumfordTorsionAlgClosed).

## Step 2: GR's theorems over GR's own CM points (06:30)
- New contributor file `ZInQKernel/Contrib/OneProof/GRDict.lean` (imports GR56Lattice, ElkiesX6StarPrinted; never
  Main). Definitions: `IsGRCMPoint Ψ R x` (pair of x base-changed along σQ is the torus ℂ²/ι(𝒪)(z,1)ᵀ, z ∈ ℍ the CM
  point `ShimuraCFT.IsCMPoint φ κ z` of an optimal φ : k → B with φ⁻¹(𝒪) = R); `GonzalezRotgerThm512X6` (LEAF);
  `GonzalezRotgerProp56X6CM` (LEAF over GR's CM points, Qbar count; composite of Prop 5.6 + Thm 5.12);
  `X6ModuliWitness` (GLUE composite, witness existence).
- Dictionary proved from uniformizationLeafAll, gagaMorphism, mumfordTorsionAlgClosed only:
  `isGRCMPoint_of_com` (End_𝒪 ≅ R ⇒ GR CM point; datQ, isUniformization_comp, embP/emb_opt),
  `com_of_isGRCMPoint` (converse; latData_of_torus, com_equiv_of_eig, com_bcQ), `isGRCMPoint_iff`.
- Theorems: `r5ptProps_of_thm512`, `gonzalezRotgerX6Ab_of_witness`, `gonzalezRotgerX6Ab_of_printed`
  (witness from elkiesX6StarFunctionField), `x6ModuliWitness_of_elkies`, `x6ModuliWitness_of_gonzalezRotgerX6Ab`,
  `gonzalezRotgerProp56X6_of_cm`. All `[propext, Classical.choice, Quot.sound]` (axioms.txt, VERIFIED).
- `lake build +Main +Discharges +Contrib.OneProof.GRDict` ok; `#discharges` (discharges.txt, VERIFIED):
  gonzalezRotgerX6Ab by gonzalezRotgerX6Ab_of_printed still assumes [GonzalezRotgerThm512X6,
  ElkiesX6StarFunctionField, UniformizationLeafAll, GAGAMorphism, MumfordTorsionAlgClosed];
  gonzalezRotgerProp56X6 by gonzalezRotgerProp56X6_of_cm still assumes [GonzalezRotgerProp56X6CM, three textbook].
  "56 open hypotheses, 3051 theorems checked, 13 discharge one".
- Witness: the existing research field `elkiesX6StarFunctionField` (ElkiesX6StarPrinted.lean L814) is
  `∃ Y Φ X Ψ fY t, R1fpPropsAb ∧ X6Props ∧ …` (VERIFIED, read): it supplies the witness. `shimuraMainThmIDeligneY3AbU`
  gives only Y₃ (no X6Props). No other top field has X6Props.
## Step 3: autofold dry runs (06:40), base kinds.tsv (both GR rows LEAF/LEAF)
- autofold.json (gonzalezRotgerX6Ab → gonzalezRotgerThm512X6): `34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`
  (VERIFIED); FoldCheck.lean (dry-run minus line 1) compiles, sixContactMin_of_open36 standard axioms (VERIFIED).
- autofold-eichler-countonly.json (gonzalezRotgerProp56X6 → eichlerOptEmbCount6; count only, the fold itself is the
  bypass): `34/11 -> 34/11` (VERIFIED).
- autofold-prop56cm.json (flag pending reading → GLUE): refused, GLUE rises 11 → 12 (VERIFIED).
- With the two GR rows re-rated GLUE/GLUE (copy of kinds.tsv in /tmp/grsim, as the 11-16 dictionary pass rates them):
  X6: `32/13 -> 33/12`; Eichler: `32/13 -> 33/12`; Prop56CM: `32/13 -> 32/13`; X6 + Eichler: `32/13 -> 34/11`
  (VERIFIED, simulation; the tree's kinds.tsv untouched).

## Step 4: combined demonstration (07:00)
- gen_bypass.py now also writes `OpenResearchLeaves26F` (= 26E with `gonzalezRotgerX6Ab` replaced by
  `gonzalezRotgerThm512X6`), `openResearchLeaves26E_of_26F` (`GRDict.gonzalezRotgerX6Ab_of_printed`),
  `sixContactMin_of_open35F`, `frozenTarget_F`. Compiled: open35E, open35F, frozenTarget_E, frozenTarget_F all
  `[propext, Classical.choice, Quot.sound]` (VERIFIED, bypass-reach.txt).
- Closure of frozenTarget_F (112744 constants): no R5fpCount / GonzalezRotgerProp56X6 / GonzalezRotgerCountX6(Ab);
  GonzalezRotgerX6Ab only as the value built by gonzalezRotgerX6Ab_of_printed and read by x6Rows_of_open14_S
  (VERIFIED). Neither GR field is an input of frozenTarget_F.

## Step 5: gen_bypass.py parametrized (07:20)
- TOP, the four top bundle names, the imports and frozenTarget's text are now read from Main.lean (frozenTarget_E/_F
  are Main's theorem text with the research bundle and top theorem renamed). Regenerated output differs from the
  previous one only in two docstrings; recompiled, four top theorems standard axioms (VERIFIED).
- Counts in the generated module: 19 structures copied, 71 theorems (70 `_S` + `ResearchLeaves3S.h5`), plus the
  new top (26E, 26F, two maps, two sixContactMin, two frozenTarget).
