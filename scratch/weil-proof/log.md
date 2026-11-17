# weil-proof results log

Base 0caafe66 (origin/main) + merge of origin/wip/pic-dict 4e95795b (PicDictionary.lean, clean merge).

## Statement
`T09Pic.WeilPairingMumford` (ZInQKernel/OneProof/H/TailZ24.lean:708), field `OpenAddedLeaves17.weilPairingMumford`.
pic-dict: `PicDict.weilPairingMumford_final` from 7 Mumford leaves over k = k̄ (MumfordSquareAC, MumfordMulNPicZeroAC,
MumfordPhiSurjectiveAC, MumfordWeilPairingAC, MumfordWeilNondegAC, MumfordWeilAltAC, MumfordKLFiniteAC).
weil-used (origin/wip/weil-used 8ea3eaf3): consumers read only left kernel, Galois, compat, e(x, λ_L x) = 0 (VERIFIED there by probe).

## 11-16 results (scratch/weil-proof/Generic.lean, imports ZInQKernel.Contrib.OneProof.PicDictionary)
- VERIFIED (compiles, standard axioms): generic lemmas on `PicDict.Transport.wf` over any scheme:
  `wf_comp` (cocycle wf(t1≫t2) = t1^*(wf t2)·wf t1), `wf_id` (wf 𝟙 = 1), `wf_isUnit`, `wf_change`
  (change of trivialization, ratio t-invariant ⇒ same value).
- VERIFIED: over any field k, X : AbVar k: translations act trivially on Γ(X,𝒪) (`tr_appTop`, from the vendored
  bijectivity of constants), `formula_indep` (part (i)), `formula_root` (part (ii)), `formula_mul` (part (iii)),
  `formula_pow`. IsAlgClosed not needed.
- VERIFIED: `mumfordWeilPairingAC_of_bilinRight : MumfordWeilBilinRightAC → MumfordWeilPairingAC`;
  `weilPairingMumford_of_bilinRight` (7 leaves: pic-dict's six other + MumfordWeilBilinRightAC); axioms standard.
- Finding: part (iv) (multiplicativity in the class) needs monoidal coherence of the vendored pullback monoidal
  structure (built by localization lifting) with Mathlib's `Scheme.Modules.pullbackComp` (adjunction-mate) and
  `pullbackObjUnitIso` vs ε. Not in the tree; out of reach today.
- VERIFIED: `wf_tensor_ratio` (from `PullbackCompMonoidal`: wf(ψ⊗ψ')·r_t = wf ψ · wf ψ', r_t = ratio of
  pullbackObjUnitIso⁻¹ and ε), `wf_unit`, `unitRatio_tr` (r_t = 1 for translations, derived: no unit-coherence
  hypothesis needed), `mumfordWeilBilinRightAC_of_pullbackCompMonoidal`,
  `mumfordWeilPairingAC_of_pullbackCompMonoidal : PullbackCompMonoidal → PicDict.MumfordWeilPairingAC`,
  `weilPairingMumford_of_pullbackCompMonoidal` (6 Mumford leaves + GLUE PullbackCompMonoidal); standard axioms.
- `PullbackCompMonoidal`: Mathlib's `Scheme.Modules.pullbackComp f g` commutes with the vendored tensorators μ
  (Modules/PullbackMonoidal.lean, built by Localization.Monoidal.functorMonoidalOfComp). Not proved: needs the
  presheaf-level pullbackComp monoidal + compatibility of `sheafificationCompPullback` with pullbackComp
  (conjugate computation). Rated GLUE (formal, STANDARD in the theory: pullback is a monoidal pseudofunctor).
- VERIFIED: `ZInQKernel/Contrib/OneProof/WeilFormula.lean` builds (lake build); `#discharges`
  (scratch/weil-proof/discharges.txt): `weilPairingMumford` by `WeilProof.weilPairingMumford_proof`, still assumes
  [MumfordSquareAC, MumfordMulNPicZeroAC, MumfordPhiSurjectiveAC, PullbackCompMonoidal, MumfordWeilNondegAC,
  MumfordWeilAltAC, T09Pic.PhiAmpleIsogeny (open field)], standard axioms.
- Merged origin/wip/pic-fix (PhiAmpleIsogeny.lean identical blob to leaf-fold32b's; PicDictionary.lean identical too).
- VERIFIED: autofold dry run (scratch/weil-proof/autofold.json; Nondeg/Alt flagged pending reading, PullbackCompMonoidal
  project glue): `strict count: 34/11 on 45 -> 37/13 on 50; strictest 34/11 -> 37/13` (needs --allow-rise);
  FoldDryRun.lean compiles, sixContactMin_of_open36 standard axioms.

## 11-16 afternoon: PullbackCompMonoidal proved (scratch/weil-proof/PBM.lean)
- VERIFIED (compiles, `#print axioms WeilProof.pullbackCompMonoidal_proof` = [propext, Classical.choice, Quot.sound]).
- Structure: `mu_sheafified` (Localization.Monoidal.functorMonoidalOfComp_μ for the vendored instance);
  `main_sheafified` (the identity at L A, L B from (E) and (P)); `pullbackComp_monoidal` (all M, N via the counit
  L(M.val) ≅ M and naturality); (E) `ee_comp` (sheaf pullbackComp vs presheaf pullbackComp through
  sheafificationCompPullback: unit chase with unit_leftAdjointUniq_hom_app and unit_conjugateEquiv_symm);
  (P) `pcP_monoidal` from the general lemma `Mates.leftAdjointCompIso_δ` (oplax monoidality of leftAdjointCompIso
  for leftAdjointOplaxMonoidal structures, via Adjunction.isMonoidal_comp) and `eF_monoidal` (presheaf
  pushforwardComp monoidal: tmul computation).
- Pitfall: presheaf pullback in the vendored `pullbackOfCommRingCat ... f.toRingCatPresheafHom` form: the
  composite defeq for `PresheafOfModules.pullbackComp` times out (2M heartbeats); in Mathlib's
  `pullback f.toRingCatSheafHom.hom` form it is instant, and the two forms are rfl-equal. Define the
  composite iso via `Adjunction.leftAdjointCompIso (AD g) (AD f) (AD (f ≫ g)) (eF f g)` with eF typed through the
  sheaf-hom form.
- §23 attempt (scratch/weil-proof/Theta.lean, VERIFIED compiles): generic lifts over endomorphisms
  (`prod`, `mv`), associativity `prod_assoc` (from pic-dict's pullbackComp_assoc_app), commutator relation
  `Comm`, `comm_prod_left` (multiplicative in the first variable, needs t^* to fix Γ), `comm_pw` (a lift
  commutes with its powers), `comm_mv_left`, `comm_smul_left`.

## 11-16 evening
- VERIFIED: `WeilProof.Theta.alt_core` (scheme-level §23 core), `mumfordWeilAltAC_of_div`, `divisibleAC`
  (k-points of an abelian variety over k = k̄ are n-divisible for n invertible; from the tree's
  `mulEtaleAbelianScheme_proof`), `mumfordWeilAltAC_proof`, `weilPairingMumford_final` (4 Mumford leaves +
  open field phiAmpleIsogeny); standard axioms (scratch/weil-proof/Axioms.lean).
- Pitfall: `set` abbreviations in the long §23 assembly made the kernel time out on `theta_rho`; fixed by a
  generic core lemma over variables (`alt_core`).
- Contributor-kit check: removed a `local notation "L"` from WeilFormula.lean (notation is not allowed in merged
  contributions); replaced by `Scheme.Modules.sheafification`.
- Autofold (honest flags, nondegeneracy pending reading): 34/11 on 45 -> 37/11 on 48 (no rise); unread flag:
  -> 38/10. Dry-run modules compile.
