# cm-stab: mcr-quot's glue `CMStabObj` (and `CMStabObjWeak`) proved from textbook fields

Branch `wip/cm-stab`, base fork main 9a100aa7 (leaf-fold22b) merged with the earlier cm-stab commits.
Contributor file: `ZInQKernel/Contrib/OneProof/CMStab.lean` (imports only `ZInQKernel.Contrib.OneProof.QMLattice`;
about 72 KB; no `sorry`). `lake build ZInQKernel.Contrib.OneProof.CMStab`: OK (VERIFIED).

## 1. Results (all VERIFIED: compiled, `#print axioms` in `scratch/cm-stab/axioms.txt`)

The statements, copied verbatim (comments in the file name their sources):

```lean
-- copied verbatim from scratch/mcr-quot/MCRQuot.lean L7639-7653 (namespace MCRQuot)
def CMStabObj : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      (∀ m : M3 Qbar, M3.twist α (M3.rightMul u (M3.twist α (M3.rightMul u m))) = m) ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m

-- copied verbatim from ZInQKernel/Contrib/OneProof/QuotientP1/FixedDisjoint.lean L540-546
-- (branch wip/p1-quot at f30ece89; namespace HDec.MCRQuot)
def CMStabObjWeak : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m

-- copied verbatim from ZInQKernel/Contrib/OneProof/QuotientP1/CMStab.lean L435-446
-- (branch wip/p1-quot at d984b2547; there namespace HDec.MCRQuot, here HDec.CMStabAL)
def AtkinLehnerFixesCM24 : Prop :=
  ∀ (A : AbVar Qbar), A.dim = 2 → ∀ q : QMStr A, HasCM24 q →
    Nonempty (QMIso (q.twist (LeafQM.AV.Pin.Exact.rep 3)) q)
```

The theorems (`#check` output, then `#print axioms` output):

```
GapGlue.cmStabObj_of : BPAnalytic.Uniformization.UniformizationLeafAll →
  ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → ObjBridge.TorsionStructure → GapGlue.CMStabObj
'GapGlue.cmStabObj_of' depends on axioms: [propext, Classical.choice, Quot.sound]

GapGlue.cmStabObjWeak_of : BPAnalytic.Uniformization.UniformizationLeafAll →
  ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → ObjBridge.TorsionStructure → GapGlue.CMStabObjWeak
'GapGlue.cmStabObjWeak_of' depends on axioms: [propext, Classical.choice, Quot.sound]

GapGlue.cmStabObj_of_textbook : BPAnalytic.Uniformization.UniformizationLeafAll →
  ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → GapGlue.CMStabObj
'GapGlue.cmStabObj_of_textbook' depends on axioms: [propext, Classical.choice, Quot.sound]

GapGlue.cmStabObjWeak_of_textbook : BPAnalytic.Uniformization.UniformizationLeafAll →
  ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → GapGlue.CMStabObjWeak
'GapGlue.cmStabObjWeak_of_textbook' depends on axioms: [propext, Classical.choice, Quot.sound]

GapGlue.atkinLehnerFixesCM24_of : BPAnalytic.Uniformization.UniformizationLeafAll →
  ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → HDec.CMStabAL.AtkinLehnerFixesCM24
'GapGlue.atkinLehnerFixesCM24_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The source declarations:
```lean
theorem GapGlue.cmStabObj_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hT : ObjBridge.TorsionStructure) : CMStabObj
theorem GapGlue.cmStabObjWeak_of (hU) (hG) (hM) (hT) : CMStabObjWeak     -- same four binders
theorem GapGlue.cmStabObj_of_textbook (hU) (hG) (hM) : CMStabObj        -- hT := AvSplit.torsionStructure_of_mumford hM
theorem GapGlue.cmStabObjWeak_of_textbook (hU) (hG) (hM) : CMStabObjWeak
theorem GapGlue.atkinLehnerFixesCM24_of (hU) (hG) (hM) : HDec.CMStabAL.AtkinLehnerFixesCM24
```

The hypotheses are all named textbook fields already in the bundles: `uniformizationLeafAll`, `gagaMorphism`,
`mumfordTorsionAlgClosed` are fields of `HDec.HSyn.OpenTextbookLeaves11` (`ZInQKernel/OneProof/H/TailZ32.lean` L22,
L23, L15; VERIFIED by grep). `ObjBridge.TorsionStructure` is T5, which the kernel proves from
`mumfordTorsionAlgClosed` (`AvSplit.torsionStructure_of_mumford`; `ObjBridge.torsionStructure_iff :
ObjBridge.TorsionStructure ↔ PkgI2.TorsionStructure.{0} := Iff.rfl`, `ZInQKernel/HDecomp/Objects.lean` L1493); the
`_of_textbook` forms drop it. No new leaf and no glue hypothesis is introduced.

### Identity of the definitions (VERIFIED)
* `CMStabObj`: the text of `scratch/mcr-quot/MCRQuot.lean` L7639-7653, of
  `ZInQKernel/Contrib/OneProof/QuotientP1/MCRQuotB.lean` L976-990 on `wip/p1-quot` (3ce73273; this is the
  `CMStabObj` that `FixedDisjoint.lean` uses, through its import of `MCRQuotB`; its `cMStabObjWeak_of
  (h : CMStabObj)` refers to it) and of `CMStab.lean` (def at L1203, with the same docstring) are identical (diff/md5).
* `CMStabObjWeak`: my copy is byte-identical to `FixedDisjoint.lean` L540-546 (the docstring and the def, inserted by
  a script from `git show f30ece89:…`; the same text at 3ce73273).
* Namespace check: theirs live in `namespace HDec.MCRQuot`, mine in `GapGlue`; inside `HDec` the `open LeafQM …`
  lines resolve to `HDec.LeafQM…` where such names exist. `scratch/cm-stab/NsCheck.lean` elaborates their
  `CMStabObjWeak` text inside `namespace HDec.MCRQuot` with their `open` lines and prints it with `pp.fullNames`:
  the same term as `GapGlue.CMStabObjWeak` (`LeafQM.AV.QML3 LeafQM.AV.Qbar`, `LeafQM.AV.HasCM4`, `LeafQM.AV.M3.twist`,
  …), and `example : CMStabObjWeakT = GapGlue.CMStabObjWeak := rfl` compiles (`scratch/cm-stab/nscheck.txt`). The
  same check for `AtkinLehnerFixesCM24` shows that its `LeafQM.AV.Pin.Exact.rep` is `HDec.LeafQM.AV.Pin.Exact.rep`
  (TailC.lean L957), which is why my copy sits in `namespace HDec.CMStabAL` (the printed term is identical).
  These checks use my import closure, not p1-quot's; when both modules are in one tree, the fold below should
  confirm the identification with `rfl` (it must hold, since both elaborate to the same constants).

## 2. `#discharges` (`scratch/cm-stab/discharges.txt`, VERIFIED)

```
DISCHARGES [OpenResearchLeaves21.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount]
DISCHARGES [OpenResearchLeaves21.neronBaseChangeStrictHenselization] by GapSHPair.neronBaseChangeStrictHenselization_of_unramified
  still assumes: [ReductGlue.NeronBaseChangeUnramifiedDVR]
DISCHARGES [OpenResearchLeaves21.elkiesX6StarPrinted] by HDec.QMSplit.Moduli.ElkiesX6Star.elkiesX6StarPrinted_of_ab
  still assumes: [HDec.QMSplit.Moduli.ElkiesEquationsX6Ab]
DISCHARGES [OpenResearchLeaves21.sga7_IX_3_3_SH] by SGA7PersistsNF.sga7_IX_3_3_SH_of_field
  still assumes: [CToPrinted.SGA7_IX_3_3]
DISCHARGES [OpenResearchLeaves21.sga7_IX_3_5_ForwardGeom] by UnipotentForward.forwardGeom_of_forward
  still assumes: [UnipotentForward.SGA7_IX_3_5_Forward, UnipotentForward.SemiAbelianDescendsSepClosed]
(each with axioms: [propext, Classical.choice, Quot.sound])
#discharges: 63 open hypotheses, 1784 theorems checked, 5 discharge one
```
None of the five is from `CMStab.lean` (they are earlier contributions not yet folded); this is expected, since
`CMStabObj` is not a bundle field. No autofold spec.

## 3. How the result enters the composites (manual fold; for the integration lead)

`CMStabObj` and `CMStabObjWeak` are hypotheses of composites that are not on the base chain yet, so there is no
consumer on my base. They enter as follows.

1. **p1-quot (wip/p1-quot at d984b2547), `ZInQKernel/Contrib/OneProof/QuotientP1Coordinate.lean`.**
   * L83 `quotientP1Coordinate_of_printed' … (hT : PkgI2.TorsionStructure.{0}) (hYI) (hO : CMStabObjWeak)`:
     pass `hO := GapGlue.cmStabObjWeak_of_textbook hU hG hM` (or `GapGlue.cmStabObjWeak_of hU hG hM hT`; `hT` is
     accepted as `ObjBridge.TorsionStructure` by `Iff.rfl`/defeq). Here `hU hG hM` are
     `t.uniformizationLeafAll`, `t.gagaMorphism`, `t.mumfordTorsionAlgClosed` of the `OpenTextbookLeaves11` bundle.
   * L67 `quotientP1Coordinate_of_leaves' … (hO : CMStabObj)`: pass `hO := GapGlue.cmStabObj_of_textbook hU hG hM`.
   * L119 `quotientP1Coordinate_of_printed` takes p1-quot's leaf `hW : AtkinLehnerFixesCM24` (plus `hQ`, `hAL`
     for `cmStab24_of`, QuotientP1/CMStab.lean L451). Either route drops that leaf:
     (a) replace the proof body by `quotientP1Coordinate_of_printed' hAF hQE hTS hP1 hE hT hYI
     (GapGlue.cmStabObjWeak_of_textbook hU hG hM)` (then `hW`, `hQ`, `hAL` are not needed), or
     (b) keep their proof and pass `hW := GapGlue.atkinLehnerFixesCM24_of hU hG hM` (after
     `HDec.CMStabAL.AtkinLehnerFixesCM24 = HDec.MCRQuot.AtkinLehnerFixesCM24 := rfl`).
   Either way `AtkinLehnerFixesCM24` stops being a leaf: it is a theorem from three fields already in the bundles.
2. **mcr-quot's own composite (`scratch/mcr-quot/MCRQuot.lean`, a scratch file; = `MCRQuotB.lean` on
   wip/p1-quot)**: its theorems with `(hO : CMStabObj)` at MCRQuot.lean L7676 (`cMStabInvolution_of`), L7739, L7870,
   L8522, L8690, L8715 (MCRQuotB.lean L1013, 1076, 1207, 1859, 2027, 2052): pass
   `hO := GapGlue.cmStabObj_of_textbook hU hG hM`.
3. **Constant names.** If p1-quot's modules and mine are imported together, `GapGlue.CMStabObj` vs
   `HDec.MCRQuot.CMStabObj` (and `…Weak`, `…AtkinLehnerFixesCM24`) are distinct constants with the same body;
   bridge each with `rfl` (`example : GapGlue.CMStabObjWeak = HDec.MCRQuot.CMStabObjWeak := rfl`), or `exact`
   the term directly (definitional unfolding closes it). No name clashes: my declarations are in `GapGlue`,
   `GapGlue.CMStab` and `HDec.CMStabAL`; the module `ZInQKernel.Contrib.OneProof.CMStab` differs from p1-quot's
   `ZInQKernel.Contrib.OneProof.QuotientP1.CMStab`.

**Lemmas that may serve st-qbar** (STQM for the same CM orders; I did not work on STQM): `GapGlue.CMStab.lat_model`
(over `ℚ̄`: injective `ρ : End A →+* End_ℂ(ℂ²)` with `ρ(ι a) = act a` and range = the maps preserving the lattice
`qmOrbit (τ,1)`), `com_comm` (`End_𝒪(A)` is commutative), `semilinear_unit` (an `End`-element `g` with
`g ι(α a) = ι(a) g` from a CM element and a normalizing `t ∈ 𝒪`), `exists_g24`, `rep3_eq_αK`, and the residue
calculus of §2-§3 (`residue`, `stab_core`).

## 4. Method

Notation: `𝒪 = LeafQM.O` (maximal order of `B = (2,−3)_ℚ`, so `i² = 2`, `j² = −3`, `(ij)² = 6`), `P = (A, ι, η)` a
level-3 object, `T = twist α ∘ rightMul u`.

* **§1 arithmetic of `𝒪`** (finite checks): coordinates in the `ofInt` basis; reduction `red : 𝒪 → 𝔽₉ = 𝔽₃[i]`
  (`n ↦ (n₀ − n₂, n₁ − n₃)`), multiplicative; involutions `αJ`, `αK` (conjugation by `j`, by `k = ij`), with
  `red ∘ α = conj`; divisibility `y² = −3 ⇒ y ∈ j𝒪`, `y² = −6 ⇒ y ∈ k𝒪` (mod-2/mod-3 finite checks by `decide`).
  `exists_unit_congr` (units of `𝒪` surject onto `(𝒪/3)^×`) copied verbatim from MCRQuot.lean L4578-4747.
* **§2-§3 residues** (`residue`, from T5 `Level3.torsor`): an endomorphism `g` with `g ι(α a) = ι(a) g` acts on the
  level structure by `g(η(α x)) = η(x u₀)`; if `g² = ε ∈ {±1}`, then `α(u₀)u₀ ≡ ε (mod 3)`; choose `u ∈ 𝒪^×` with
  `u ≡ ε u₀` (`exists_unit_congr`); `isoMk` gives `T(P) ≅ P` through `g` (`stab_core`). For every object `Q`, `T²(Q)` has
  level structure `x ↦ η(x α(u) u)` with `α(u)u ≡ ε² α(u₀)u₀ ≡ ε (mod 3)`, so multiplication by `ε ∈ {±1}` is an
  isomorphism `T²(Q) ≅ Q`. This is the involution clause, proved for all classes, not assumed.
* **§4 lattice model** (gt-qm's `qmCentralizerCMC` machinery: `QMLattice.unif_conj` over `ℂ`, transported to `ℚ̄`
  by the bijectivity of `endBC` (T11b, proved in the chain)): `End A` ≅ the `ℂ`-linear maps preserving the lattice
  `𝒪·(τ,1)`. Hence (`semilinear_unit`) for `s ∈ End_𝒪(A)` with `s² = d` and `t ∈ 𝒪` normalizing with
  `t⁻¹ x t = α(x)`, `y² = d ⇒ y ∈ t𝒪`, the map `ι(t)⁻¹ s` lies in `End A`. Cases: `ℤ[i]`: `α = id`, `g = φ`
  (`g² = −1`); `ℤ[ζ₃]`: `α = αJ`, `g = ι(j)⁻¹(2φ − 1)` (`g² = 1`); `ℤ[√−6]`: `α = αK`, `g = ι(k)⁻¹φ` (`g² = −1`).
  `com_comm`: `End_𝒪(A)` is commutative (its elements act on `ℂ²` by scalars, gt-qm's `QMLattice.commutant`).
* **§5 `T ≠ id`** (`nonid_core`, `nonid_t`, `nonid_4`): if `T(m) ≅ m` for `m = rightMul w P`, the composite
  `c = h g⁻¹` lies in `End_𝒪(A)`, has a residue `c₀`, and `α(u)α(w)u₀c₀ ≡ w (mod 3)`. For `ℤ[ζ₃]`, `ℤ[√−6]`
  (`w = 1 + i`): mod `𝔓₃`, `c̄₀ = (1+i)/(1−i) = i`, but `c` commutes with `s = ι(t) g` (`com_comm`), which forces
  `c̄₀ ∈ 𝔽₃`: contradiction (`finA`). For `ℤ[i]` (`w ≡ 1 + j`, `exists_w4`): the equations force `c₀ = 1 + jd` with
  `d̄ = −1` and `d̄ = 0`. So the non-identity clause uses the commutativity of `End_𝒪(A)` rather than an object with
  automorphism group `{±1}`; it is proved, not assumed.
* **§7 Atkin–Lehner** (`rep3_eq_αK`): the chain's `rep 3 = conjO (ui·uj)` is `αK` (both are conjugation by
  `ij = ok`, `uij_val`); `exists_g24` gives `g` with `g² = −1`, `g ι(αK a) = ι(a) g`, i.e. a `QMIso` from
  `q.twist (rep 3)` to `q` with inverse `−g`.

Files: `ZInQKernel/Contrib/OneProof/CMStab.lean`; `scratch/cm-stab/Axioms.lean` + `axioms.txt`,
`Discharges.lean` + `discharges.txt`, `NsCheck.lean` + `nscheck.txt`, `RepCheck.lean` (the scratch test of
`cmStabObj_of_textbook`), `py/coords.py` (coordinate checks), `log.md`.
