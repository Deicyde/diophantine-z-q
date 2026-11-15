# cm-stab results log

Base: wip/cm-stab = 3782dac8e (leaf-fold18). Target: `CMStabObj` (scratch/mcr-quot/MCRQuot.lean L7648).

## Statements / findings
- VERIFIED (read): CMStabObj at MCRQuot.lean L7648-7653; QML3/M3/twist/rightMul in ZInQKernel/HDecomp/QM/Structures.lean;
  HasCM4/3/24, com in ZInQKernel/HDecomp/QM/Pairs.lean; exists_unit_congr MCRQuot.lean L4686.
- VERIFIED (read): QMLattice.unif_conj gives over ℂ an injective ρ : End A →+* End_ℂ(ℂ²), ρ(ι a) = act a, range = maps
  preserving qmOrbit (τ,1); yuB6Emb_of shows the transport from k ⊂ ℂ (endBC bijective by T11b, proved in chain).
- VERIFIED (python, scratch/cm-stab/py/coords.py): conj by j on B is (re,-imI,imJ,-imK), i.e. ofInt n ↦ ofInt(n0,-n1,n2,-n3);
  conj by k=ij is (re,-imI,-imJ,imK). red(ofInt n) = (n0-n2, n1-n3) mod 3 is multiplicative into F9=F3[i] (all 81^2 pairs);
  red∘α_j = red∘α_k = conj. y*y ≡ 0 mod 3 ⇒ j*y ≡ 0 and k*y ≡ 0 mod 3; y*y ≡ 0 mod 2 ⇒ k*y ≡ 0 mod 2.

## Plan (math)
- CM4: α=id, g=φ (g²=-1). CM3: α=conj j, g=ι(j)⁻¹(2φ-1) (g²=1). CM24: α=conj k, g=ι(k)⁻¹φ (g²=-1).
  g exists in End A via the lattice model (j⁻¹·x·y ∈ O for y²=-3, k⁻¹·x·y ∈ O for y²=-6).
- residue u₀: g(η(α x)) = η(x u₀); α(u₀)u₀ ≡ ε; u ∈ O^× with u ≡ εu₀ ⇒ T P ≅ P, T² = rightMul(≡ε) = id on classes.
- T ≠ id: m = rightMul w P, w=1+i (CM3/24) or w ≡ 1+j (CM4); iso h ⇒ c = h g⁻¹ ∈ com commutes with s ⇒ F9 contradiction.

## Compile log
- lake build ZInQKernel.Contrib.OneProof.QMLattice: OK (already built, 14 s).
- CMStab.lean §1-§5 (arith mod 3, involutions αJ/αK, residues, isoMk, stab_core, lat_model, com_comm,
  semilinear_unit, nonid_core, nonid_t): `lake env lean` exit 0, ~16 s, no sorry (VERIFIED, 03:28→~05:30 run).

## Run 2 (base 6242b2f91 = 9a100aa7 leaf-fold22b merged)
- `lake build ZInQKernel.Contrib.OneProof.CMStab` on the merged base: OK (21 s). VERIFIED.
- `#print axioms GapGlue.cmStabObj_of`: [propext, Classical.choice, Quot.sound]; no sorry/axiom/admit in CMStab.lean. VERIFIED.
- Added `GapGlue.CMStabObjWeak` (verbatim copy of FixedDisjoint.lean L540-546, wip/p1-quot f30ece89; same text at 3ce73273)
  and `GapGlue.cmStabObjWeak_of` (hU hG hM hT): build OK, axioms [propext, Classical.choice, Quot.sound]. VERIFIED
  (scratch/cm-stab/axioms.txt).
- CMStabObj text: MCRQuot.lean L7639-7653 = MCRQuotB.lean L976-990 (wip/p1-quot 3ce73273, the def FixedDisjoint.lean
  uses through its import of MCRQuotB) = CMStab.lean L1145-1159 (md5/diff identical). VERIFIED.
- Namespace check (scratch/cm-stab/NsCheck.lean, nscheck.txt): p1-quot's CMStabObjWeak text elaborated inside
  `namespace HDec.MCRQuot` with their opens gives the same term as GapGlue.CMStabObjWeak (pp.fullNames print; `rfl`). VERIFIED.
- Added `rep3_eq_αK` (chain's `HDec.LeafQM.AV.Pin.Exact.rep 3` = αK, both conjugation by ij = ok), `exists_g24`, and
  `GapGlue.atkinLehnerFixesCM24_of (hU hG hM) : HDec.CMStabAL.AtkinLehnerFixesCM24` (verbatim copy of p1-quot's leaf
  `AtkinLehnerFixesCM24`, QuotientP1/CMStab.lean L435-446 at d984b2547). Build OK; axioms standard. VERIFIED.
  So p1-quot's leaf AtkinLehnerFixesCM24 is a theorem from the textbook fields (pitfall: `mul_assoc` resolves to
  MonObj.mul_assoc under `open MonObj`; use `_root_.mul_assoc`).
- #discharges (scratch/cm-stab/discharges.txt): 63 open hypotheses, 5 discharged, none by CMStab (expected: CMStabObj
  is not a bundle field). VERIFIED.
