# gt-x6facts results log

Base a454ad64 (leaf-fold16, top TailZ26). Build copied from ~/dzq-wt/gt-qm (same base).

## Statements (verbatim in TailZ22, copied in scratch/gt-x6facts/Statements.lean)
* `HDec.QMSplit.Moduli.BabaGranathRationalAb` (TailZ22 L91)
* `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (TailZ22 L64)

## Results
* 2026-11-14 22:47 VERIFIED (compiled, `lake env lean`, 1m38s, axioms [propext, Classical.choice, Quot.sound]):
  `HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_of_elkies (hE : ElkiesEquationsX6Ab) (hC : QMPairsCMExist) :
  BabaGranathRationalAb` in ZInQKernel/Contrib/OneProof/X6Facts.lean. `QMPairsCMExist` = existence over ℚ̄ of
  QM pairs with HasCM4 / HasCM3 / HasCM24 (new witness-free leaf). Witness: Elkies' (Y,Φ,X,Ψ,fY,t),
  t₄ = 1, t₃ = ∞, t₂₄ = 0.
* 22:50 VERIFIED (compiled): `QMPairsCMExistC` (ℂ form) + bundle `shimuraTaniyamaQbar` (+ chain T11b
  `AVB2.t11b_of_exists t11bExists_lf8`) ⇒ `QMPairsCMExist` (`qmPairsCMExist_of_C`, `descend_pair`, `map_mem_com`);
  `babaGranathRationalAb_of_printed`.
* 22:52 VERIFIED: `lake build +Main +Discharges +X6Facts` OK (build tree copied from gt-qm, 16 s);
  `#discharges`: babaGranathRationalAb discharged by `_of_elkies` (assumes Elkies, QMPairsCMExist) and `_of_printed`
  (assumes Elkies, ShimuraTaniyamaQbar, QMPairsCMExistC); standard axioms. Output: discharges.txt.
* 22:53 VERIFIED: autofold `--dry-run` of autofold-spec.json: strict count 47/14 on 61 unchanged; generated module
  FoldDryRun.lean compiles (sixContactMin_of_open21 standard axioms).
* 22:54 VERIFIED (compiled): `qmPairsCMExist_of_babaGranath` (BG ⇒ QMPairsCMExist via ShimuraSplit.surj_of_fibre),
  `babaGranathRationalAb_iff` (under Elkies), `cmExists_iff`.
* 22:55 VERIFIED (computed, cm_check.py, PARI): h(-4)=h(-3)=1, h(-24)=2; b = 1, 1, 0; GR predicts degree 2 for all
  three; Elkies conic fibres over t = 1, ∞, 0 are 2 points each with residue fields Q(i), Q(√-3), Q(√-3);
  Q(√-3) ⊉ Q(√-6); j = 16(t-1)/27 maps (1, 0, ∞) to (0, -16/27, ∞).
* GonzalezRotgerX6Ab: not reduced (used for arbitrary CM orders by NoCM FibreComTrivial; no bundle field implies it).
