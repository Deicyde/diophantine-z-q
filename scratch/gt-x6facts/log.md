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
