# el-e4 log

## Definitions
- E4 (el-gadget) = M1 (el-cert), same normalization: Theta0 = Tr W0^{-1}, W0 = prod_j (1 + R0 C_j^2),
  B = R0 a^2 / Theta0^2, a = 1 - R0 q^2. theta = 1 witness (rs-pole 2.2(2)): e = A = mB, z = B c,
  c^2 = m(m - B) gives polePoly = 0 (from Hypotheses/Pole.lean: r1 = 0, Az^2 = eH since H = m B^2 (m - B)).
- Completeness curve: C_m : h^2 = m(m Theta0^2 - R0 (1 - R0 q^2)^2), m in multiplier set
  (Lean: signed divisors of 2730, 64 values; L7: m0 k^2, m0 | prod_{p<=324} p signed, k bit-integer).

## Step 1. locsol.py (p-adic local solubility of y^2 = quartic, recursive Hensel on residue discs)
- t0_locsol_check.py: 30/30 agree with el-cert's local obstruction lemma (p in 11..43, random R0, m, Theta0
  with v_p = 1,2); 5/5 curves with a q=0 point found soluble at 2,3,5,7,11,13. VERIFIED.
