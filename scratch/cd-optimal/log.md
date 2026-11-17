# cd-optimal log

Task: prove `ZInQ.GZOptimal.CdOptimal` (ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean) or reduce it.
Base wip/gz-optimal 2631cd0b. Build tree copied from the gz-optimal worktree (.lake/build, lean/.lake/build).

## Numerics (py/)

* `py/lev32.gp`, `py/lev32b.gp` (output `py/lev32b_out.txt`, 3888 rows, all (a, c), c = 32k, k <= 24,
  1 <= a <= c, gcd(a,c) = 1, max rounding error 1e-18): rho(gamma) = Phi_1(gamma tau) - Phi_1(tau) for
  gamma in Gamma0(32), in the basis (w1, w2) = E.omega of C_1 : y^2 = x^3 - x (w1 = Omega real, w2 = -i Omega).
  VERIFIED (computed): every coordinate is in (1/2)Z with x + y in Z, both kinds occur:
  Lambda_{f_1} = ((1+i)/2) L_1 (rhombic; X0(32) = 32a1, C_1 = 32a2).
* `py/analyze.py`: VERIFIED (computed, same sample): rho(gamma) in L_1 iff a = +-1 mod 8 (a = gamma_00), i.e.
  rho mod L_1 is the congruence character chi_8(d) (d = gamma_11, ad = 1 mod 8). The other two characters of
  Lambda_1/2Lambda_1 (restricted to d = +-1 mod 8: rho mod (1+i)L_1) do NOT depend on (a mod 256, c mod 512):
  non-congruence (as expected: unramified double covers of a genus-1 curve).
* `py/sroot.gp`, `py/sfit.gp`, `py/x1fit.gp`: with x = 2 + eta(2)^2eta(16)/(eta(4)eta(32)^2) (x0-32 model of
  32a1), s := sqrt(x^2+4) = eta(8)^5/(eta(4)^2 eta(16) eta(32)^2) (VERIFIED to q^20), and
  x1 := (x+s)/2 = q^-2 prod (1-q^m)^{e_m}, e_m = -1 (m = 4,28 mod 32), +1 (m = 12,20 mod 32): the reciprocal
  of the Goellnitz-Gordon (octic) continued fraction at q^4 -- a generalized eta quotient. x1 - 1/x1 = x.
  Identity: s = -y/w with w := eta(16)^3/(eta(8)eta(32)^2), w^2 = x (monomial identity from x = eta16^6/(eta8^2 eta32^4)).
  w has character (2/d) on Gamma0(32) by Gordon-Hughes/Newman (prod delta^r = 2^-1); all exponent sums OK.
* Unif.lean: general gz-weil uniformization (local_eq_gen, global_eq_gen, period_mem_gen) and lattice uniqueness lattice_eq_of_g₂_g₃ — compiled, no errors (VERIFIED).
* py/wchar.gp: w(gamma tau)/w(tau) = (2/d) for 602 gamma in Gamma0(32) (c <= 384, a <= 60, both signs): VERIFIED (computed), 0 failures.
* Structure.lean: lattice_eq_of_periods (Lambda_d <= L and some period not in (1+i)L => L = c0 Lambda_d, c0 in Q) compiled, axioms standard (Check0.lean).
* Level32.lean: period_mem_C1 (EtaW32Character => periods of Phi_1 over gamma in Gamma0(32), chi_8(gamma_11)=1, lie in every lattice of C_1) compiled.
* Level32.lean: LamCd_le_of_etaW32 (EtaW32Character => Lambda_d ⊆ L for every period lattice L of C_d, d = 1 mod 4 squarefree > 1) compiled. Sharpens gz-weil's 2 Lambda ⊆ L.
* CdOptimal.lean: cdOptimal_of (EtaW32Character, CdTwistedPeriodOdd => CdOptimal), periodLattice_le_of_etaW32,
  grossZagierFormulaCd_of_cdLeaves; Check.lean: 9 theorems, standard axioms (VERIFIED).
* Eta leaf restated for v = eta8 eta32^2/eta16^3 (s = 2 integral, as in Ono Thm 1.64); w = 1/v.
* MainEdit.lean: frozenTarget_cdoptimal, standard axioms (VERIFIED). Discharges.lean: 61 open, 3123 theorems, 9 discharge
  one, no CdOpt line (hL3 is top-level all-E, as for gz-optimal) (VERIFIED).
* Target.lean: verbatim copy of CdOptimal, rfl against the original; cdOptimal_target standard axioms (VERIFIED).
* py/twn_mod2.gp: mod-2 level-32 criterion (sum_{e|d} rho(A/(32d^2/e^2)) not in (1+i)L_1) found an odd A for every
  squarefree d = 5 mod 8 tested (output py/twn_mod2_out.txt) (VERIFIED, computed; relies on the derived reduction).
* py/twn_mod2_out.txt complete: all 32 squarefree d = 5 mod 8, 5 <= d <= 301, have an odd A <= 23 (VERIFIED computed). py/twn_table_out.txt: parity table, primes p <= 109, A <= 31; every row has a 1.
