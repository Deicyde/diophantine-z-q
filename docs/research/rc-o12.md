`O12.inputs_of_theta` supplies both halves of `GaloisConstituentModel.Inputs` from the named data below, on the model's coefficientwise reduced expansions. It proves the character conditions on the local pair, (O.12) on the characteristic-zero sum containing the actual form, its integral evaluation, and the fresh and omission readings. The result passes directly to `X.o12_of_constituents` and `X.fixedU_of_constituents`, together with the same type-character comparison. The theta forms and their local constituent data remain inputs.

## Statements

Below, $V=U\setminus\{p\}$, $U$ is good, and its cardinality plus one is at most $B$. Write `a_n(U,h)` for the residue of the n-th coefficient of `t(h) F_U`, and `e_U(h)` for `X.readE U (X.tE h (X.FE U))`.

| Lean theorem | Statement and use |
| --- | --- |
| `localPair_exists` | At a good $p$, there is a maximal ideal over $p$, an inertia element $\tau$ there with $\chi_p(\tau)=-1$, and an arithmetic Frobenius lift $\phi$ at that same ideal. Step 1. |
| `localPair_characters` | $\chi_{\rm type}(\tau)=1$, the bits of $\tau$ away from $p$ in $U$ are zero and its $p$-bit is one; $\chi_{\rm type}(\phi)=\operatorname{typ}(p)$ in additive labels and the bits of $\phi$ there are $\operatorname{legBit}(p,s)$. Step 1. |
| `upDifference_supported` | $(t(g\tau\phi)-t(g\phi))F_U$ vanishes outside the active ramified blocks. Step 2. |
| `o12_charZero` | $U_p^{(2)}(t(g\tau\phi)-t(g\phi))F_U=d(\phi)(t(g\tau)-t(g))F_U$ as vectors over the coefficient field. Step 2. |
| `whittaker_sum` | With invariance under the upper unipotents $n(nb)$, the finite double-coset sum evaluated at $a(n)$ equals $pW(a(np))$. Fourier part of steps 1 and 3. |
| `goodHecke_of_data` | Outside the ambient `avoid` set, `GoodOperators` and `DeterminantFourierData` give the good Hecke formula and identify its operator with scalar trace on $F_U$. Steps 4–5. |
| `trace_coeff_of_not_dvd` | If $q\nmid n$, the integral coefficient of $t(\operatorname{Fr}_q)F_U$ at $n$ equals $F_U[qn]$. Steps 4–5. |
| `orbitCoeff_eq`, `read_orbit` | $a_n(U,h)$ is the reduction of the integral trace coefficient, and $e_U(h)$ decodes $a_1(U,h)$. Steps 3–5. |
| `o12_integral` | The integral coefficient at $p$ of the left trace difference equals the integral coefficient at one of $d(\phi)$ applied to the right trace difference. Step 3. |
| `o12_reduced` | $a_p(U,g\tau\phi)-a_p(U,g\phi)=a_1(U,g\tau)-a_1(U,g)$. Step 3. |
| `eta_residue` | The phase $\eta(p)$ maps to one in the residue field. Step 5. |
| `fresh_normalized`, `fresh_residue` | At fresh $q$, $H_U[q]\equiv 2^{-n_U-1}a(uq)\pmod{2\mathcal O_{\rm coef}}$ with an integral normalized coefficient, and $a_1(U,\operatorname{Fr}_q)=\overline{H_U[q]}$. Step 4. |
| `coefficientOne` | `R (insert q U) = X.readE U (X.tE (X.frob q) (X.FE U))`. First half of `Inputs`. |
| `omission_at_p` | For fresh $r$, with $\kappa=(\psi/\eta)(p)(-vr/p)\in\{1,-1\}$, decoding $a_p(U,\operatorname{Fr}_r)$ gives $\overline{C_p(vr)}e_V(\operatorname{Fr}_r)$. Step 5. |
| `representative_trace`, `representative_bit` | For $\operatorname{Fr}_r=jxj^{-1}n$ with $n\in N_U$, reduced traces agree on every subset of $U$ and the $p$-bit agrees for $p\in U$. Step 5. |
| `omissionSign_flip` | Opposite bits at $p$ of two fresh primes give opposite signed Legendre values, with the same $v$ and character ratio. Step 5. |
| `o12_at_one` | With the characters above and $\kappa_0=(\psi/\eta)(p)(-vr_0/p)$, the identity is $\overline{C_p(-\kappa_0)}e_V(g\tau\phi)-\overline{C_p(\kappa_0)}e_V(g\phi)=e_U(g\tau)-e_U(g)$, writing (C_p(\kappa)=(a_p-\kappa-1)/2) in this row. Second half of `Inputs`. |
| `inputs_of_theta` | Given the theta and local data and `IsTypeChar T chiType`, `X.Inputs`. Step 6. |

Private helpers (formal bookkeeping, provenance (c)): `residue_two` says (2) reduces to zero; `residue_eq_of_two_dvd` reduces an integer-two congruence; `no_div_of_fresh` gives $s\nmid q$ for $s\in U$; `even_ap` proves (a_p) even from the source congruence and oddness of $p$; `decode_int_mul` commutes with integer multiplication; `scale_erase` gives $2\cdot 2^{-n_U-1}=2^{-n_V-1}$. These supply bookkeeping for steps 3–5.

## Named hypotheses

| Data | Kind and manuscript anchor |
| --- | --- |
| `FourierData.index`, `coeff`, `expand_coeff`, `integral_inclusion`; characteristic zero of (K) | Definition of the theta data: consistent positive integral and characteristic-zero Fourier coordinates and the coefficient DVR in its field (tex 9638–9668, 9891–9901). `X.coefK` and `X.expand_spec` are from the existing model. |
| `FourierData.decode`, `decode_one`, `read_at_one`; `ThetaData.residue_maximal` | Definition of the coefficient-one reading. The values used by the manuscript are in the prime subfield (tex 9688–9698). Encoding evaluation by a common additive extension from the prime subfield is on-the-spot (c); only its values on (0,1) affect the final readings. |
| `ThetaData.δ`, `truncation`, `admissible`, `a`, `η`, `source` | Definition of the common actual source at the chosen stage, with the existing `Odd.SourceHyp` of (O.9)–(O.11), tex 9450–9455, 9471–9489, 9570–9636, 9670–9679. |
| `ThetaData.ratio`, `ratio_sign`, `signed_recur`, `eta_phase` | Definition of the actual $\psi/\eta$ sign in the recurrence and the two-power phase (tex 8424–8426, 9585–9589, 9696–9698, 9908). `SourceHyp` supplies existence of a recurrence sign; the named recurrence identifies it with the sign used in (C_p). |
| `ThetaData.H`, `theta_mod_two` | Definition/comparison from (F_U=\theta H_U), using $\theta=1+2\sum_{m>0}q^{m^2}$ (tex 9647–9648, 9672, 9689). |
| `ThetaData.H_off_unary` | Definition of the off-unary coefficients after the same integral division in (O.11) at the chosen precision. Supplies an integral witness for the normalized undivided coefficient and an integer-two error, also allowing zero error (tex 9486–9498, 9614–9636, 9699–9704, 9913–9918). It does not supply the two values of `TL`; the proof computes those using `TL_fresh` and `TL_omission`. |
| `ThetaData.source_symbol` | Definition of (R) as the prime-subfield residue of the normalized source at the tested squarefree products, including zero off support (tex 9675–9680, 9694–9704). |
| `ThetaData.good_hecke` (`FormwiseHecke`) | Definition/comparison of the existing good Hecke formula with trace on the individual form, outside its added primes (tex 9660–9668, 9670–9674, 9714–9717, 9795–9796). Uses the coefficient and lattice types of `buildConstituentModel`. The base constructor's `D U` supplies this formula at the primes in its domain by `goodHecke_of_data`. |
| `LocalBlocks.active`, `ramified`, `Up`, `supported`, `preserves_ramified`, `old` | Definition of the characteristic-zero direct sum and its local action (tex 9754–9769, 9885–9889). Old summands are degeneracies of forms of level prime to $p$; their Galois action at inertia is unramified by the unramified case of the same compatibility already used for `ρ`. Preserving the ramified coordinate subspace is the only multiplicity-space invariance used; no condition of diagonalizability or scalar action is imposed on old multiplicities. Coordinate support is on-the-spot (c). |
| `LocalBlocks.newLine` | PRINT in the form used for cuspidal blocks: Casselman, Theorem 1, pp. 302–306, Corollary p. 306 and Theorem 4, p. 313, at primitive quadratic conductor one, and Carayol, §§0.3–0.7, Théorème A, pp. 409–411, for the character lines with the manuscript's two duals (tex 9773–9861, 9866–9873). The resulting two matrices in a common basis are $\operatorname{diag}(1,-1)$ and $\operatorname{diag}(\lambda,\mu)$, with (U_p^{(2)}=\lambda) on that block. The field includes the parallel Eisenstein calculation as data of the character pair and divisor-sum expansion (tex 9862–9864); the cuspidal print does not apply to it. The existing `GaloisConstituentModel.ρ` is used without duplicating the existence print. |
| `UpAtOne`, `LocalInput` | Definition/comparison of the weight-two (U_p^{(2)}) on these same vectors with the shift from coefficient $p$ to coefficient one (tex 9841–9856). `whittaker_sum` proves the finite matrix and sum calculation; identification with the actual Fourier coefficients is supplied by `UpAtOne`. `LocalInput` packages this comparison with the local blocks. |
| `IsTypeChar` | Existing comparison of the stationary type character with the types of arithmetic Frobenius (tex 2017–2020, 9932–9944). No extra type or bit conditions are assumed on either local element. |

## Known issues

- The shared constructor's `UnramifiedConstituents T avoid ρ` tests every constituent simultaneously. The manuscript's good Hecke test at a prime outside $U$ is on the form at $U$. One cannot assume all good primes avoid `avoid` and use that constructor to model ramification at the added primes. This is a gap in the base interface for actual forms (tex 9660–9668, 9670–9674, 9754–9769). The result uses the permitted formulation on any constituent model carrying the typed comparisons, with formwise Hecke on the individual form. The smallest additional input for a specialization to the current constructor is the good Hecke comparison on $F_U$ at good (q\notin U) excluded from the ambient Hecke domain. Construction of the common model (including the diamond and two-fresh inputs) remains with its own lane.
- The Casselman and Carayol locators above are transcribed from the manuscript; the exact print passages and normalization were not independently verified on this run. Existing transcriptions of the conductor consequence do not state the simultaneous character-line and bad-prime Fourier comparison. As already described in `docs/research/r17-rebase.md`, the conductor equality is a consequence of the local correspondence and Casselman, not the statement of Carayol's Théorème A.
- The historical `CoefficientDictionary.TraceModel` is deprecated because its Frobenius condition is exact conjugacy in the whole group. This proof uses `GaloisConstituentModel.N`, with representatives modulo the joint finite subgroup, and the existing corrected `GaloisTraceModel` consumers.
- No manuscript error was identified in the checked arithmetic. The formal result does not build the actual modular forms, prove the print-based local description, or identify the absolute module quotient with the module of reduced Fourier expansions.

## Manuscript check

- Tex 9450–9455, 9471–9489 — OK: the two readings use one common stage, with the fixed support excluded from good primes and only matching parity used.
- Tex 9614–9636 — OK: the odd-stage precision after both divisions is an integer-two error on the chosen range; the proof takes the defining off-unary coefficient comparison as data.
- Tex 9638–9668 — OK: coefficientwise reduction, Fourier comparison and integral stability suffice; no saturation, integral projector or proof of stability is inserted into this lane.
- Tex 9670–9687 — OK: the fresh index is off unary support, and the (V_p) terms vanish by `TL_fresh`.
- Tex 9688–9704 — OK: the diamond term at index one vanishes and the same normalized coefficient gives the valuation symbol, including the off-support interpretation.
- Tex 9712–9729 — OK: only the existing reduced `det_orbit` is used; the diamond calculation stays outside this lane.
- Tex 9754–9769 — OK: the old blocks and multiplicity spaces are retained, using the common characteristic-zero trace and determinant operators.
- Tex 9773–9811 — unverified: the stated local-global normalization and printed conductor-one classification enter through the local input.
- Tex 9813–9841 — unverified: the weighted newvector double-coset normalization is used in the local input; the actual newvector action is not formalized separately.
- Tex 9842–9856 — gap filled: the matrix identity gives the finite Whittaker sum with the stated translation invariance; `UpAtOne` names the remaining identification with the true Fourier coefficients.
- Tex 9857–9864 — unverified: the scalar on the conductor-one block with multiplicities and the Eisenstein divisor-sum comparison enter as described above.
- Tex 9866–9873 — OK: the existing absolute-inertia and Frobenius facts give a pair at one prime above $p$, with all five character conditions; the local matrices are the stated input.
- Tex 9874–9892 — OK: (O.12) holds on the characteristic-zero sum, and the zero old contribution needs no semisimplicity.
- Tex 9893–9902 — OK: integral evaluation uses the two lattice stability fields, injective coefficient inclusion, and `det_orbit` after reduction; there is no cancellation of two in (O.12).
- Tex 9905–9918 — OK: `TL_omission`, (n_U=n_V+1), the evenness of (a_p), and the phase reduction give the coefficient at (pr).
- Tex 9919–9925 — OK: quotient representatives retain both forms' reduced trace orbits and flip the $p$-th Legendre sign. Equality of the ultimate omitted symbols and the odd sum of the two (C_p)'s are downstream.
- Tex 9926–9945 — OK: the existing `o12_of_constituents` exports the product-label reading, and `Rules.symb_contraction` uses `cp_sum_odd` and `omission_rule` to finish the dictionary rule.

## Verification

All four modules (`Local.lean`, `Fourier.lean`, `Theta.lean`, `Inputs.lean`) compile with `lake env lean -j1` on the pinned toolchain, one compiler invocation at a time. The files print the axioms of all 27 theorems, including private helpers; each reports only `propext`, `Classical.choice`, and `Quot.sound`.
