# gz-conj results log

Target: `ZInQ.GZHL3.GrossConjugationCd` (ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean),
i.e. `GrossConjugationAt (shortCurve (-(d:ℚ)^2))` for d ≡ 5 (mod 8) squarefree
(statement in ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean §2).

## Setup
- merged wip/gz-weil ad22e947 (VERIFIED: git merge, no conflicts).
- build: copied gz-weil .lake/build (reflink) and lean/.lake/build; `lake build` of Heegner, Cd, ALBasic,
  Level, FHNonvanishing.FE, HeckeAll.Provider: success (VERIFIED).

## Plan (proof outline)
1. rootNumber f = -1 for the newform of C_d: Tau Ceti FE (`completedL_newform_sub`) vs proved
   FunctionalEquation5 at level N = 32 d^2 (`level_eq_of_coeff_cd`), L(f,s) not identically 0. Kills clause eps=+1.
2. eps = -1 means frickeSign = +1: f(-1/(Nz)) = N z^2 f(z), so eichler f ∘ W_N - eichler f has derivative 0,
   value 0 at the fixed point i/sqrt N.
3. coefficients real: conj(eichler f τ) = eichler f (-conj τ) = eichler f (W_N ψ τ) = eichler f (ψ τ), ψ τ = 1/(N conj τ).
4. lattice uniqueness: g2,g3 determine the lattice (local ODE argument + identity theorem + poles), so
   conj L = L for a period lattice of E/ℚ; hence conj(weierPt z) = weierPt(conj z).
5. ψ τ_Q = τ_{Q*}, Q* = [N C, B, A/N] (residue β, same D); Q ↦ Q* permutes Γ0(N)-classes; so conj fixes heegnerC.
6. ι∘σ = conj∘ι; map ι injective ⇒ σ y = y.

## Compile results
- Lattice.lean: `lattice_eq_of_g` (g2, g3 determine the lattice, any PeriodPair), `conjPP`, `G_conjPP`,
  `conj_mem_iff_of_isPeriodLattice`, `weierstrassP_conj`, `map_conj_weierPt`: compiles, no sorry (VERIFIED).
- Fricke.lean: `fricke_apply` (f(-1/(Nz)) = ε N z² f(z)), `eichler_fricke` (ε=+1 ⇒ φ_f∘W_N = φ_f),
  `conj_eichler`, `conj_eichler_psi` (conj φ_f(τ) = φ_f(1/(N τ̄))): compiles (VERIFIED).
- Main.lean (all parts + `rootNumber_cd`, `iota_comp_sigma`, `map_conj_heegnerC`, `conj_clause`,
  `grossConjugationCd : ZInQ.GZHL3.GrossConjugationCd`): compiles; `#print axioms` for
  grossConjugationCd, conj_clause, lattice_eq_of_g: [propext, Classical.choice, Quot.sound] (VERIFIED).
- Contributor file ZInQKernel/Contrib/OneProof/GrossConjugationCd.lean: `lake build` success (VERIFIED).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: success, 13667 jobs (VERIFIED).
- MainEdit.lean (frozenTarget with hL3 → HeegnerPointRationalCd + GrossZagierFormulaCd, and → X0ModuliGaloisMero +
  GrossZagierFormulaCd): compiles, standard axioms (out_mainedit.txt) (VERIFIED).
- Discharges.lean: 61 open hypotheses, 2958 theorems, 8 discharge one; no GZConj line (GrossConjugationCd is not
  an open field at 60a3fac7; hL3 must first be replaced by the C_d chain) (VERIFIED).
