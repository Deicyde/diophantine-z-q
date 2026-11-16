# weil-used results log

Base: 43513d873 (leaf-fold25). Field: `HDec.HSyn.OpenAddedLeaves17.weilPairingMumford : T09Pic.WeilPairingMumford`
(def at ZInQKernel/OneProof/H/TailZ24.lean:708; bundle field TailZ34.lean:150).

## Setup
- lean/.lake copied from ~/dzq-wt/hx-used (same lean/ZInQ commit f7475aed) — fixes "unknown module prefix 'ZInQ'".

## Step 1: consumers (VERIFIED, read + compiled probe)
- Field passes unchanged through the bundle maps TailZ34:169, TailZ31:66, TailZ30:70, TailZ26:190 down to
  `addedLeaves12_of_open13` (TailZ24:821), its only consumer: `T09Pic.t09SymmIsogenyExists_of_four`
  -> `t09SymmIsogenyExists_of_mumford` -> `weilPairingPicZeroPrinted_of_mumford` (TailZ24:730, discards clause 6, the
  `weilScalar` pin, with `-`) -> `weilPairingPicZero_of_printed` (clause 4 to existential fv, clause 5 to very ample L)
  -> `t09SymmIsogenyExists_of_leaves` (TailZ24:520ff), which builds `WeilDual.mk` / `SymmIsogeny.mk` from clauses 1-5.
- Probe scratch/weil-used/FieldUse.lean (closure of `ZInQ.OneProof.frozenTarget`, 244312 constants; every constant whose
  value mentions a projection / recursor / `.proj` of `WeilDual`, `SymmIsogeny`, `Polarization`). Output FieldUse_out.txt.
  Compiled, 3m34s.
  - `WeilDual.dualEnd`: no reader in the closure (only producer `WeilDual.mk` in t09SymmIsogenyExists_of_leaves).
  - `WeilDual.perfect`: one reader, `WeilPairing.weil_nondeg`, which uses `.1` (left kernel) only (TailB.lean:3704).
  - `WeilDual.galois`: `weil_galois` (-> wv_galois, tatePairing_galois, oldT9_of_symmIsogeny).
  - `WeilDual.compat`: `wv_compat`, `oldT9_of_symmIsogeny`.
  - `SymmIsogeny.symm`, `.isogeny`, `.lam`, `.D`: `tatePairingZl_of_leaves4` (TailK:250), `oldT9_of_symmIsogeny` (TailB:3856).
  - no `casesOn`/`rec` destructuring of either structure in the closure; `Polarization` absent.
- Hence: clause 6 (weilScalar values) unread; clause 4 (adjoint) and the right half of clause 1 (perfect) are read only
  to fill structure fields that no consumer reads (inert downstream); clauses 2, 3, 5 and perfect.1 are read.
