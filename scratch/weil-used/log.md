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

## Step 2: contributor file (VERIFIED, compiled)
- ZInQKernel/Contrib/OneProof/WeilPairingUsed.lean (namespace WeilUsed, imports TailZ24), builds in 21 s.
- Split L4a-f copied verbatim from scratch/t09-pic/Pic.lean:751-811. `weilPairingMumford_of_split` (split -> field);
  `constK_injective`, `isMumfordPairing_eq`, `split_of_weilPairingMumford` (field -> each split leaf: never stronger).
- `weilPairingPicZero_of_mumford`, `t09SymmIsogenyExists_of_picZero` (single-leaf restatement = what the consumer reads).
- `WeilPairingRead` + implications (read set below T09_SymmIsogenyExists; not folded).
- All six main theorems: axioms [propext, Classical.choice, Quot.sound].

## Step 3: checks (VERIFIED)
- #discharges: `DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by WeilUsed.weilPairingMumford_of_split`, still assumes
  the six leaves; standard axioms. scratch/weil-used/discharges.txt.
- autofold dry-run: `strict count: 46/10 on 56 -> 51/10 on 61; strictest 45/11 -> 51/10` (strict GLUE unchanged,
  strictest GLUE -1, +5 fields). Printed module compiles (`sixContactMin_of_open30` standard axioms).

## Ratings (locators UNVERIFIED throughout)
- L4a printed with bridging note (Kleiman 9.2.5, Mumford 8 (iv)); if read as composite the strictest gain vanishes.
- L4b, L4d Mumford 20; L4c Milne 1986 16 (weakest locator); L4e Mumford 20 (5)/Milne 16.2(c), inert downstream;
  L4f Mumford 23 (consequence: ample L).
