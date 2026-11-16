# weil-used (field `weilPairingMumford`), done

**Proved** in `ZInQKernel/Contrib/OneProof/WeilPairingUsed.lean` (namespace `WeilUsed`, imports `TailZ24`). Every
theorem has axioms `[propext, Classical.choice, Quot.sound]`.
- `weilPairingMumford_of_split (ha : WeilPairingExists) (hb : WeilPairingPerfect) (hc : WeilPairingGalois)
  (hd : WeilPairingCompat) (he : WeilPairingDual) (hf : WeilPairingAlternating) : WeilPairingMumford`.
  The six leaves are t09-pic's L4a-f, copied verbatim. They state the properties of Mumford's genuine `ē_n`
  (`IsMumfordPairing`: values `weilScalar`), one printed property each: existence/bilinear (Mumford §20), perfect (§20),
  Galois (Milne 1986 §16), compatible (§20), adjoint (§20 (5) / Milne 16.2(c)), `e^L(x,x)=1` for ample L (§23).
- `split_of_weilPairingMumford : WeilPairingMumford → (the six leaves)`: no leaf is stronger than the field (via the
  new `constK_injective`).
- `weilPairingPicZero_of_mumford` and `t09SymmIsogenyExists_of_picZero`: the single-leaf restatement
  `T09Pic.WeilPairingPicZero`, which is exactly what the consumer reads.
- `WeilPairingRead` and `weilPairingRead_of_mumford`: the read set below `T09_SymmIsogenyExists`.

**Consumers** (probe over the closure of frozenTarget, `scratch/weil-used/FieldUse.lean`): the only consumer is
`t09SymmIsogenyExists_of_four` (TailZ24:821).
- Clause 6 (the `weilScalar` pin) is unread.
- Clauses 1-5 fill `WeilDual` and `SymmIsogeny`.
- Downstream, `WeilDual.dualEnd` (clause 4) and the right half of `perfect` are never read. Dropping them needs a
  weaker `WeilDual` and a reroute through old generations; that is reported, not done.

**#discharges**: `DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by WeilUsed.weilPairingMumford_of_split`, still
assumes the six leaves, standard axioms (`scratch/weil-used/discharges.txt`).

**Autofold** (`scratch/weil-used/autofold.json`, dry-run only): `strict count: 46/10 on 56 -> 51/10 on 61; strictest
45/11 -> 51/10`. The strict GLUE count is unchanged, the strictest GLUE count goes down by 1, and the bundle gains 5
fields. The dry-run module compiles.

**Remains / caveats**
- The strictest gain holds only if L4a counts as one printed statement. Its values are read on the Lean `Pic⁰` through
  Kleiman 9.2.5 and Mumford §8 (iv); I flagged this as a note. If a reviewer reads it as composite, the split gains
  nothing; keep the single leaf, or use the manual bypass fold to `WeilPairingPicZero` written in the report.
- All locators are UNVERIFIED.
- L4e is inert downstream.

Report: `docs/research/weil-used.md`.
