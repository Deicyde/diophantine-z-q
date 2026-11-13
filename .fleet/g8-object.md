# g8-object (fleet note)

**Main result.** G8's representation is now a Lean object:
`G8Object.DescData.r : GaloisRep ℓ 2`. It is `ρ_ℓ = β⁻¹ a Tm` restricted to `e₀₀V` in a chosen
basis, built from G7's output (`G0Galois.G7Out`) and `dim = 4` (T26). Its G8 properties are
proved: `intertwines`, and the full `G8Out` (`DescData.g8Out`, via C2 and Burnside).

The G8-G16 interface is restated over the object (`ModObj`, `M.toModData`), and each statement
is proved true of the construction:
- `interface_obj` gives `G12Spec ∧ G14TraceCompat ∧ G15RamG` on `M.toModData`.
- `modularConstituent_tail_obj` gives G13-G16.

**`G15RamG` is proved for the constructed `r_ℓ`** (`g15RamG_obj`), from g15-ram's
`g15RamG_of_localData`. g15-ram's `LocalData p r`, which is on a bare `r`, is replaced by
`LocalDataG p Tm a β`, which is on G7's descent data. `LocalDataG` implies `LocalData` for every
`r` with G8's intertwining (`localData_of_intertwines`, using the scalar transfer
`mat_eq_scalar_of_intertwines`). G11 is proved for any such `r` (`g11_of_intertwines`).

**Check against `GluePieces2` and linked-tate.** The restated field `LinkedTateObj` consists of
g14-trace's `TateBridge35` data plus G15's local data `LocalDataC`; the β-clauses are on
`G7Data`'s own β. The following are proved:
- T7 + `LinkedTateObj` → g0-assemble's field 28 `LinkedTateData`, verbatim copy
  (`linkedTateData_of_obj`);
- → linked-tate's `LinkedTateCore` and `LinkedTateCoreDR`, copied from its commit dae5b706;
- on fibre contexts, the data contain `TateBridge35`'s conclusion.

The local clause implies linked-tate's `RhoRamWild` (`rhoRamWild_of_localDataG`, using g15-ram's
T20/T21, `upperWild` and `wildFixTame`). As a hypothesis it is logically stronger, but its content
is more primitive: the ramification theory is proved. `localDataG_triv` is a weak non-vacuity
check (`LocalDataG` alone, not jointly with `G7Out`).

**Split (part 3).** `TmWild` is split into three pieces:
- `ContainsL`, which is closed: `decomp(G_F) ⊆ G_L` (`decomp_mem_fixing`);
- `OnL`, the `G_L`-clause of the Tate functor on G7's datum, independent of `p`;
- `WildTateTrivial`, a statement about `A/L` alone (R6 + D2).

`LocalDataS` contains no ℓ-adic operator. `LinkedTateObjS` → `LinkedTateObjD` →
`LinkedTateDataD` is proved, where the `D` forms carry the premise `[L:ℚ] ≤ D`.

**Compiles (VERIFIED).** `scratch/g8-object/G8Object.lean` is assembled by `build.sh` from verbatim
copies of g0-mod-field, g14-trace, g15-ram, g0-mod-galois and g0-assemble's 87, plus the new
`part_obj`, `part_link`, `part_split`. `lake env lean` on it exits 0 in about 2 min with 0 errors
and no sorry. All 56 axiom reports are `[propext, Classical.choice, Quot.sound]`. The check is in
one environment, but over kernel imports rather than g0-assemble's `Leaves.lean` copies, so the
identification with `G0Assemble.lean` is by identical text.

**Remains (glue).**
- `TateBridge35` + `OnL`: the Tate functor on G7's descent datum at ℓ = 5, 3.
- `WildTateTrivial`: R6/D2 transported to `LadicCond`'s `G_{ℚ_p}`.
- `BetaUpperC`/`BetaTameC`: T16/D3 on G7Data's β.
- The existence of the local field `F` with `e(F) ≤ (DG₀)!` (resp. tame).

**Finding (review, VERIFIED by reading; repaired).** `G7Data` drops G4's bound `[L:ℚ] ≤ D`.
- Without that bound the split field `LinkedTateObjS` is false: enlarge `L` by `ℚ(ζ_{2^k})`.
  The premise has been added.
- The unrestricted `LinkedTateData`, `LinkedTateCore` and `LinkedTateObj` are not shown false,
  but their truth for every `G7Data` is not established.
- Recommendation: add `[L:ℚ] ≤ D` to `G7Data` (`g7OutUnr_of_g4Out` has it). The `D` forms then
  feed `afterG7_of`.

**Finding (SPECULATIVE).** N5 L848-850 says "the surface has good reduction" at `p > R`, which is
not evident for bad primes `p ∈ T`. The needed conclusion, that wild inertia acts trivially,
holds by potential good reduction of QM surfaces together with Serre–Tate.

Report: `docs/research/g8-object.md`. Log: `scratch/g8-object/log.md`.
