# cm-numeric (2026-11-13)

**Result.** TYZ's class-7 base CM point is now pinned, and every check of the CM leaves passes
numerically. Every genus point is now a Lean definition, and cm-points' bundled `GenusPointLeafCM`
is split into closed leaves about these pinned objects.

* **Class-7 point** (TYZ L1196, L1203–1205): `z_n` is the Heegner point of `[(n+δ²)/4, δ, 1]` on
  X₀(32) = A, with δ² ≡ −n (mod 128). Computed for 8 values of n: the point lies on A, depends only
  on δ mod 64, and generates exactly the Hilbert class field H_n.
* **Lemma 3.21(4)** holds for the pinned `Z(e)` in all 12 cases tested.
* **Lemma 3.21(1)** holds for class 5 in all 30 cases.
* **`ShimuraReciprocity`:** Frobenius at 𝔭 acts as multiplication by 𝔭̄, as stated. This held in
  26/26 cases; the opposite direction fails in all 24 cases where [𝔭] has order > 2.
* **`TYZSigmaFixesZn`** holds numerically in 15 cases. Sharper form, which is not printed in TYZ:
  σ_{1+2ϖ} maps f₀(P_n) to f₀(P_n) + (0,0).
* Scripts and outputs are in `scratch/cm-numeric/*.py` and `*.out` (PARI 2.17, 400 digits).

**What compiles.** `scratch/cm-numeric/Class7.lean`, run with `lake env lean` after building
`TYZGenus.Package`: no errors, no warnings, and 13 declarations audited with only the three
standard axioms. It contains:

* the pinned objects `tyzForm7`, `tyzZ7`, `Z7`, `Phi0` and `tyzZ`, plus a proof that TYZ's Φ₀ exists
  (`phi0_spec`);
* verbatim, `rfl`-checked copies of the task's Props;
* the split `genusPointLeafCM_of_pinned`, also routed through `genusPointLeaf_of_split`;
* a Galois descent proving `Class7GenusPtDefined` from `CMFieldOfDefinition7` and `GenusFieldLeLni`;
* `tyzSigmaFixesZn_of`;
* the finest main theorem, `tyzThm35ReadingA_of_pinnedLeaves`.

**What remains.** The following are unproved leaves:

* the CM leaves `CMFieldOfDefinitionTYZ`, `CMFieldOfDefinition7` and `TYZSigmaFixesZn`;
* the genus-theory leaves `GenusFieldLeLni` and `IInH4`;
* `HprimeNormal`, which is ring-class's task;
* `Lemma318Literal`, `Thm35First ℓ tyzZ`, `Lemma321Five` and `Lemma321Seven`.

`CMFieldOfDefinition H`, `TYZSigmaFixesZn` and `Lemma318Literal` are not proved in Lean: numerics
cannot prove them for all n. The sign of `[i]` in `tyzZn` is not singled out by any check.
Report: `docs/research/cm-numeric.md`.
