# composite-out (fleet note)

**Result: the composite `shimuraMainThmIDeligneY3AbU` (gt-rayclass) is no longer needed.** All three of its uses are
proved in Lean. Standard axioms only, and no new leaf. The three uses:
* `rayClassCMAb`;
* `shimuraFamilyAb`;
* dcy3-used's `TSHecke.Y3Connected`.

They follow from leaves already proposed by other tasks:
* `QMRecPrinted.MainTheoremCM` (qmrec-printed, printed form);
* `ShimuraSplit2.ShimuraHolFamilyAb`, or its ∀-form `ShimuraHolModAll` with the X6 witness (shimura-split2,
  published, pending reading; itself a consequence of the composite).

The rest comes from fields the bundles already keep: the textbook fields and `mumfordGroupLaw`.

* **File:** `ZInQKernel/Contrib/OneProof/CompositeOut.lean`. Main theorem `CompositeOut.compositeUses_of_hol`; also
  `y3Connected_of_hol` and `y3Connected_of_modAll`.
* **New argument (a): `Y3Connected` from a holomorphic family known only as QM pairs.** Its level structure may jump
  with τ, and no map `Ψ` is used. For `w ∈ 𝒪^×`, the families are `A^w = y ≫ e_w`, where `e_w` is a Hecke
  automorphism. For a clopen `U`, `χ(w) = [A^w_τ ∈ U]` has three properties:
  * it is constant in τ;
  * it depends only on `w mod 3`;
  * it is invariant under a conjugate of `c ≡ (1+i+j)⁻¹`, by reciprocity at `√2+i` from `MainTheoremCM`, and under a
    conjugate of `ω⁻¹`, by the elliptic point `i√3`.

  `decide` tables in `(𝒪/3𝒪)^×` show these generate everything for any conjugator, so `χ` is constant.
* **(b): `shimuraFamilyAb` needs an analytic leaf** (holomorphy of the moduli map; SPECULATIVE that no Lean route
  avoids one). The smallest leaf found is shimura-split2's.
* **Compiles (VERIFIED):**
  * the file: 0 errors and standard axioms;
  * `lake build` of Main, Discharges and the file: OK, 12998 jobs;
  * `#discharges`: no current field matches, as expected, since only the composite's uses are proved;
  * the bypass dry run `scratch/composite-out/BypassFold.lean` (on dcy3-used's): `sixContactMin_of_open31` and
    `frozenTarget_compositeOut` have standard axioms;
  * the spec is `scratch/composite-out/autofold.json`, a bypass.
* **Count:** composite out, `mainTheoremCM` and `shimuraHolModAll` in. Strict GLUE is unchanged now and drops by 1
  when the `ShimuraHolModAll` reading clears. It is now compatible with dcy3-used's −1.
* **Remains:**
  * the integrator's hand fold;
  * the readings of `ShimuraHolModAll` (Shimura 1963/1967, Deligne 1971 §4) and of `MainTheoremCM`'s torsion clause.
* **Report:** `docs/research/composite-out.md`. **Log:** `scratch/composite-out/log.md`.
