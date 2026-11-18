# Appendix F: Eichler order handoff

**Scoped stop.** The locally principal right-ideal model gives a finite class set for any full order in a definite rational quaternion algebra. Every class has an integral representative of uniformly bounded positive additive index. Its left order has a rank-four integer basis, and its unit group is the class stabilizer, embeds in the ambient units, and has order dividing `Odd.c0`. For good primes, reversal of actual index-`p²` ideal arrows proves the App F weighted adjointness once the kernels are indexed by lines.

The class, finiteness, subgroup and weight terms fit the existing Visibility and App F fields. No changes to either `ThetaStage` or `ThetaSide` are needed. The explicit order for `ell₀ ≡ 3 (mod 4)` is proved closed under multiplication and full; the algebra is proved anisotropic at infinity.

Three steps remain: realize the Eichler local profile globally (including finite ramification and maximality in the explicit case), identify the ideal classes and their left orders with the adelic double cosets and stabilizers, and identify the locally principal index-`p²` kernels with the lines in `F_p²`. The precise statements and manuscript checks are in [the report](../docs/research/rc-eichler.md). No manuscript error was identified in the checked scope.

All eleven Lean files compile. The [78 axiom checks](../scratch/rc-eichler/axioms.md) use only `propext`, `Classical.choice` and `Quot.sound` or no axioms. No new printed leaves were added.

Final proof and report commit: `8cd1da90038d3f78c8a2640f5156b0e940dace6e`. This handoff is the sole change in the following commit.
