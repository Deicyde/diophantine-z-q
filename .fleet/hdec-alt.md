# hdec-alt (2026-11-11): fleet report

Full note: `docs/research/hdec-alt.md`. Lean draft: `scratch/hdec-alt/Leaves.lean`. Log:
`scratch/hdec-alt/log.md`.

**Verdict.** No published theorem replaces the core of Glazer's Theorem 4.1. Von Känel's
effective Shafarevich bound for `GL₂`-type varieties over `ℚ` needs a `GL₂`-type `B₀ ⊇ A` whose
dimension is not bounded in `M`. Its constant then grows with the dimension and breaks the
polynomial `M²⁴` shape. That depends on recalled forms of the theorem (UNVERIFIED, no network),
so reading vK arXiv:1310.7263 is the first open check. Baker-type genus-two Shafarevich theorems
are excluded by bad stable reduction at the contact primes. The height, isogeny and
explicit-model papers are already inputs of the existing proof. **One substitution is sound and
adopted:** modularity by Ribet (building blocks) plus Khare–Wintenberger (`GL₂`-type over `ℚ` is
modular), in place of Pan plus p-adic Hodge theory (h-trust C3-C5, C7, C8). It removes 6 leaves
and two passages that are new in N5, adds 2 leaves and an elementary twist lemma, and leaves the
constants unchanged. The argument is VERIFIED here but not yet reviewed.

**Leaf count:** 30 published theorems, without merging distinct ones: **18 deep** (in no
library), 7 already formalized in Tau Ceti or Stacks, 5 textbook. Glue: 21 steps, of which F4 and
the transfer arithmetic are already proved in Lean. "About ten" cannot be reached without hiding
theorems.

**Statable now (concrete Mathlib Props, compiled):** Hasse principle and Hilbert reciprocity for
quaternion algebras over `ℚ`, Kronecker–Weber, Skolem–Noether, Brauer–Nesbitt. Sixteen more
leaves (Raynaud, Néron–Ogg–Shafarevich, Mumford's rank bound, Faltings' Tate theorem, Ribet,
Khare–Wintenberger, newform twists, Shimura's `A_f`, Carayol, Javanpeykar, Gaudron–Rémond,
Faltings' isogeny-height lemma, additivity, Bost, Pazuki, Igusa–Lin–Yang) are stated over
genuine cheap definitions (`AbelianVariety` from Mathlib group schemes, `GalRep`) plus 22
`opaque` placeholders. They are not faithful until the placeholders are built. Top theorem
`jHeightBoundAt_of_leaves`: `sorry`. Final step `sixContactMinAt_of_jHeightBoundAt`: proved
(standard axioms).

**Biggest missing definition:** the Faltings height (very large; carries 6 leaves). Then Shimura
curves with canonical models, and Tate modules with newform Galois representations.

**Most serious risk:** L13 (Ribet) and L14 (Khare–Wintenberger) are stated from memory. Ribet's
theorem is in a proceedings volume, and its exact printed form must be read before adoption.
Behind it, Lemma PR, NoCM, the scalar descent and the conductor bound remain model-reviewed only.
