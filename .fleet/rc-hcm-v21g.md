# rc-hcm-v21g: level-one fixes, the JetchevKane split, level-N Deuring in Lean

**Scoped stop after injectivity.** Parts (0) and (1) are complete. Part (2) fixes a supersingular reference pair `(E₀, ⟨P₀⟩)` over `F_q^al`. For it, part (2) proves in Lean:
- the map `levelDeuringClass` from isomorphism classes of supersingular enhanced curves of level `N` to `ClassSet (levelOrder q h N hN)`;
- the reference lemma (the reference goes to `⟦fromAdelic z⟧`);
- the order lemma (`End(E, C) ≃+*` the left ring of every representative);
- injectivity.

Every level-`N` step is a Lean proof. The level-one inputs are the permitted Voight candidates in separable scope:
- Thm 42.1.9 and Main Thm 14.1.3 for the frame;
- Thm 42.3.2, invertibility clause (unrestricted) and étale bijection clause;
- Cor. 42.3.7, on integral ideals containing an integer prime to `q`.

No new print was needed. `SeparableIsogenyExists` (GLUE) is stated but unused. All 34 checked declarations use only `propext`, `Classical.choice` and `Quot.sound`.

- **(0)** `HCMV21/DeuringRankFour.lean`:
  - `VoightThm4219`, the printed rank-four candidate;
  - `SupersingularTorsionRankFour`, the GLUE bridge from 42.1.7(ii);
  - `deuringSupersingularEndOrder_of_rankFour`.
  Docstrings re-cite `DeuringSupersingularEndOrder` and `QuaternionRamificationUniqueness` (Main Thm 14.1.3, p. 218).
- **(1)** `JetchevKane` keeps only `classes` (GLUE; Ribet 3.3 reports it without proof; a Lean proof is in progress), with the same arity as before. The new `OperatorComparison` holds `hecke`, `atkin` and `frobenius` (ELLIOT). All consumers are updated. The four sinks, the nine docstring modules, Main and Discharges build.
- **(2)** 13 new files in `ZInQKernel/Contrib/OneProof/RC/HCMV21/`. They include:
  - the left-ideal mirror, from orders being stable under the involution;
  - integral prime-to-`q` representatives, via Nakayama over `ℤ_q`;
  - local principality of the placed level ideal through Tate chain isomorphisms;
  - the identification of `End(E₀, C₀)` with `levelOrder` on class sets;
  - recovery of the level subgroup from the Hom lattice.

**What remains:** surjectivity and the `Equiv` (step 13). This needs the cyclic subgroup built from the nested pair (the converse of `tateLevelPreimage`) and the essential-surjectivity candidate (already stated). It is estimated at 600–900 lines of Lean, with no new print. After that comes the next run: `hecke`, `atkin` and `frobenius`.

**Findings:**
- Jetchev–Kane arXiv v1 §1.1 states `N ≥ 1`, whereas `INVENTORY.md` row A052 says `N > 1`. The v21f "citation scope error" at tex 8468–8474 is withdrawn, but the source proves nothing: it refers to Ribet Prop. 3.3.
- The separable-scope condition "contains an integer prime to `q`" is only meaningful for integral ideals, so the candidates require `I ⊆ O₀`.

[Report](../docs/research/rc-hcm-v21g.md) · [Builds](../scratch/rc-hcm-v21g/builds.txt) · [Axioms](../scratch/rc-hcm-v21g/axioms.txt)

Report commit: 0dc254f23 (this file is committed after it).
