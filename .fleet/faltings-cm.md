# faltings-cm (r9a, r9b): summary

**Proved** (`ZInQKernel/Contrib/OneProof/FaltingsTateSurj.lean`, namespace `ZInQ.Contrib.FaltingsCM`, built; axioms
`[propext, Classical.choice, Quot.sound]` for both theorems):

- `def FaltingsTateSurj : Prop := ∀ K [Field K] [NumberField K] (A B : AbVar K) ℓ [Fact ℓ.Prime],
  {φ | IsGalEquivariant φ} ⊆ Set.range (tateHomZl ℓ A B)`. New LEAF, the surjectivity half of Faltings 1983 Satz 4 /
  Kor. 1 (locator UNVERIFIED), in printed form (a consequence of the statement).
- `faltingsTateSurj_of_faltingsTate : PkgI3.FaltingsTate → FaltingsTateSurj`: the new leaf is never stronger than the
  field.
- `faltingsTate_of_surj : FaltingsTateSurj → ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed → PkgI3.FaltingsTate`.
  Injectivity comes from Mumford §19 Thm 3, which is already the field `OpenTextbookLeaves11.homFreeFiniteAlgClosed`.

**#discharges:** `DISCHARGES [OpenResearchLeaves22.r9b] by ZInQ.Contrib.FaltingsCM.faltingsTate_of_surj`, still
assumes `[FaltingsTateSurj, HomFreeFiniteAlgClosed]`, with the standard axioms.

**Autofold:** `scratch/faltings-cm/autofold.json`. The dry run reports the strict count unchanged (46/10 on 56); its
module compiles, and `sixContactMin_of_open30` uses only the standard axioms.

**Finding: CM theory removes neither field.**
- Every live use is on a general abelian variety:
  - `J₁(N)` and R16's `A_f` over `ℚ` (C9, E1Sub);
  - `J₁(M)_{L'}` (E1);
  - the QM model of the fibre over `J(u)` for arbitrary `u ∈ ℚ \ contactSet` (C2/G8, E1, ConjTwist), which is
    non-CM in general.
- `hCM` is used only on the TYZ branch.
- `r9a` stays a LEAF in printed form (Faltings Satz 3). Semisimplicity is not a formal consequence of the Tate
  property (a non-split extension can have scalar commutant), and nothing in the bundles gives it.
- The consumer table, with file and line for each use, is in docs/research/faltings-cm.md §2.

**Remains:**
- r9a is open.
- The new leaf `faltingsTateSurj` needs a statement check against Faltings 1983.
- The fold is for the integration lead.
