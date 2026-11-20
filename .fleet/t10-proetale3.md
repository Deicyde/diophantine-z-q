# T10 pro-étale comparison

**Verified:** The row's integral pro-étale H¹ is additively isomorphic to the
inverse limit of its finite pro-étale H¹ groups by the original residue
reductions. Countable products of the quotient maps are epi: use successive
affine local lifts and an affine weakly étale inverse limit. This removes
the previous comparison's last assumption.

**Known issue:** At tex 10967–10972 the manuscript's reference to Milne's
Part I, Theorem 12.1(a) for equivariance is incomplete in the local audit,
which points separately to Remark 12.5. The primary-source locators and
scope of Milne's naturality remain unverified. No mathematical error has
been established.

**Verified:** The actual lift sheaf of every finite pro-étale degree-one
class on the geometric abelian variety is represented by a finite étale
surjection, and it splits on pullback to that cover. The two coefficient
presheaves agree under restriction, compatibly with additive coefficient
maps. The seven new modules compile; the axiom check covers 85 declarations
and uses only the three standard Lean axioms.

**Open:** Identify the class of the same torsor in the big étale Ext group
`T10Milne86.FiniteH1`. The next concrete statement is the degree-one
Ext–Čech dictionary for classes split by a fixed étale cover, followed by
refinement and coefficient compatibility. No semilinear square or discharge
was attempted. T10 remains GLUE; count delta zero. See
`docs/research/t10-proetale3.md` and `scratch/t10-proetale3/`.
