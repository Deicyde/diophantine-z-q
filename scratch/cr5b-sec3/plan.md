# cr5b-sec3 plan

Files under ZInQKernel/RouteK/Rank5b/Sec3/, root ZInQKernel/RouteK/Rank5bSec3.lean.

Generic setting (namespace ZInQ.RouteK.Rank5b.Sec3): `ι` Fintype, DecidableEq; bits
`a : ι → ι → ZMod 2`, `y z : ι → ZMod 2`; reciprocity `a i j + a j i = y i * y j` (i ≠ j).

1. Defs.lean: `lapl a U` (Laplacian on U), `kappa a B ρ` (det of L_B on B∖ρ, Matrix.det on the
   subtype), `redeiG a y z B` (Prop 2.3 kappa forms; case y(B)=1 written Σ y_ρ κ_ρ, = κ_ρ by Lemma 2.2(1)),
   `genusSum5b` (Finpartition sum), d-level `gBit`, `T5b`, `CertifiedRankTYZ`.
2. Perm.lean: permanent-minor `pmin M R C` over normalized functions ι → ι; det = pmin over ZMod 2;
   row linearity, row expansion, alternating, relabel.
3. Forest.lean: maps, root map r = f^[card ι], acyclic, forest lemma (per-W form):
   pmin (lapl a U) (U∖F) (U∖W) = Σ_{f acyclic, roots F} wt f [W transversal of the trees].
   Proof: expand diagonal → Σ_f wt f · #compat(f,W); compat ≃ valid E-sets
   {E ⊆ R : InjOn f E, f E ⊆ E ∪ F, (E ∪ F) \ f E = W}; cycle → involution E Δ Z; acyclic → E = paths from W.
4. Redei.lean: κ = Σ arborescences; KD (Lemma 2.2(3)) via row-sum trick; 2.2(1); (2.1),(2.2).
5. Det.lean: X = yyᵀ + D_y; rank-one lemma det(N + uuᵀ) = det N (1 + u·x) if N x = u;
   det M5b = (1+y(V)) det N, N = border(P,(0,y)), P = [[D_y, Lᵀ],[L, D_z]];
   det N = Σ_k y_k (det P(z[k↦1]) + det P(z[k↦0])); det P(c,d) = Σ_{F,W} c^F d^W pmin L.
   ⇒ det M5b = Σ_{φ forest of V} wt φ Π_T y(T) Σ_{k root} y_k z^{R∖k}   (y(V)=0).
6. Glue.lean: gluing forests along a Finpartition; root-partition correspondence; FPF involution parity.
7. Row5b: T5b (marked form) = same forest sum ⇒ Theorem 3.6. Prop 3.5 if time.
8. CertifiedRankTYZ → CertifiedRank5b; variant main theorem; cross-check (optional).
