# t28-igusa results log

Leaf: `PkgI1.IgusaClebschSeparation` (T28), copied verbatim with its definitions
(`J2 J4 J6 j10Data J10 sexticAct lyVec`) from scratch/h-decomposition/Leaves.lean lines 423-784
into scratch/t28-igusa/Defs.lean. Compiles (VERIFIED, `lake env lean`, 77 s).

## Plan (route choice)
- (⇒) transformation law: elementary; proof by generators of GL2 (diag, swap, translations),
  cocycle identity for `sexticAct`, and for translations the derivation trick
  (d/dt J(f(x+t)) = (D J)(f(x+t)), D = Σ (i+1) a_{i+1} ∂/∂a_i, D J = 0 by `ring`).
- (⇐) reduction to exact equality of invariants (scaling by a square root of r).
- (⇐) content: see docs/research/t28-igusa.md for the route comparison.

## Computer algebra (scratch/t28-igusa/mestre_check.py, VERIFIED by running)
- With transvectants (φ,ψ)_k normalized by (m-k)!(n-k)!/(m!n!), Clebsch covariants
  i=(f,f)_4, Δ=(i,i)_2, y1=(f,i)_4, y2=(i,y1)_2, y3=(i,y2)_2 and G_ij=(y_i,y_j)_2,
  a_ijk=(f, y_i y_j y_k)_6:
  * conic identity Σ adj(G)_ij y_i y_j = 0 (identically in x,z): 8 random integer sextics.
  * reconstruction identity det(G)^3 · f = Σ_{i,j,k} a_ijk (adj G·y)_i (adj G·y)_j (adj G·y)_k,
    constant exactly 1: 8 random integer sextics.
  * A,B,C,D, G_ij, a_ijk scale by powers of det M under f ↦ f∘M (one random M).
  * leaf normalization (PARI genus2igusa) in terms of Clebsch A=(f,f)_6, B=(i,i)_4, C=(i,Δ)_4,
    D=(y3,y1)_2: J2=-240A, J4=4320A²-18000B, J6=34560A³-432000AB-1440000C,
    J10=-15925248A⁵+248832000A³B+414720000A²C-777600000AB²-1555200000BC-1166400000D
    (interpolated on 30 sextics, checked on 10 fresh ones).

## Lean
- T1.lean (defs + JnR + actC + J10_eq + sexticAct_eq + actC_actC + actC_scale): those four
  compile (VERIFIED, 1m49 total). A single 246-term J10R definition times out in elaboration
  (4M heartbeats); split into 10 chunks J10R0..J10R9 it elaborates.
