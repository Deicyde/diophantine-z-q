# Derivative-switch determinant interface — independent proof coverage

Status: **research PR candidate, not arithmetic acceptance**. Date: 2026-11-08.

This is the ingested and checked working edition of the supplied ZIP packet.
The received archive has SHA-256
`7242ed88ac6e93a30aed751f53b3bf252b4be332382011280e3d4f2d85afeb75`.
See [verification and statement coverage](VERIFICATION.md) and the
[local reproduction entry point](README.md). The original supplied bytes are
preserved separately; preparation-environment statements in the uploaded README
are historical, not evidence of current verification.

## Frozen source and ownership

- Target fork: `CheyLoveday/diophantine-z-q`, default `main`.
- Pinned inherited baseline: `9c0b3aba60d90fdcac82115f0582a6f52f1054f7` (Version 13).
- Owning claim: `manuscripts/quartic_v13.tex`, `ex:limits-derivative-switch`;
  consumers: `ex:limits-uniform-lower-bound`, (5.5a), (5.5), and
  `ex:arith-paired-functional`.
- Underlying finite arithmetic: (H19)--(H22), (4.2); source duality is
  Nekovar's Selmer-complex functoriality. Those arithmetic implications
  are **not** proved by this packet.
- Repository protocol: `AGENTS.md`, `docs/research-review/PROTOCOL.md`
  and `docs/audit-history/PROTOCOL.md`.
- Frozen accepted Lean snapshot: 48 modules in `lean/ZInQ/`; do not edit
  those sources, `lean/ZInQ.lean`, `SOURCE_MANIFEST.json` or the frozen target
  to force admission of this separate research work.

## Source-exact model and rank scopes

Let `R` be a DVR with fraction field `L`. At a derivative prime use
`U_str = D0`, `U_rel = D0 + (F + S)[-1]`, `U_F = D0 + F[-1]`,
`U_S = D0 + S[-1]`, retaining D0 in each condition.

Over an appropriate characteristic-zero test field let

    dF : F -> H²(C_str), dS : S -> H²(C_str)
    J : F -> S, dim F = dim S = 2, det J = -1.

The manuscript's relaxed self-annihilator assertion is exactly the
**hypothesis**

    ker [(x,y) |-> dF(x)+dS(y)] = L (v,0) + L (0,Jv)

for the actual nonzero old localization `v`, with derivative singular
localization `Jv`.

Consequences proved in ordinary algebra, and proposed for a separate
Lean module:

1. `ker dF = Lv` and `ker dS = L(Jv)`. Both generic H¹ dimensions equal
   one. No rank reduction is asserted on this generic inner field.
2. `im dF ∩ im dS = {0}`. Proof: if dF(x)=dS(y), then
   (x,-y) is in the combined kernel, forcing x in Lv and y in LJv,
   so both boundaries vanish.
3. Provided F has a vector not in Lv, `dF != dS ∘ J`. A distinguished
   triangle map with identity on the strict object and J on the quotient
   would force this equality; consequently that particular triangle
   square cannot be the required source of determinant compatibility.
   This does NOT rule out all complex isomorphisms with a *nonidentity*
   strict factor, and does NOT refute equality of determinant valuations.
4. Exterior local volume satisfies
   `area(Jv,Jx)=det(J) area(v,x)=-area(v,x)`.
   In a DVR, for `v=pi^k v0` with primitive v0, the complement x with
   unit area can be fractional; J transports it without a valuation
   loss. The transport by an integral invertible J also induces an
   isomorphism on `F/Rv -> S/RJv`, so the respective torsion modules
   and Fitting ideals agree. The last quotient assertion remains an
   *ordinary algebra proof*, not a declaration in the bundled Lean file.

The source's *outer* rank drop is a distinct operation. A family with
rank-one generic kernels can acquire extra kernel directions in the
outer ultraproduct when nonunit matrix entries tend to zero. Those
new directions are then removed by derivative-prime selection. This
fact neither proves nor disproves a quasi-isomorphism of each generic
inner pair. The incompatibility of the identity-on-strict square is
instead the direct boundary calculation above.

Allowing a nonidentity strict map removes that particular obstruction over the
inner generic field: choose `x` outside `Lv`, put `a=dF(x)` and `b=dS(Jx)`, and
define `T(a)=b`, `T(b)=-a` on their independent image lines. If strict H² has
dimension two this is a determinant-one automorphism of that space. At the
rank-reducing field, in contrast, the manuscript has `U=F`; then `dF=0` and
`dS J` is injective. There is no boundary intertwiner at that test, even a
noninvertible one. A compatible integral derived strict automorphism therefore
cannot be required as a replacement strategy. These observations are ordinary
algebra here; the six Lean theorems below do not formalize an eta construction,
derived triangles, or specialization.

## Exact formal coverage

The first four Lean theorems work over **any field**, with modules and a linear
equivalence `J`, conditional on the explicitly defined `AxesKernel`. They do
not assume characteristic zero, finite dimension, or `v != 0`. The no-go
theorem additionally assumes a vector outside the scalar line of `v`.
Consequently they prove the stated kernel membership and image-intersection
identities, not a formal dimension-one theorem or the arithmetic occurrence of
the hypotheses. Those dimension assertions additionally use the source's
nonzero `v`, dimension-two local planes, and actual exact triangles.

The two `Volume` theorems prove polynomial identities on pairs over an arbitrary
commutative ring. They do not declare DVRs, fractional complements, quotient
modules, Fitting ideals, global functionals, or determinant lines. A primitive
DVR vector has a unit-volume complement by Bezout; scaling by `pi^k` scales
that complement by `pi^-k` over the fraction field. The quotient isomorphism in
item 4 follows because integral `J` and its inverse carry `Rv` and `RJv` to
each other. These are the ordinary algebra bridges, rather than hidden Lean
coverage.

## Correct determinant comparison target

The two actual triangles (not a claimed morphism between them) are

    C_str -> C_F -> F[-1] -> C_str[1]
    C_str -> C_S -> S[-1] -> C_str[1].

Their determinant-line additivity, combined with `det(J)=-1`, defines
an integral isomorphism of inverse-determinant lines

    Phi_det : det^-1(C_F) ~= det^-1(C_S).

This construction does not require an isomorphism `C_F ~= C_S`.

**Separate, still-unproved arithmetic compatibility**:

    Phi_det( [A] tensor [lambda_A] )
      = epsilon * ( [B] tensor [lambda_B] ), epsilon in R^x.

The symbols `lambda_A`, `lambda_B` must denote the exact integral
functionals constructed via conjugate transport, inverse orthogonal
comparison and Poitou--Tate duality. A determinant-line map **does
not automatically induce** a map between the individual degree-two
functional spaces. Comparing arbitrary rescaled functionals would
silently assume the missing conclusion.

The next valid step must state and verify boundary--cup adjunctions
for the actual H19--H22 cochains and their homotopy-corrected maps,
and compare the precise determinant bases, at both the completed
2-adic DVR and the required height-one localizations. The fixed
clearing factor and old-place torsion must remain attached.

## Nine application obligations

| Obligation | Current evidence | Pending item |
| --- | --- | --- |
| Primary source | V13 lemma and arithmetic proposition located | Primary Nekovar diagram hypotheses must be checked at exact loci |
| Constructed objects | Local F/S split, J, v and derivative vector stated | Actual finite Selmer cochain maps required |
| Domain coverage | Generic inner field and separate outer scope distinguished | Every required height-one and outer comparison |
| Transition maps | Abstract boundary maps and no-go checked | H19--H22 cup/transfer naturality |
| Object identity | Abstract A->B localization fixed | Identify actual paired lambda after switching |
| Coefficients | Matrix J integral, det -1 | Ring-specific duality, base changes and units |
| Local conditions | D0 kept in four derivative conditions | Local orthogonal homotopies after compression |
| Exceptions | Divisible v allowed, fractional complement | Quadratic t and t+2 and old support torsion |
| Consumers | (5.5a), (5.5) and regularity identified | Full unit-coordinate transport into consumers |

## Concrete countermodel (finite dimensional, exact)

Over Q, take `F=S=H=Q²`, `J=diag(1,-1)`, and `a != 0`:

    dF = [[0,a],[0,0]], dS = [[0,0],[0,a]], v=(1,0).

Both kernels have dimension one and the combined boundary has kernel
`Q(v,0) + Q(0,Jv)`. Nevertheless `dF != dS J`. The images are
independent lines in H. Thus equal generic ranks do **not** justify
an identity-on-strict triangle square.

For a=2^m, class A and derivative B with coordinates 2^k in their
respective generic lines, and paired functionals consistently
normalized with coordinates 2^k, both determinant-coordinate
valuations are 2k-m (up to a sign). This is an illustrative model,
not a proof that the arithmetic functional has this normalization.
Multiplying only the new functional by 2 changes the comparison by
an explicitly nonunit factor, without changing the local J evidence.

The checked torsion example uses the shared strict differential `(a,0,0)^t`
and the three-by-three plane differentials

```math
D_F=\begin{pmatrix}a&0&0\\0&0&0\\0&0&1\end{pmatrix},\qquad
D_S=\begin{pmatrix}a&0&0\\0&0&1\\0&0&0\end{pmatrix}.
```

Both classes are `(0,2^k,0)^t`; the closed functionals are `(0,2^k,0)` and
`(0,0,2^k)`. Their local vectors satisfy the exact `J=diag(1,-1)` relation.
The checker derives the coordinates `2^(2k)/a` and `-2^(2k)/a` from every
cofactor in `z lambda = u adj(D)`, retaining the strict `R/(a)` factor.
It also derives the changed coordinate after rescaling the second functional.
It does not merely assign the desired ratios. These choices model the
normalization; they do not establish it for the arithmetic functionals.

## Verification boundaries

Execute:

    python -B research/determinant-switch/check_local_model.py
    cd lean && lake env lean Research/DerivativeSwitchBoundary.lean
    python -B scripts/check_audit_history.py --self-test
    python -B scripts/check_lean.py

For one fresh, logged native verification of this packet, from the repository
root use:

```sh
python3 -B research/determinant-switch/verify.py \
  --output lean/.checks/derivative-switch-fresh
```

The output directory must not already exist. Prepare the two pinned dependency
import closures as described in [README.md](README.md). The driver checks all
nine dependency revisions and tracked-source cleanliness, compiles this target
into a fresh output tree with `debug.skipKernelTC=false`, prints its statements
and transitive axioms, and rejects axioms outside `propext`, `Quot.sound`, and
`Classical.choice`. The frozen-source and audit-history checks are separate
guards; their passing status does not establish coverage of this new module.

The supplied packet reported a Python pass but no Lean compilation in its
preparation environment. Current results are bound in [VERIFICATION.md](VERIFICATION.md)
and `evidence/RESULT.json`; do not inherit the earlier uncompiled status or
treat a supplied success claim as an observed check. Local macOS verification
uses pinned Lean 4.35.0 **without `--paranoid`**, as requested. External checkers,
Linux bubblewrap isolation, release-profile reproduction, and independent
mathematical acceptance are not claimed. No finite test verifies the arithmetic
theorem.

## PR acceptance scope

- Acceptable: an isolated, compiled finite-dimensional no-go lemma;
  generic-kernel and boundary-image lemmas; integral 2x2 volume
  transport; exact regression controls; a clearly typed open
  arithmetic naturality obligation.
- Not acceptable: new claims of a completed integral Selmer comparison,
  a proof of restricted converse, an isomorphism `C_F ~= C_S` fixing
  `C_str`, or manuscript-level acceptance without a separate source
  audit and non-author mathematical review.
- This is a **non-release**, independent research PR in the owner's fork.
  It should not update upstream release manifests or acceptance hashes.

This isolated packet changes no publication source, accepted helper source,
dependency pin, polynomial artifact, release asset, or canonical proof-status
record. Consequently manuscript/PDF regeneration and release archive
synchronization are outside this small non-release candidate's scope. A future
arithmetic integration or release must obtain its own non-author review and
perform all applicable maintenance; this local verification grants no such
acceptance.
