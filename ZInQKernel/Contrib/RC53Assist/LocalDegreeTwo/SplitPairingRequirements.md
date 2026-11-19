# Split Selmer pairing: remaining inputs

## Supplied arithmetic input

For the actual localized module

```lean
ResMod (locMap K S q) (Mcoef K S W i α)
```

over `Acoef i`, `exists_stageCoordinate` produces a uniformizer, its tame
root, arithmetic Frobenius and inertia elements, and an `Acoef i`-linear map
on the actual continuous degree-two cochains with both
`LocalDegreeTwoCoordinate` and `LocalDegreeTwoNormalized`.

The unramified character is `urCharN`; the tame character is the exact
`kummerLog` of the chosen root. The scalar cup has local Brauer invariant
`1 / 2^i`, with the unramified character in the first argument. This invariant
identity is proved by an explicit continuous coboundary comparison with the
positive carry class. Surjectivity follows from this cup, not from an assumed
degree-two isomorphism. The map on all cochains is obtained using the proved
self-injectivity of the residue ring, then extended to the full coefficient
module by finite coefficient coordinates. Linearity over the full coefficient
ring is proved.

There are no new printed inputs. Kummer--Brauer injectivity is the independently
typed hypothesis `hKB`. The other hypotheses are the full elliptic torsion,
the trivial derivative action on the finite localized module, fixed local roots
of unity, and the prime not dividing two. The residue coefficient basis is
constructed from the full elliptic torsion and the polynomial power basis.

## Exact consumer shape

With `A` a commutative ring and `L := splitLocalComplex A`, the consumer uses

```lean
abbrev splitSelData (G : GCx A) (res : GHom G (splitLocalComplex A))
    (U : GCx A) (ι : GHom U (splitLocalComplex A)) : SelData A :=
  ⟨G, U, splitLocalComplex A, res, ι⟩
```

and requires

```lean
Q : SelPairData (splitSelData G res U ι) (splitSelData G res U ι)
tr : (coneCx Q.resE).X 3 →ₗ[A] A
htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0
```

The fields of `Q` have the following exact types, after substituting the same
Selmer datum on both sides:

```lean
E : GCx A
EL : GCx A
resE : GHom E EL
cupG : GPair G G E
cupL : GPair L L EL

compat : ∀ (a b c a' b' c' : ℤ)
  (h : a + b = c) (h' : a' + b' = c')
  (ha : a = a') (hb : b = b') (hc : c = c')
  (x : G.X a) (y : G.X b),
  resE.f c c' hc (cupG.P a b c h x y) =
    cupL.P a' b' c' h' (res.f a a' ha x) (res.f b b' hb y)

hU : ∀ a b c : ℤ, a + b = c + 1 →
  U.X a →ₗ[A] U.X b →ₗ[A] EL.X c

isotropy : ∀ (a a₁ b b₁ c c₁ : ℤ)
  (h : a + b = c + 1) (ha : a + 1 = a₁)
  (hb : b + 1 = b₁) (hc : c + 1 = c₁)
  (u : U.X a) (v : U.X b),
  EL.d c c₁ hc (hU a b c h u v) +
    hU a₁ b c₁ (by omega) (U.d a a₁ ha u) v +
    sgn a • hU a b₁ c₁ (by omega) u (U.d b b₁ hb v) =
  cupL.P a b c₁ (by omega) (ι.f a a rfl u) (ι.f b b rfl v)
```

`GPair` also includes the full Leibniz identity for every bilinear component.
None of these global, local-condition or trace fields is a conclusion of the
scalar tame-symbol normalization alone.

## Local comparison still required

Let

```lean
Cq := natCx (contCochains A (Gloc K q) M)
```

and choose a coefficient identification `e : M ≃ₗ[A] Vec2 A`. The intended
local comparison is

```lean
p : GHom Cq (splitLocalComplex A)
```

with components, in degrees zero, one and two,

```lean
p.f 0 0 rfl = e.toLinearMap ∘ₗ evalZero A M
p.f 1 1 rfl =
  (e.prodCongr e).toLinearMap ∘ₗ
    ((evalOne A M D.frobenius).prod (evalOne A M D.inertia))
p.f 2 2 rfl = e.toLinearMap ∘ₗ c₂
```

and zero components outside these degrees. The degree-two component and its
boundary identity are supplied. Trivial coefficient action gives the degree-zero
boundary identity for the degree-one component. These formulas specify a
cochain projection, not yet a proved quasi-isomorphism.

The remaining quasi-isomorphism inputs can be stated as

```lean
Function.Injective
  (tameCoordH1 D.frobenius D.inertia
    (fun m => htriv D.frobenius m)
    (fun m => htriv D.inertia m))

∀ n : ℤ, 2 < n → Subsingleton (Cq.toCC.homology n)
```

with degree-one surjectivity realized by the same oriented unramified and tame
characters. A paired transport needs the reverse comparison and its cochain
homotopies, or a proved construction deriving these from the comparison; an
abstract isomorphism of cohomology groups does not supply the required cup
compatibility and isotropy homotopies.

The ring and coefficient identifications must be retained as well when the
consumer is written over `StageA i` rather than `Acoef i`.

## Cup compatibility and the local condition

The normalized mixed scalar cup does not assert either self-cup identity. The
retained degree-one cup table must include the finite and singular self-cups
and the reversed mixed cup, as well as the degree-zero/degree-two adjoints.
At two-power precision the vanishing of the tame self-cup needs the retained
extra precision; fixed `2^i`-th roots alone do not imply that `-1` is a
`2^i`-th power. The extra arithmetic hypothesis may be expressed as

```lean
∃ z : q.adicCompletion K, z ^ (2 ^ i) = -1
```

when this is the route used to discharge the tame self-cup.

The actual Weil pairing and conjugation must be transported so that the local
cross pairing is the retained `ε e₂(x, J y)`, not just an arbitrary perfect
pairing on modules of the same size.

The displayed consumer type pairs the same `U` with itself. Its `isotropy`
field is therefore a self-isotropy requirement. Strict/relaxed orthogonality
cannot be silently substituted for it. In particular, the relaxed condition
retains the entire degree-one finite-plus-singular space; its mixed pairing is
nonzero, so a zero self-isotropy homotopy for that condition is not justified.
The actual choice of condition, or a two-condition consumer using the strict
and relaxed data separately, must be specified.

## Trace and global duality

After the local comparison, cup compatibility and condition homotopies have
been supplied, the original Galois compact-target trace must be transported
to the displayed `coneCx Q.resE`. The required identity is exactly `htr`
above. The final consumer also requires the independent global statement

```lean
QuasiIso (GHom.toCC (globalDualityMap Q tr htr))
```

in that transported diagram. The existing global duality and trace results
apply to their original Galois targets; equality of their transported maps and
targets must be proved before applying them to this `Q`.

No split-model `Q` or transported global trace is claimed here. The supplied
result closes the normalized local degree-two arithmetic input, not these
remaining paired-diagram constructions.
