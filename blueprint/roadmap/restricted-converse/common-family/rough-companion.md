---
declaration: theorem
origin: cited
---

# A bounded companion in the prepared filter (3.3)

Let $h$ range over positive squarefree parameters in the prepared odd-sign unit filter containing $1$,
prime to its fixed support; thus $h\equiv1\pmod8$ and $w(E^{(h)})=-1$. There are constants $A$ and $C_E$,
fixed before $h$ and before any additional finite exclusion set, such that for every such $h$ there is a
negative odd fundamental discriminant $k'$, prime to $2Nh$ and to the exclusions, a square at every place
dividing $2Nh$, outside the fields with extra units, for which $hk'$ is partitionable, $L_*(hk')\ne0$, and
$$\omega(k')\le A,\qquad v_2L_*(hk')\le2\omega(h)+2\omega(k')+s(hk')+C_E.\tag{3.3}$$
Here $A$ is a fixed number of dummy labels plus five.

**Proof sketch.** Prepare an even symbol for each of the finitely many total types at the fixed support.
A least nonempty unit seed does not depend on its internal bits, and the parity of a negative discriminant
at $2$ makes its total label nonzero, so it is nonempty. Before $h$ varies, fix a bounded multiset of dummy
labels supplying the anchors of every prepared seed. For each $h$, realize the dummies by fresh primes, put
the fixed support, the primes of $h$ and the dummies in the exclusion set, absorb $h$ and the dummy product
into the curve, and apply the even case of the nonvanishing theorem: it adds at most five primes and gives
$k'$ with $L_*(hk')\ne0$. The dummy supply makes $hk'$ partitionable whatever its remaining primes. Nonzero
central value gives Selmer corank zero by the forward rank-zero case of Lemma 5.5, and (3.3b) gives (3.3).
In Appendix G the same bound appears as (F.1)–(F.3): a unit symbol gives
$v_2L_*(\sigma D)=2\omega(D)+C_{e,\rm unit}$ (F.1), and the one-symbol address cube with the comparison of
Section 9 gives $v_2L_*(d)-2\omega(d)-s(d)\le C_{e,\rm unit}+2C_{\rm loc}$ for partitionable corank-zero $d$
(F.2).

## Depends on

- [Finite realization, unit seeds and contraction certificates](seeds.md)

## Proof depends on

- [Nonvanishing in a prescribed unit filter](../coefficient-sources/nonvanishing.md)
- [The partitionable even upper estimate (3.3b)](even-upper.md)
- [The fixed-form even scalar (3.2)](../coefficient-sources/even-scalar.md)
- [An actual even form with rational normalized phase](../coefficient-sources/even-form.md)
- [The address constructions](address-constructions.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-rough-companion` (L2343–2401) and
  `ex:app-rough-companion` (L10055–10150)

## Manuscript check

Mapped by AI review in Section 7 and Appendix G, and read for structure; not yet checked line by line. The
review checked the order of choices: dummy types and their number are fixed before $h$, their prime
realizations after $h$ and the exclusions, and the companion does not use the later odd minimum.
