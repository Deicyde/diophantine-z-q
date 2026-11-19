---
declaration: theorem
origin: cited
---

# The odd minimum and the intrinsic odd symbol

Fix the original odd filter, the detecting sequence and one nonprincipal ultrafilter on its stages. Before any
odd minimum is chosen,
$$2j_{\rm gen}(h)\ge2\omega(h)+s(h)-C_{\rm gen},\qquad v_2a_M(D)\ge\min\{M,\ \omega(D)-C_{\rm coarse}\}\tag{F.4, F.5}$$
for known simple zeros $h$ and all admissible $D$. The bounded-weight visible depths
$v_2a_M(D)-\omega(D)$ therefore have an attained finite integer minimum $\delta_o$, and for every weight cutoff
$W$, on a set in the ultrafilter,
$$v_2a_M(D)\ge\omega(D)+\delta_o\quad\text{for every visible }D\text{ with }\omega(D)\le W.\tag{F.6}$$
For every finite operator budget there is a stage at which all the divisions required by the coefficient rules
are valid at every index. On a fixed range the unit symbol is exhaustive, and a unit satisfies
$$\operatorname{ord}_{s=1}L(E^{(D)},s)=1,\qquad j_{\rm gen}(D)\le\omega(D)+C_o,\quad C_o=\delta_o+C_{\rm det}.\tag{F.7}$$
For every cutoff $W$, one table of symbol values on compatible typed graphs with at most $W+1$ vertices occurs on
a set in the same ultrafilter; these tables agree on restrictions, and their union is the intrinsic odd symbol on
all finite compatible typed graphs. It keeps its bounded-weight witness and the coefficient rules, and stationary
tests at the primes of $k$ can later be added through a common alphabet without changing $\delta_o$. No minimum
changes when a vertex is omitted, and no single stage serves every weight.

**Proof sketch.** (3.4), (3.5) and the companion bound (F.3) give (F.4), in which $s(hk')$ cancels; (F.4) with
(O.8) gives (F.5), using at a visible coefficient first that it is a simple zero, and at other odd-sign parameters
that the coefficient is zero modulo $2^M$, which avoids any use of the future minimum. The set of integers attained
by bounded-weight visible sequences on ultrafilter-large sets is nonempty, by the witness $D_w$ with (O.2) and
(O.7), and bounded below by (F.5); its minimum is $\delta_o$. If (F.6) failed on an ultrafilter-large set, choosing a
violating index at each bad stage and one of finitely many smaller values would contradict minimality. A unit is
visible, so (O.8) gives (F.7). For the tables, the moving prime adds only boundedly many label coordinates and the
root characters were fixed before $M_\theta$, so for each $W$ there are finitely many possible tables, and one is
ultrafilter-large.

## Depends on

- [One witness and a compatible detecting sequence (3.7), (O.2)](../coefficient-sources/odd-witness.md)
- [Compatible typed graphs and coefficient symbols](coefficient-symbols.md)
- [Arithmetic realization of the coefficient rules](coefficient-rules.md)

## Proof depends on

- [The genus bound before odd normalization (3.4)–(3.6)](genus-lower-bound.md)
- [A bounded companion in the prepared filter (3.3)](rough-companion.md)
- [Visibility and the native genus index (O.8)](../coefficient-sources/visibility.md)
- [The unaveraged weighted theta comparison (O.7)](../coefficient-sources/theta-comparison.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): the minimum $\delta$ in Section 7 (L2538–2551),
  `ex:app-odd-minimum` (L10151–10256), `ex:app-odd-stabilization` (L10508–10552)

## Manuscript check

Mapped by AI review and read for structure. The review checked the order of choices: the lower bound (F.4)
precedes the theta prime, the precision, the odd minimum, the final field and the binary dimension, and
(F.5) does not use the minimum it serves to define. The ultrafilter bookkeeping is not yet checked line by line.
