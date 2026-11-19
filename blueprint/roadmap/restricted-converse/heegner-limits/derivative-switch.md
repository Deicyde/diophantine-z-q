---
declaration: theorem
origin: cited
---

# Derivative local conditions and the determinant-preserving switch

At a derivative prime $v$ use $L_v=D^0\oplus(F_v\oplus S_v)[-1]\oplus D^2[-2]$ with the transported pairing,
and keep $D^0$ in all four conditions:
$$U_{\rm str}=D^0,\quad U_{\rm rel}=D^0\oplus(F_v\oplus S_v)[-1],\quad U_F=D^0\oplus F_v[-1],\quad U_S=D^0\oplus S_v[-1].$$
Then strict and relaxed are orthogonal, the two plane conditions are self-orthogonal, and the cone triangles
$C_{\rm str}\to C_F\to F_v[-1]$ and $C_{\rm str}\to C_S\to S_v[-1]$ hold. The finite and singular planes are
free of rank two with cross pairing $\beta(x,y)=\varepsilon\langle x,Jy\rangle$.

Over the relevant fraction or test field, suppose the old class $A$ spans generic $H^1$ and has finite
localization $f(A)=v\ne0$, and let $B$ be its derivative, with $f(B)=0$ and $s(B)=Jv$ by (4.2). Then the strict
generic $H^1$ vanishes, the new generic $H^1$ is spanned by $B$, and the class-functional coordinates of the
finite and singular determinant sequences have equal valuations, even when $v$ is divisible.

**Proof sketch.** The orthogonality statements are linear algebra with $D^0$ paired to $D^2$ and $F$ to
$S$; keeping $D^0$ removes the $H^0$ terms from the triangles. The transported duality and localization
identities identify the relaxed localization image with its exact annihilator (Nekovář, 6.3.3–6.3.4), a
Lagrangian of dimension two in $F_v\oplus S_v$. It contains $(v,0)$ and $(0,Jv)$, which are orthogonal since
$\beta(v,Jv)=\varepsilon\langle v,v\rangle=0$, so they span it, and the new $H^1$ is spanned by $B$. For the
determinants, choose $x$ with $v\wedge x$ of unit volume and $y$ with $Jv\wedge y$ of unit volume in the
fraction field; the two determinant sequences share the strict factor, so the coordinates have equal
valuations, and all strict torsion stays in that common factor. Requiring $x$ integral would be wrong when
$v$ is divisible.

## Depends on

- [Local conditions, the derived Kummer condition and duality](local-conditions.md)
- [Finite Heegner descent with one multiplier (4.1), (4.2)](finite-heegner.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-derivative-switch` (L4833–4908)

## Manuscript check

Checked line by line by AI review, with the switch pairing and the symmetry of the determinants checked by
script. The manuscript states the equality of valuations in two sentences; written out, $H^2(C_{\rm str})$ has
the dual basis $A^*,B^*$, the finite plane maps to $H^2$ by $x\mapsto\varepsilon\langle x,v\rangle B^*$ and the
singular plane by $y\mapsto\varepsilon\langle v,Jy\rangle A^*$, both pairings are units with the unit volumes
above, and the symmetry needs $s(B)=Jf(A)$ exactly, which (4.2) gives. The locator in Nekovář (6.3.3–6.3.4) is
not yet checked against the print.
