---
declaration: theorem
origin: cited
---

# Finite Heegner descent with one multiplier (4.1), (4.2)

Let $K$ be imaginary quadratic, split at every prime of $2N$, not $\mathbb Q(i)$ or $\mathbb Q(\sqrt{-3})$; let
$f$ be prime to $2ND_K$ (it may contain the active primes and the moving prime), $H_f$ the ring class field
of $\mathcal O_f=\mathbb Z+f\mathcal O_K$, $I$ a finite set of good inert primes outside $6fND_K$,
$n_I=\prod_{\ell\in I}\ell$ and $M_I=H_{fn_I}$. Let $\theta=\chi_h\Psi$ (or the universal quadratic character
times $\Psi$) be a finite character of $\operatorname{Gal}(H_f/K)$ with values in
$A=(\mathbb Z/2^m)[t]/t^b$ or $A[G]$, with $\Psi$ trivial at $2N$. There are integers $e\ge0$ and $L>0$,
depending only on the fixed curve, parametrization and old local types, with the following properties.
Forming the Kolyvagin derivative over $H_{fn_I}/H_f$ and descending it before applying $\theta$ gives finite
classes $P_{I,m}$ with the old Kummer conditions, unramified conditions at the other good places, and full
conditions at the active and moving primes; for $I=\varnothing$, $P_{\varnothing,m}$ is the Kummer class of
the $L$-multiplied unaveraged weighted point. The unaveraged norms satisfy
$$\operatorname{Tr}_{H_{d\ell}/H_d}y_{d\ell}=a_\ell y_d\quad(\ell\text{ inert}),\qquad\operatorname{Tr}_{H_{dq}/H_d}y_{dq}=(a_q-\sigma_q-\sigma_q^{-1})y_d\quad(q\text{ split}).\tag{4.1}$$
If $a\ge m+e$ and every new derivative prime has $\rho_T(\operatorname{Fr}_\ell)\equiv\rho_T(\tau)\pmod{2^{a+1}}$,
the classes at precision $m$ satisfy, in common coordinates at the derivative prime,
$$f(P_{I\cup\{\ell\},m})=0,\qquad s(P_{I\cup\{\ell\},m})=Jf(P_{I,m}),\tag{4.2}$$
where $f$ and $s$ are the finite and singular coordinates and $J=\rho_T(\tau)$. All this holds over $A[G]$
before evaluation at characters, with finite cocycles and boundary witnesses, and no multiplier depends on
$K$, $f$, $I$, $m$, the truncation, the number of active primes or $|G|$.

**Proof sketch.** Serre's open image theorem gives $n\ge2$ with $1+2^nM_2(\mathbb Z_2)$ in the image and an
element $z$ acting as $u^4$ with $e=v_2(u^4-1)=n+2$, fixing every ring class field; so $2^e$ kills
$E(H_d)[2^\infty]$ (H1)–(H2). The norm relations (4.1) are Cai–Chen–Liu's Theorem 2.15 on $X_0(N)$, with no
cuspidal correction since $\pi(\infty)=0$. The CM congruence $\bar y_{d\ell}=F_\ell\bar y_d$ at a supersingular
place (H4), the structure $\prod_\ell C_{\ell+1}$ of the relevant kernel (H5) and $(\sigma_\ell-1)D_\ell=(\ell+1)-\operatorname{Tr}_\ell$
(H6) make the derivative classes invariant (H7). Inflation–restriction with the torsion bound (H8)–(H9),
local descent at unramified places (H10) and the multiplier $L=m_0C_\pi C_{\rm bad}2^{2e}$ (H11) give the
local conditions. At a derivative prime, $\rho(\operatorname{Fr}_\ell)\equiv J\pmod{2^{a+1}}$ forces
$2^{a+1}\mid a_\ell$ and $2^{a+1}\mid\ell+1$ (H12); the Frobenius identities (H13)–(H18), with one extra bit
paying for a division by two, compute the finite and singular parts (H19). Shapiro's lemma and the twisted
transfer (H20)–(H21), with local tame diagrams and Selmer-cone witnesses (H22), carry everything to $A[G]$
without averaging factors.

## Depends on

None.

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): setup (L2834–2857), `ex:arith-finite-heegner`
  (L2858–3410)

## Manuscript check

Checked line by line by AI review. The arithmetic was checked by script, 28 checks: (H1), the matrix span,
(H5), (H6), (H12), (H14)–(H18), the self-cup, local restriction and corestriction, (H11), the transfer (H21)
on a $\operatorname{GL}_2(\mathbb Z/8)$ model and the homotopy identities; the last two with negative
controls. Two small gaps in the statement were filled. The construction of $P_{I,m}$ needs $2^a\mid a_\ell$ and
$2^a\mid\ell+1$ for every $\ell\in I$, not only the new prime, which (H12) for every retained prime gives;
every use chooses $I$ by Chebotarev with (H12). The twisted split norm relation (L3281–3295) needs $\theta$
to factor through $\operatorname{Gal}(H_{f/q}/K)$; its use at (4.5) satisfies this. Not yet checked against
the prints: Cai–Chen–Liu's Theorem 2.15, Elkik (Manin–Drinfeld), Nekovář (4.1.4.1), 8.1.1–8.1.6 and
8.6.2.1–8.6.2.4 (including whether the local data meet those hypotheses), Lang, Silverman and Howard. A TeX
comment just before the subsection (L2832–2833) is an editorial note from the file's assembly; the
proposition's proof is complete as written.
