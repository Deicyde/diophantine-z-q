# Metric and archimedean evaluation bridge

Author: internal model task `/root/d214_metric_evaluation` (requested Sol61 lane), 2026-11-10. This is an author proposal awaiting a separately authored review. It supplies only Brox v17 lines62–78 and210–251, conditional on the exact integral map and trace-lattice bound specified below. It supplies neither acceptance of those algebraic inputs nor whole-214/256 closure. The immutable manuscript is private commit `a81afd7996a20e6b7bb5e48670418541c036d7aa`; exact whole-file and passage bindings are in SOURCE_USES.json.

## 1. Published normalization and actual Jacobian

Read the final published Javanpeykar2014, §§2.1/2.3, printed pp93–94/97–98, and final von Känel2021 §2.1, printed p5. The former specifies the inner product `(i/2)∫_X ω∧barη`, its determinant metric, and `hFal(X)=Ardeg(det p*ω)/[K:Q]`, equal to stable Faltings height of the Jacobian. The latter defines original relative height using the Néron top-differential line and all embeddings, then defines stable height by semistable extension and proves its extension invariance. Its paragraph after(2.2) explicitly distinguishes the alternative shifted height by `(g/2)log π`. That shifted height is not used here. Sources were acquired from their publishers on2026-11-10; hashes and exact source locations are retained in SOURCE_USES.json.

Apply Javanpeykar's identification to the *same* smooth projective geometrically connected curve `X/K`, genus `g≥1`, and its minimal regular semistable model `p:𝒳→Spec O_K`. Thus `E=H0(𝒳,ω_𝒳/O_K)` with the displayed L² metric has

`Ardeg(E)=[K:Q] hF(Jac X)`.

This is the Jacobian itself, not an isogenous abelian variety, a modular factor, the singular normalization model, or an Arakelov metric on individual cotangent fibres. The relevant metric is on global differentials. Javanpeykar's published statement supplies the integral model identification; it is a theorem input, not a claim that a generic vector-space identification alone identifies lattices.

For an explicit check of the archimedean determinant scalar, choose symplectic integral cycles and normalized holomorphic forms `ω1,…,ωg`; write their period matrix `(1,τ)`. Riemann's bilinear identity gives their Gram matrix `Im τ`. The analytic Jacobian is `C^g/(Z^g+τZ^g)` and Abel–Jacobi pulls `dz_i` to `ω_i`. The positive volume of its fundamental parallelepiped is `det Im τ`, so the squared norm of `dz1∧…∧dzg` in the positive top-form convention is exactly `det Im τ`, also the squared determinant norm of the `ω_i`. The top-form integral uses the usual positive ordering of real pairs; changing between block and interleaved complex wedges accounts for the orientation sign, not a positive metric scalar. No `g!`, `π^g`, polarization degree, or isogeny degree occurs. A Kähler form raised to its gth power would require a factorial, but that is not this norm.

For any further number-field extension `K'/K`, stable height is unchanged. Equivalently the normalized degree for the semistable model over `K'` again equals this same stable height. We need no assertion that the singular base change of a minimal regular model is already regular. In this argument choose one extension that simultaneously makes the curve semistable and splits the finite unramified fibre, then construct its model and E there. The degree in the height formula and the number of complex embeddings are both `[K:Q]`. The auxiliary field is unrelated to the controlled field `L'` in the surface-isogeny argument.

## 2. One global coordinate choice and its analytic bound

Let `π:X→P1_t` be the same degree-d Belyi cover and let its split fibre over2 be `P1,…,Pd`. Characteristic zero implies separability. Riemann–Hurwitz gives `2g−2=−2d+Σ(e_P−1)≤−2d+3(d−1)=d−3`; over each of the three possible branch values the contribution is d minus the nonzero number of geometric points in that fibre. Hence `d>2g−2`. A nonzero regular differential has zero divisor of degree `2g−2`, including g=1 where it has no zeros. Since every `Pj` is unramified, `ω/dt(Pj)=0` is precisely vanishing there. Thus

`ev:E⊗K→K^d`, `ω↦(ω/dt(Pj))j`

has rank g. Some g×g minor is nonzero over K. Fix its coordinate set `I⊂{1,…,d}` **once over K**. Each embedding sends that nonzero minor to a nonzero complex number, so the same I works at every embedding. An embedding permutes the labels of the geometric fibre but does not lose distinctness or unramifiedness. No separately chosen analytic minor is used to define the integral map.

The algebraic lane must supply the actual integral `ev:E→C^vee` for `C=B/(t−2)B`, where B is the normalization algebra over `O_K[t]`. Set `F=pr_I(C^vee)` with the standard Euclidean metric, and use the exact lattice bound `Ardeg(F)≤(1/2)log N disc(C)`. Projection gives the generically invertible integral map `φ:E→F` used here. This packet does not replace F by the maximal order or its trace dual.

At every complex embedding the open disc `D={|t−2|<1/2}` avoids `0,1,∞`. The inverse image consists of d disjoint sheets isomorphic to D. On the sheet through `Pj`, write `ω=f_j(t)dt`. The power-series identity, or the mean-value inequality, gives

`|f_j(2)|²≤4/π ∫_D |f_j(t)|² dxdy≤4/π ||ω||²`,

because `(i/2)dt∧dbar t=dxdy`. For completeness, expansion `f_j(2+z)=Σ a_n z^n` on each smaller disc gives integral `πΣ |a_n|² r^(2n+2)/(n+1)≥πr²|a_0|²`; take `r↑1/2`. The sheets are disjoint, so their positive integrals are parts of the integral on X. This also rules out an unnoticed multiplicity in comparison with the global L² norm.

In a Hermitian orthonormal basis of `E_σ`, the row of the evaluation matrix at j represents the functional `ω↦f_j(2)`. Its squared Euclidean norm is its dual Hermitian norm squared, bounded by `4/π`. Hadamard therefore gives

`||det φ||_σ≤(2/√π)^g`.

Here the target's standard coordinate basis is orthonormal; F's finite-place lattice does not alter its complex metric. One could obtain an operator-norm estimate using disjointness, but the displayed row/Hadamard proof already gives the exact constant consumed in v17. No strengthening is substituted downstream.

## 3. Arithmetic degree, signs and consumer

The determinant is a nonzero integral section `s` of `L=det(F)⊗det(E)^−1`. Its finite divisor is effective. The rank-one degree definition gives exactly

`Ardeg(F)−Ardeg(E)=log #(L/O_K s)−Σ_σ log||s||_σ`.

Thus `Ardeg(E)≤Ardeg(F)+Σ_σ log||det φ||_σ`. This sign can also be checked by multiplication by m on the standard rank-one lattice: the finite term and the log norm both equal `[K:Q]log|m|`. Inserting the two bounds and dividing by `[K:Q]` proves precisely

`hF(Jac X)≤log N disc(C)/(2[K:Q])+g log(2/√π)`.

The small positive constant is `log(2/√π)=(1/2)log(4/π)`; there is no extra `g log g`, square-norm factor two, or half-weight for a conjugate embedding pair.

For the modular consumer, substitute *the same* `X=X_H=X_1(N)/H`, `H⊃{−1}`, `t=j/1728`, `J_H=Jac X_H`, `d=d_H`, and `g=g_H` from Brox354–401. The modular-model and different lanes must establish that cover and the normalized discriminant bound `d_H(log12+log N+2log d_H)`. The result is exactly Brox453–488/H0.3, with no convention change when used in height/PROOF.md H2–H4. In the actual non-CM realization `H=ker ε` with ε even; the actual Jacobian contains an abelian surface over L', so `g_H≥2`. That identity is not supplied by this metric lane.

There is no large-level, torsion-free-congruence-subgroup, genus≥2, or absence-of-elliptic-points assumption in the evaluation proof. Every positive-genus modular curve for every positive N is covered, including genus1. Possible elliptic/cusp ramification is confined to the three omitted branch values; it cannot affect the disc over2. N=1 and N=2 give genus-zero curves (the covers have degrees1 and3); the modular section's explicit positive-genus hypothesis excludes them. Any other genus-zero level is excluded by that same hypothesis, and cannot be the actual surface-factor consumer since a zero Jacobian has no surface factor. No classification of small N is needed to cover all allowed positive-genus cases. If one extends the displayed modular inequality to genus0, its left side is `hF(0)=0` and its right side is nonnegative, but that extension is not used in this contract.

## 4. Scope and incorporation

This is a source/application explanation of an already written argument; no numerical repair or manuscript edit is proposed. Historical justification was found in the actual earlier source assessment and report, including their withdrawn normalization concern, and in the current frozen v17 proof. We do not call this a newly repaired gap. The explanation can be incorporated by an exact pointer from an additive height-closure packet. Its author status, the still-separate algebraic/different inputs, and the need for fresh non-author acceptance must remain explicit. The 214 existence and the proposed256 work both consume the same full-family height supplier; the proof here is not restricted to a distinguished parameter β.
