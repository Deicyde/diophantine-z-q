---
article_id: af_f3af5db39f93c4e0e72fefa1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Even.CentralLengthInput.E7, ZInQ.Manuscript.RC.Even.CentralLengthInput, ZInQ.Manuscript.RC.Even.E7_of_lengths
---

# (E.7): the central valuation before the local terms

Assume the exact sequences of the central calibration at one corank-zero constituent, with their
lengths (`CentralLengthInput`, the manuscript's own steps with standard readings, not proved): the
sequence of [(E.6)](equation-e6-global-h2-length.md); the real map
$\rho:H^1_{\rm glob}\to H^1(\mathbb R,T)$, with $r_1=\ell H^1(\mathbb R,T)$, global torsion of length $g$, and
$K=\ker\rho$ of torsion length $k$ and free index $m$; the positive cone $0\to T^+\to P\to K\to0$ with
$P=H^1(C^+_h)$ of torsion length $p_0$ and saturation index $a_s$; the degree-two positive cone
$0\to\operatorname{coker}\rho\to H^2(C^+_h)\to H^2_{\rm glob}\to H^2(\mathbb R,T)\to0$; the contribution of the
wedge (E.4), $v_2u^{\rm ev}_h(0)=(a_s+1+v_{\rm free}(z)-m)+(p_0-\ell H^2(C^+_h))$; and
$v_2\exp^*z=v_{\rm free}(z)+i+e_2$, where $e_2$ is the valuation of $\exp^*$ on a generator of
$L_2=H^1(\mathbb Q_2,T)/H^1_f(\mathbb Q_2,T)$. Then
$$v_2u^{\rm ev}_h(0)=v_2\exp^*z-s(h)-\sum_vg_v+2g+1-r_1-e_2.\tag{E.7}$$

In Lean the modules are abstract $\mathbb Z_2$-modules, and $v_2u^{\rm ev}_h(0)$, $v_{\rm free}(z)$, $e_2$ and
$v_2\exp^*z$ are integers recorded in the structure. The outputs of Appendix E tie
$v_2u^{\rm ev}_h(0)$ to the central valuation of the scalar and $s(h)$ to the genuine $Ш$; nothing ties
$v_2\exp^*z$ to a dual exponential of Kato's class.

**Proof sketch.** By (E.6), $\ell H^2_{\rm glob}$ is known. Exactness gives
$\ell\operatorname{coker}\rho=r_1-g+k-m$ and $k=p_0+a_s$, and the degree-two cone relates
$\ell H^2(C^+_h)$ to $\ell\operatorname{coker}\rho$, $\ell H^2_{\rm glob}$ and $r_2$. Substituting into the
wedge contribution cancels $m$, $a_s$ and $r_2$.

In the Lean proof of Theorem 5.3 this theorem is not used.

## Depends on

- [Appendix E: the positive complex and the even scalar](README.md)

## Proof depends on

- [(E.6): the length of global $H^2$](equation-e6-global-h2-length.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
