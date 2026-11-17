import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges

/-!
# Lane RC8: Milne, *Modular functions and modular forms*, Theorem 11.19 and Remark 11.18

**Use in the manuscript (11/5 text).** tex L1779–1788: "By [bcdt, Theorem A and Introduction,
conditions (1)–(6)], `E = E_ℓ` is modular. Here `N` denotes its conductor. The modular realization
gives a rational weight-two newform `f` of level `N` and an elliptic quotient `q_f : J₀(N) ↠ A_f` in
the rational isogeny class of `E`; see [milnemf, Theorem 11.19 and Remark 11.18]. Choose a
`ℚ`-isogeny `α : A_f → E` and put `φ = α q_f` and `π(x) = φ([x] - [∞])`. Thus `π(∞) = 0` and, for
`q ∤ N`, `φ T_q = [a_q(f)] φ`."

**The print** (J. S. Milne, *Modular functions and modular forms (Elliptic modular curves)*,
v1.31, March 22, 2017, read in the author's PDF), pp. 116–117:
* p. 116: "Let `E` be an elliptic curve over `ℚ`. Let `N` be its geometric conductor. It has an
  L-series `L(E, s) = ∑ aₙ n^{-s}`. For any prime `m` not dividing `N`, and primitive character
  `χ : (ℤ/mℤ)^× → ℂ^×`, let `Λ_χ(E, s) = N^{s/2} (m/2π)^s Γ(s) ∑ aₙ χ(n) n^{-s}`."
* Conjecture 11.17 (strong Hasse–Weil): "For all `m` prime to `N`, and all primitive Dirichlet
  characters `χ`, `Λ_χ(E, s)` has an analytic continuation of `ℂ`, bounded in vertical strips,
  satisfying the functional equation `Λ_χ(E, s) = ±(g(χ)χ(-N)/g(χ̄)) N^{1-s} Λ_χ̄(E, 2 - s)`."
* "An elliptic curve `E` over `ℚ` is said to be modular if there is a nonconstant map
  `X₀(N) → E` (defined over `ℚ`)."
* Remark 11.18: "... Thus to say that `E` is modular means that there is a surjective homomorphism
  `J₀(N) → E`."
* Theorem 11.19: "An elliptic curve `E` over `ℚ` is modular if and only if it satisfies the strong
  Hasse–Weil conjecture (and in fact, there is a map `X₀(N) → E` with `N` equal to the geometric
  conductor of `E`)." Proof: "the pull-back of `ω` [the Néron differential] to `X₀(N)` can be
  written `f(z)dz` with `f(z)` a cusp form of weight 2 for `Γ₀(N)`, and the Eichler–Shimura theorem
  shows that `Λ(E, s)` is the Mellin transform of `f`."
* Proposition 11.21: elliptic curves admitting a surjection from `X₀(N)` but none from `X₀(M)`,
  `M < N`, correspond to "newforms for `Γ₀(N)` that are eigenforms with rational eigenvalues".

**Statement check and use check.** With BCDT's Theorem A (`E` modular), Remark 11.18 gives
`J₀(N) ↠ E` and Theorem 11.19 gives `N` = the conductor and `L(E, s) = L(f, s)` for a weight-2 cusp
form `f` on `Γ₀(N)`. The manuscript's "newform `f`" is Proposition 11.21 (not in the locator), and
the Hecke equivariance `φ T_q = [a_q(f)] φ` is not in the cited statements (it is the
Eichler–Shimura relation; Version 19 of the manuscript cites Shimura's Theorem 1 for it and replaces
the whole locator: noted DEPARTURE of the later text, not followed). Two misprints in the print's
Conjecture 11.17 (not used): the definition of `Λ_χ` asks for a *prime* `m ∤ N` while 11.17 says
"`m` prime to `N`", and the factor `N^{1-s}` sits beside a `Λ_χ` that already contains `N^{s/2}`; so
the untwisted functional equation is not literally an instance of 11.17 as printed, and is taken
here from the proof of Theorem 11.19 ("`Λ(E, s)` is the Mellin transform of `f`") with Hecke's
functional equation for newforms (proved in the vendored library).

**What is stated.**
* `ModularNewform` (`Newform.lean`, PRINT composite of BCDT Theorem A condition (2), Milne
  Theorem 11.19 and Proposition 11.21): the analytic half of the modular realization — a newform
  `f` of trivial character, weight 2, with `L(f, s) = L(E, s)`.
* `MilneHasseWeil` (below): in the shared vocabulary, `L(E, s)` has an entire continuation with a
  functional equation (`RootNumber E w` for some `w`): the strong Hasse–Weil property at the trivial
  character. `milneHasseWeil_of` (PROVED) derives it from `ModularNewform` and `HasseConvergence`
  through Tau Ceti's proved functional equation of newforms.
* **Not stated (STATED-DEFS):** the geometric half — `X₀(N)` over `ℚ`, `J₀(N)`, the quotient
  `q_f : J₀(N) ↠ A_f`, the `ℚ`-isogeny `α`, `π(x) = φ([x] - [∞])` and `φ T_q = [a_q(f)] φ`. A genuine
  definition needs: modular curves `X₀(N)` as smooth projective curves over `ℚ` (coarse moduli of
  cyclic `N`-isogenies; Deligne–Rapoport), Jacobians of curves over `ℚ` (not in Mathlib), Hecke
  correspondences and their action on `J₀(N)`, and the Abel–Jacobi map at the cusp `∞`. The
  complex-analytic substitute used by the shared blueprint's Cai–Shu–Tian leaf (`φ(τ) = ℘(κ∫f)`)
  is the available stand-in; the Heegner-point lanes consume it.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **The strong Hasse–Weil property at the trivial character** (the analytic content of Milne,
*Modular functions and modular forms* v1.31, Theorem 11.19 and its proof, p. 117, for a modular
elliptic curve, and of BCDT's Theorem A): every elliptic curve over `ℚ` has a root number, i.e.
`L(E, s)` has an entire continuation whose completion satisfies `Λ(2 - s) = w Λ(s)` for some level
`N > 0` (the conductor) and sign `w`. Derived from `ModularNewform` by `milneHasseWeil_of`. -/
def MilneHasseWeil : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ w : ℤ, RootNumber E w

/-- **`MilneHasseWeil` from modularity in newform form** (PROVED, with `HasseConvergence` to move
from Hecke's half-plane `Re s > 2` to `Re s > 3/2`): the newform's entire L-function continues
`L(E, s)` and Tau Ceti's functional equation gives the sign `i² ε_N(f) = -ε_N(f)`. -/
theorem milneHasseWeil_of (hM : ModularNewform) (hH : HasseConvergence) : MilneHasseWeil :=
  fun _ hE => exists_rootNumber hM hH hE

end ZInQ.Manuscript.RC.PrintsAnalytic
