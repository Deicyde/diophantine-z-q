import ZInQKernel.Contrib.OneProof.R16Thm1

/-! # r16-thm1b: Shimura 1973 Theorem 1 as one row (the constructed triple is `J/I_f J`, with uniqueness)

Task r16-thm1b (round 3 of r16-shimura73, 2026-11-17), report `docs/research/r16-thm1b.md`, scratch
`scratch/r16-thm1b/`.

Input: an AI page read of the print of Shimura 1973 (cited as "AI page read"). Per that read, the print pins
the kernel of the quotient map: p. 525 "`C = Ker(ν)`"; p. 526 `C` is built from the ideal of the Hecke ring
annihilating `f`, intersected with `End(J)`; p. 526 the quotient is unique "up to isomorphisms over `ℚ`"; p. 527
`m = 1` (multiplicity one) from `q`-expansions, which gives the tangent-space clause. So the round-2 glue
`R16Thm1.ShimuraQuotientIsAf` (Shimura's `A` is Diamond–Shurman's `J/I_f J`) is inside the print, up to the
on-the-spot steps listed below, and the round-2 pair of rows `shimuraThm1Printed` + `shimuraQuotientIsAf`
becomes the single row `ShimuraThm1Af` (the lead's ruling (a)).

* `ShimuraThm1Af` (kind consequence, GLUE, steps flagged): there is a triple `(A, ν, θ)` with Shimura's clauses
  (i)–(iii) (`R16Thm1.ShimuraClauses`) and `IsAfQuotient` (`ker ν = I_f J`), unique up to `ν`-compatible
  isomorphism over `ℚ` among triples with (i)–(iii).
* `afShimura_of_thm1Af` (proved): `AfTateLam.AfShimura` from the row (the action clause by
  `R16Thm1.isAfAction_of`).

No `sorry`, no `axiom`. -/

noncomputable section

namespace R16Thm1b

open scoped TensorProduct MatrixGroups ModularForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform IsNormalizedEigenform)
open AfTateLam (IsX1Gen IsHeckeT IsDiamond HeckeFree evF heckeJ KillsIf IsAfQuotient IsAfAction)
open R16Thm1 (ShimuraClauses)

/-- **Shimura 1973, Theorem 1 as printed, with `C = I_f J` and the uniqueness clause** (one row; kind
consequence, GLUE, its steps flagged). G. Shimura, *On the factors of the jacobian variety of a modular function
field*, J. Math. Soc. Japan 25 (1973), 523–544, Theorem 1 (AI page read of the print), at `Γ = Γ₁(N)`. For a
newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ`, the kernel's model `X` of `X₁(N)` (`IsX1Gen`) with Jacobian `J` and
Hecke operators `T_p = ξ_p`, `⟨d⟩` (`IsHeckeT`, `IsDiamond`; transported from Shimura's standard model by
`R16Thm1.BShStandardModel`): `K_f` is finite over `ℚ`, and there are `A` over `ℚ`, `ν : J → A`,
`θ : K_f → End⁰(A)` with
* Shimura's clauses (i)–(iii) (`R16Thm1.ShimuraClauses`: `ν` surjective with connected kernel; `ν ∘ ξ_n =
  θ(a_n) ∘ ν` at `n = p` and `n = p²`, `p ∤ N`, `ξ_{p²} = T_p² − p⟨p⟩`; `dim A = [K_f : ℚ]`);
* `IsAfQuotient` (`ν` kills `I_f J` and is universal for that: `ker ν = I_f J`);
* uniqueness: every `(A', ν', θ')` with (i)–(iii) is `(A, ν)` up to an isomorphism `ψ : A ≅ A'` over `ℚ` with
  `ν ≫ ψ = ν'`.

What the print gives (per the AI page read): the triple constructed as `A = J/C` with `C = Ker(ν)` (p. 525),
`C` built from the ideal of the Hecke ring annihilating `f`, intersected with `End(J)` (p. 526); (i)–(iii)
(dimension and tangent space from `m = 1`, `q`-expansions, p. 527); uniqueness "up to isomorphisms over `ℚ`"
(p. 526).

Steps not printed, ON THE SPOT (each flagged on the row; proofs sketched in `docs/research/r16-thm1b.md` §2):
1. `C = I_f J`: the print's ideal is the kernel of `ρ : 𝕋 ⊗ ℚ → K_f` (`T_n ↦ a_n`); its intersection with
   `End(J)` is the saturation of `I_f = ker(evF) ∩ 𝕋_ℤ`; the saturation and `I_f` give the same abelian
   subvariety `I_f J` (`m • x ∈ I_f` ⇒ `(m x)(J) ⊆ I_f J` and `(m x)(J) = x(J)`); and the print's generators
   `ξ_n` and the kernel's `T_p`, `⟨d⟩` generate the same ring (Hecke relations in both directions:
   `ξ_{p^{k+1}} = ξ_p ξ_{p^k} − p ⟨p⟩ ξ_{p^{k−1}}` for `p ∤ N`, `ξ_{p^k} = ξ_p^k` for `p ∣ N`, `ξ_{mn} = ξ_m ξ_n`
   for coprime `m, n`; and `⟨p⟩ = (ξ_p² − ξ_{p²})/p` with Dirichlet's theorem for `⟨d⟩`).
   `ker ν = I_f J` is then `IsAfQuotient` (`J → J/B` is universal among maps killing `B`).
2. (ii) for all `n` from `n = p, p²`: the competitors in the uniqueness clause are asked (ii) only at `p, p²`
   (`ShimuraClauses`); the same Hecke relations and the multiplicativity of `a_n` give (ii) for every `n`, so the
   clause here is the print's.
3. `ν`-compatible isomorphisms: the print's "unique up to isomorphisms over `ℚ`" is read as an isomorphism
   `ψ` with `ν ≫ ψ = ν'` (both kernels are `C`).
The Euler-factor clause of the print is not in this row (no consumer in the fold; it stays in
`R16Thm1.ShimuraThm1Printed` for `R16Thm1.euler_of_shimura73_li`). Clause (iv) (cotangent space) is dropped as in
round 2 (no `q`-expansion dictionary for `J₁(N)` in the kernel). Misprint (Known issues 1 of the report): in the
`f_σ` sentence before (iv) on p. 526, "`f_σ | T_n = a_n^σ f`" should read "`… = a_n^σ f_σ`". -/
def ShimuraThm1Af : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ (A : AbVar ℚ) (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
          ShimuraClauses f tp δ A ν θ ∧ IsAfQuotient χ f tp δ A ν ∧
          ∀ (A' : AbVar ℚ) (ν' : AbVar.Hom J A') (θ' : coeffField f →+* A'.End0),
            ShimuraClauses f tp δ A' ν' θ' →
              ∃ ψ : AbVar.Hom A A', IsIso ψ.hom ∧ ν.hom ≫ ψ.hom = ν'.hom

/-- **`afShimura` from the one row `ShimuraThm1Af`** (proved): `IsAfQuotient` is in the row; `IsAfAction` from
clause (ii) by `R16Thm1.isAfAction_of` (`T_p` at `n = p`; `⟨d⟩` at `n = p²` via `ξ_{p²} = T_p² − p⟨p⟩` and a
Dirichlet prime `p ≡ d (mod N)`). -/
theorem afShimura_of_thm1Af (h : ShimuraThm1Af) : AfTateLam.AfShimura := by
  intro N χ f h2 hf X _ jX tX hC hX P₀ J aj hJ tp δ htp hδ
  obtain ⟨hfin, A, ν, θ, hcl, hQ, -⟩ := h N χ f h2 hf X jX tX hC hX P₀ J aj hJ tp δ htp hδ
  exact ⟨hfin, A, ν, θ, hQ, R16Thm1.isAfAction_of h2 hf.1 hQ hcl.2.1.1 hcl.2.1.2⟩

/-- **`r16CoreY` with the round-3 suppliers**: B-Sh for `heckeJ1DS`, the one row `ShimuraThm1Af` for
`afShimura`; `afCharpolyDS965` (DS 9.6.5, flagged), Diamond–Shurman 7.6.3 and Mumford as before. -/
theorem r16CoreY_of_thm1Af (hB : R16Thm1.BShStandardModel) (hS : ShimuraThm1Af)
    (h3 : AfTateLam.AfCharpolyDS965) (hI : X1Igusa.IgusaGL2DS) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  AfTateLam.r16CoreY_of_ds965 (R16Thm1.heckeJ1DS_of_bSh hB) (afShimura_of_thm1Af hS) h3 hI hM

end R16Thm1b

end
