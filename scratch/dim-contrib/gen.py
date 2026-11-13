"""Generate ZInQKernel/Contrib/Dim/{MvPolynomial,Cotangent,SubmersivePresentation,SmoothStalk}.lean
from scratch/curve-infra/CurveInfraAll.lean (whose lines 3-526 are infra-smooth-dim's SmoothStalk.lean
verbatim), renaming declarations Mathlib-style. Proof bodies are unchanged except for renamed references."""
import re, sys, os
root = os.path.dirname(os.path.abspath(__file__)) + '/../..'
src = open(root + '/scratch/curve-infra/CurveInfraAll.lean').read().split('\n')
def L(a, b): return '\n'.join(src[a-1:b])
RENAME = [
    ('height_isMaximal_mvPolynomial', 'height_eq_natCard_of_isMaximal_mvPolynomial'),
    ('spanFinrank_add_card_le', 'spanFinrank_maximalIdeal_add_card_le'),
    ('relCot', 'relationCotangent'),
    ('linearIndependent_relCot', 'linearIndependent_relationCotangent'),
    ('stalk_dim_of_chart', 'ringKrullDim_stalk_of_chart'),
    ('stalk_dim_of_smoothOfRelativeDimension', 'ringKrullDim_stalk_of_smoothOfRelativeDimension'),
    ('exists_stalk_dim_of_smooth', 'exists_ringKrullDim_stalk_of_smooth'),
    ('exists_nbhd_stalk_dim', 'exists_nhds_ringKrullDim_stalk'),
    ('stalk_dim_eq_of_closed', 'ringKrullDim_stalk_eq_of_isClosed'),
    ('topologicalKrullDim_eq_of_smooth', 'topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth'),
    ('stalk_dims_of_section', 'ringKrullDim_stalk_of_section'),
    ('isClosed_of_section', 'isClosed_singleton_of_section'),
]
def ren(s):
    # unused hypothesis `hU : IsAffineOpen U` of stalk_dim_of_chart (dim-contrib statement check)
    s = s.replace("{U : (Spec (CommRingCat.of K)).Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)",
                  "{U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (hV : IsAffineOpen V)")
    s = s.replace("stalk_dim_of_chart f hU hV", "stalk_dim_of_chart f hV")
    s = s.replace("obtain ⟨U, hU, V, hV, hxV, e, h⟩", "obtain ⟨U, -, V, hV, hxV, e, h⟩")
    for a, b in RENAME:
        s = re.sub(r'(?<![\w.])' + re.escape(a) + r'(?![\w])', b, s)
    return s
HDR = """/-!
# {title}

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task infra-smooth-dim, `scratch/infra-smooth-dim/`). Mathlib only.

{body}
-/
"""
GEN = r"""
/-- **Dimension of a smooth `K`-scheme of relative dimension `n`.** If `X` is nonempty and
`X → Spec K` is smooth of relative dimension `n`, then `dim X = n`. (infra-smooth-dim assumed `X`
irreducible; nonempty suffices: every point specializes to a closed point, whose local ring has
dimension `n`.) -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] [Nonempty X] :
    topologicalKrullDim X = n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hdim : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  rw [hdim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun y => ?_
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({y} : Set X))
      ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hyz : z ≤ y := specializes_iff_mem_closure.mpr hz
    calc (Order.coheight y : WithBot ℕ∞) ≤ Order.coheight z := by
          exact_mod_cast Order.coheight_anti hyz
      _ = ringKrullDim (X.presheaf.stalk z) := (ringKrullDim_stalk_eq_coheight z).symm
      _ = n := (ringKrullDim_stalk_of_smoothOfRelativeDimension f n z hzc).1
  · obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X))
      Set.univ_nonempty isClosed_univ.isLocallyClosed
    rw [← (ringKrullDim_stalk_of_smoothOfRelativeDimension f n x hx).1,
      ringKrullDim_stalk_eq_coheight]
    exact Order.coheight_le_krullDim x
"""

def write(name, imports, title, body, pre, content, post=''):
    txt = '\n'.join(imports) + '\n\n' + HDR.format(title=title, body=body) + '\n' + pre + '\n' + ren(content) + '\n' + post + '\nend ZInQ.Contrib.Dim\n'
    open(root + '/ZInQKernel/Contrib/Dim/' + name + '.lean', 'w').write(txt)

write('MvPolynomial', ['import Mathlib'], 'Heights of maximal ideals of polynomial rings over a field',
"""## Main results

* `ZInQ.Contrib.Dim.height_eq_natCard_of_isMaximal_mvPolynomial`: for a field `k`, a finite type
  `ι` and a maximal ideal `M` of `k[x_i : i ∈ ι]`, `ht M = |ι|`.
* `ZInQ.Contrib.Dim.ringKrullDim_mvPolynomial_fin`: `dim k[x_1, ..., x_s] = s`.""",
"namespace ZInQ.Contrib.Dim\n\nopen Ideal\n\n/-- **Every maximal ideal of `k[x_i : i ∈ ι]` has height `|ι|`** (`k` a field, `ι` finite).\nProof by induction on `ι` through `Option`, using `k[x_ι][y] ≅ k[x_{Option ι}]` and\n`ht P = ht (P ∩ k[x_ι]) + 1` for maximal `P` of a polynomial ring over a Jacobson ring. -/",
L(24, 51),
"""
/-- `dim k[x_1, ..., x_s] = s` for a field `k`. -/
theorem ringKrullDim_mvPolynomial_fin (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp
""")

write('Cotangent', ['import Mathlib'], 'Killing part of a minimal generating system lowers the embedding dimension',
"""## Main results

* `ZInQ.Contrib.Dim.spanFinrank_maximalIdeal_add_card_le`: let `ψ : B → C` be a map of local rings,
  `B` Noetherian, with `𝔪_B C = 𝔪_C`, killing `f : σ → 𝔪_B` whose classes in `𝔪_B/𝔪_B²` are
  linearly independent. Then `edim C + |σ| ≤ edim B` (`edim` = minimal number of generators of the
  maximal ideal, `Submodule.spanFinrank`).
* `ZInQ.Contrib.Dim.derivation_mem_of_mem_sq`: a derivation maps `M²` into `M`.""",
"namespace ZInQ.Contrib.Dim\n\nopen Ideal IsLocalRing\n\n/-- **Killing elements with independent cotangent classes lowers the embedding dimension.** If\n`ψ : B → C` (local rings, `B` Noetherian) satisfies `𝔪_B C = 𝔪_C` and kills `f : σ → 𝔪_B`, whose\nclasses in `𝔪_B/𝔪_B²` are linearly independent over `κ(B)`, then\n`spanFinrank 𝔪_C + |σ| ≤ spanFinrank 𝔪_B`. -/",
L(53, 115) + "\n\n/-- A derivation `D : A → A` maps `M²` into `M`. -/\n" + L(119, 128))

write('SubmersivePresentation', ['import ZInQKernel.Contrib.Dim.MvPolynomial', 'import ZInQKernel.Contrib.Dim.Cotangent'],
'Local rings of standard smooth algebras over a field',
"""## Main result

`ZInQ.Contrib.Dim.ringKrullDim_and_spanFinrank_localization`: if `S` has a submersive
presentation `P` over a field `k` (so `S` is standard smooth of relative dimension `P.dimension`)
and `𝔪` is a maximal ideal of `S`, then `S_𝔪` has Krull dimension `P.dimension` and its maximal
ideal is spanned by `P.dimension` elements and no fewer. In particular `S_𝔪` is a regular local
ring of dimension `P.dimension`.

## Proof

Write `S = k[x_ι]/(f_σ)` with invertible Jacobian, and let `M` be the preimage of `𝔪`. Krull's
height theorem and `ht M = |ι|` give `dim S_𝔪 ≥ |ι| - |σ|`. Differentiating a relation
`∑ aᵢ fᵢ ∈ M²` and reducing the Jacobian modulo `M` shows that the `fᵢ` have linearly independent
classes in the cotangent space of `k[x]_M`; so killing them lowers the embedding dimension `|ι|` of
the regular local ring `k[x]_M` by `|σ|`. Finally `dim ≤ edim`.""",
"namespace ZInQ.Contrib.Dim\n\nopen Ideal IsLocalRing\n",
L(132, 320))

write('SmoothStalk', ['import ZInQKernel.Contrib.Dim.SubmersivePresentation'],
'Local rings and dimension of smooth schemes over a field',
"""## Main results

Let `K` be a field and `f : X ⟶ Spec K`.

* `ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension`: if `f` is smooth of
  relative dimension `n` and `x` is a closed point, then `dim 𝒪_{X,x} = n` and `𝔪_x` is spanned by
  `n` elements.
* `ZInQ.Contrib.Dim.isRegularLocalRing_stalk_of_smooth`: if `f` is smooth, the local rings at closed
  points are regular.
* `ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension`: `dim_{κ(x)} 𝔪_x/𝔪_x² = n`
  at closed points.
* `ZInQ.Contrib.Dim.ringKrullDim_stalk_of_section`: the same two facts at a `K`-point.
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`: if `f` is smooth and `X`
  is irreducible, `dim X = dim 𝒪_{X,x} = edim 𝒪_{X,x}` for every closed point `x`.
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension`: if `f` is smooth of
  relative dimension `n` and `X` is nonempty, then `dim X = n`.""",
"namespace ZInQ.Contrib.Dim\n\nopen Ideal IsLocalRing CategoryTheory AlgebraicGeometry\n",
L(331, 514), GEN)
