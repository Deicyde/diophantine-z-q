# leafq-check results log

Base 67c2daf9. Candidates (leaf-fold4 §2.3 LEAF?): thetaRatiosAlgebraic, qmHauptmodul, x6ConicModel,
y3Connected, cmDescends, gammaStarGen, valenceBoundGammaStar. Source of the statements:
scratch/leaf-fold4/Leaves4.lean (lines: QMHauptmodul 358, ThetaRatiosAlgebraic 43228, X6ConicModel 75669,
Y3Connected 97479, ValenceBoundGammaStar 113443, CMDescends 114469, GammaStarGen 117339).

## GammaStarGen: plan of a direct proof (computations VERIFIED in py/)
- y = i+j ∈ 𝒪 (y² = −1, fixed point of ι(x₄)); pure elements v of 𝒪 with v² = −1 ↔ points of the
  hyperboloid −2b²+3c²−6d² = 1; ⟨v,y⟩ = −2b+3c = cosh d(v,y) (`py/gsg_enum.py`).
- the four nearest orbit points u_k = s_k⁻¹ y s_k, s = x₆, x₆⁻¹, x₆x₄, (x₆x₄)⁻¹ (`py/gsg_words.py`);
  ⟨v,u_k⟩ − ⟨v,y⟩ = b+3d, b−3d, −5b+6c+3d, −5b+6c−3d.
- certificate: 3·nrd(v) − ⟨v,y⟩² = (b+3d)(−5b+6c−3d) + (b−3d)(−5b+6c+3d) (`py/gsg_dir.py`: the
  Dirichlet cone of the four is compact, vertices at cosh = √3, the order-6 points).
- upper sheet: pairY(x y x̄) − nrd x = 12((b−c)²+d²) (`py/gsg_sym.py`).
- base: x commutes with y ⇒ x = a + b y; u = x j x⁻¹ has imJ = 1 + 4b²/N, imK = 2ab/N (N = a²+b²)
  (`py/gsg_norm.py`); integrality forces ab = 0 or a = ±b, i.e. x ∈ ℚ^×⟨x₄⟩.
- normalizer witnesses for x₄, x₆ (`py/gsg_norm.py`).
