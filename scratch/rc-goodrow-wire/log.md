# rc-goodrow-wire results log

- Merges: 98a68f7e0 (wip/rc-model-target 621cccc1d), 45957b1d0 (main 8e5d680c1). Clean.
- Item 1 docs: 67896e640.
- Finding: `ModelGeneric5.eq_Wint_of_extendsAtkin` needs neither `q.Prime` nor `q ∣ N`; the
  agreement `(ext q hq he).choose = Wint` needs no factorization conversion.
- Fact instance for stage primes: `O7Assemble.stagePrime` (RC/O7Assemble/ActualFamily.lean:19), global.
- SamePlace.lean builds (258s); point_W_choose axioms: propext, Classical.choice, Quot.sound
- Row.lean first build: errors (variables used only in proof need `include`; `StageSamePlace : Type` not `Type 1`; `PreparedParam.projectiveOverQ` not opened). Fixed.
- Row.lean builds (442s). stage_coprime, stageRow, stageRow_closed/_M/_source/_E/_point/_W: axioms propext, Classical.choice, Quot.sound.
- All type equalities in stageRow closed by defeq with no bridge: K = ResidueAt (place s i); Ebar = ReducedEquation (EcurveZ ℓ) p (goodTarget's `ReducedEquation W₀ ell` at W₀ := EcurveZ ℓ); E₀ = (EcurveZ ℓ)⁄ℚ (IsElliptic instance is Prop: goodTarget's `detRational_isElliptic hΔ` vs the variable instance); fixedMap π hQ : Over.mk (X0Model3.model N).overQ ⟶ ..., against rationalSource N = Over.mk (X0Branch.model N).overQ (Assembly.lean already typechecks G at this type); `genericProjection` vs ModelNeron.denseGeneric (as in eq_Wint_of_extendsAtkin).
- Assembly.lean builds first try (50s; PMWire.Assembly deps rebuilt after the main merge). stageRows, oddStagedOfSamePlace: axioms propext, Classical.choice, Quot.sound. No warnings in GoodRowWire files.
- oddStagedOfSamePlace: binders hB, sp, J, relations, cusps, H, hm, refs, ha, hL, hsign; G := stageRows a s π hQ hN hB sp, hcop := stage_coprime s hN hB, R inferred as fun i => LocalIntegers (s.q.stage i).p. No free G, hcop, R (grep of the source: only named-argument substitutions).
