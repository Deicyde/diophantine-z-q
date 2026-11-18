# Exact statement and axiom audit
Source module: `ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget`.
Verified source SHA256: `67b2567ab86c69a15d5ccc0d4c314fe6ee978cfe85f0c869da7237c5bcbfd837`.
Single-file verification succeeded. Every one of the 56 named theorems, including private helpers, and 20 proof-producing definitions was checked. The union of axioms is `propext`, `Classical.choice`, and `Quot.sound`; there are no other axioms. Eight style/unused-tactic warnings were emitted, with no errors.
These are conditional theorems. The source-duality, genuine cochain/model, retained-diagram and arithmetic identification inputs are explicit; this audit is not an unconditional arithmetic instantiation or a proof of the cited printed theorems.
The statement and axiom text below is copied verbatim from the successful compiler output. Private helper identifiers are the compiler-generated names of this public source module, not external execution identifiers.

## 1. `singularKerIso`

def; private helper.

```lean
@singularKerIso : {R : Type} →
  [inst : CommRing R] →
    (X Y : Matrix (Fin 2) (Fin 2) R) →
      kernel ((singularCx X Y).d 1 2) ≅ kernel (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singularKerIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 2. `singularCokerIso`

def; private helper.

```lean
@singularCokerIso : {R : Type} →
  [inst : CommRing R] →
    (X Y : Matrix (Fin 2) (Fin 2) R) →
      cokernel ((singularCx X Y).d 1 2) ≅ cokernel (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singularCokerIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 3. `singularH1Iso`

def; private helper.

```lean
@singularH1Iso : {R : Type} →
  [inst : CommRing R] →
    (X Y : Matrix (Fin 2) (Fin 2) R) → homology (singularCx X Y) 1 ≅ ↧↥(X.mulVecLin.prodMap Y.mulVecLin).ker
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singularH1Iso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 4. `singularH2QuotIso`

def; private helper.

```lean
@singularH2QuotIso : {R : Type} →
  [inst : CommRing R] →
    (X Y : Matrix (Fin 2) (Fin 2) R) →
      homology (singularCx X Y) 2 ≅ ↧(((Fin 2 → R) × (Fin 2 → R)) ⧸ (X.mulVecLin.prodMap Y.mulVecLin).range)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singularH2QuotIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 5. `quotientProdEquiv`

def; private helper.

```lean
@quotientProdEquiv : {R : Type} →
  [inst : CommRing R] →
    {A B : Type} →
      [inst_1 : AddCommGroup A] →
        [inst_2 : Module R A] →
          [inst_3 : AddCommGroup B] →
            [inst_4 : Module R B] →
              (f : A →ₗ[R] A) → (g : B →ₗ[R] B) → ((A × B) ⧸ (f.prodMap g).range) ≃ₗ[R] (A ⧸ f.range) × B ⧸ g.range
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.quotientProdEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 6. `singularH2Equiv`

def; public.

```lean
@singularH2Equiv : {R : Type} →
  [inst : CommRing R] → (X Y : Matrix (Fin 2) (Fin 2) R) → ↑(homology (singularCx X Y) 2) ≃ₗ[R] singularJ X Y
```

```text
'ZInQ.Contrib.RC53Assist.Budget.singularH2Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 7. `singular_homology_zero`

theorem; private helper.

```lean
@singular_homology_zero : ∀ {R : Type} [inst : CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) (n : ℤ),
  n ≠ 1 → n ≠ 2 → Subsingleton ↑(homology (singularCx X Y) n)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singular_homology_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 8. `singular_h1_zero`

theorem; private helper.

```lean
singular_h1_zero : ∀ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]),
  X.det ≠ 0 → Y.det ≠ 0 → Subsingleton ↑(homology (singularCx X Y) 1)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singular_h1_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 9. `coker_isTorsion`

theorem; private helper.

```lean
@coker_isTorsion : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] (X : Matrix n n ℤ_[2]),
  X.det ≠ 0 → Module.IsTorsion ℤ_[2] ((n → ℤ_[2]) ⧸ X.mulVecLin.range)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.coker_isTorsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 10. `singularJ_isTorsion`

theorem; private helper.

```lean
singularJ_isTorsion : ∀ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]),
  X.det ≠ 0 → Y.det ≠ 0 → Module.IsTorsion ℤ_[2] (singularJ X Y)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singularJ_isTorsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 11. `functionExact_of_shortComplex`

theorem; private helper.

```lean
@functionExact_of_shortComplex : ∀ {R : Type} [inst : CommRing R] (S : ShortComplex (ModuleCat R)),
  S.Exact → Function.Exact ⇑(ModuleCat.Hom.hom S.f) ⇑(ModuleCat.Hom.hom S.g)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.functionExact_of_shortComplex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 12. `injective_of_exact_zero_left`

theorem; private helper.

```lean
@injective_of_exact_zero_left : ∀ {R : Type} [inst : CommRing R] {A B C : Type} [inst_1 : AddCommGroup A]
  [inst_2 : Module R A] [Subsingleton A] [inst_4 : AddCommGroup B] [inst_5 : Module R B] [inst_6 : AddCommGroup C]
  [inst_7 : Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C), Function.Exact ⇑f ⇑g → Function.Injective ⇑g
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.injective_of_exact_zero_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 13. `surjective_of_exact_zero_right`

theorem; private helper.

```lean
@surjective_of_exact_zero_right : ∀ {R : Type} [inst : CommRing R] {A B C : Type} [inst_1 : AddCommGroup A]
  [inst_2 : Module R A] [inst_3 : AddCommGroup B] [inst_4 : Module R B] [inst_5 : AddCommGroup C] [inst_6 : Module R C]
  [Subsingleton C] (f : A →ₗ[R] B) (g : B →ₗ[R] C), Function.Exact ⇑f ⇑g → Function.Surjective ⇑f
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.surjective_of_exact_zero_right' depends on axioms: [propext]
```

## 14. `exact_change_middle`

theorem; private helper.

```lean
@exact_change_middle : ∀ {R : Type} [inst : CommRing R] {A B C B' : Type} [inst_1 : AddCommGroup A]
  [inst_2 : Module R A] [inst_3 : AddCommGroup B] [inst_4 : Module R B] [inst_5 : AddCommGroup C] [inst_6 : Module R C]
  [inst_7 : AddCommGroup B'] [inst_8 : Module R B'] (f : A →ₗ[R] B) (g : B →ₗ[R] C),
  Function.Exact ⇑f ⇑g → ∀ (e : B' ≃ₗ[R] B), Function.Exact ⇑(↑e.symm ∘ₗ f) ⇑(g ∘ₗ ↑e)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.exact_change_middle' depends on axioms: [propext,
 Quot.sound]
```

## 15. `exact_change_source`

theorem; private helper.

```lean
@exact_change_source : ∀ {R : Type} [inst : CommRing R] {A B C A' : Type} [inst_1 : AddCommGroup A]
  [inst_2 : Module R A] [inst_3 : AddCommGroup B] [inst_4 : Module R B] [inst_5 : AddCommGroup C] [inst_6 : Module R C]
  [inst_7 : AddCommGroup A'] [inst_8 : Module R A'] (f : A →ₗ[R] B) (g : B →ₗ[R] C),
  Function.Exact ⇑f ⇑g → ∀ (e : A' ≃ₗ[R] A), Function.Exact ⇑(f ∘ₗ ↑e) ⇑g
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.exact_change_source' depends on axioms: [propext,
 Quot.sound]
```

## 16. `exact_change_target`

theorem; private helper.

```lean
@exact_change_target : ∀ {R : Type} [inst : CommRing R] {A B C C' : Type} [inst_1 : AddCommGroup A]
  [inst_2 : Module R A] [inst_3 : AddCommGroup B] [inst_4 : Module R B] [inst_5 : AddCommGroup C] [inst_6 : Module R C]
  [inst_7 : AddCommGroup C'] [inst_8 : Module R C'] (f : A →ₗ[R] B) (g : B →ₗ[R] C),
  Function.Exact ⇑f ⇑g → ∀ (e : C ≃ₗ[R] C'), Function.Exact ⇑f ⇑(↑e ∘ₗ g)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.exact_change_target' depends on axioms: [propext,
 Quot.sound]
```

## 17. `finrank_eq_of_exact_torsion`

theorem; private helper.

```lean
@finrank_eq_of_exact_torsion : ∀ {R : Type} [inst : CommRing R] [IsDomain R] {A B C : Type} [inst_2 : AddCommGroup A]
  [inst_3 : Module R A] [inst_4 : AddCommGroup B] [inst_5 : Module R B] [inst_6 : AddCommGroup C] [inst_7 : Module R C]
  (f : A →ₗ[R] B) (g : B →ₗ[R] C),
  Function.Injective ⇑f → Function.Exact ⇑f ⇑g → Module.IsTorsion R C → Module.finrank R A = Module.finrank R B
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.finrank_eq_of_exact_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 18. `length_coker_eq_ord_det`

theorem; private helper.

```lean
@length_coker_eq_ord_det : ∀ {R : Type} [inst : CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {n : Type}
  [inst_3 : Fintype n] [inst_4 : DecidableEq n] (X : Matrix n n R),
  X.det ≠ 0 → Module.length R ((n → R) ⧸ X.mulVecLin.range) = Ring.ord R X.det
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.length_coker_eq_ord_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 19. `length_singularJ`

theorem; private helper.

```lean
length_singularJ : ∀ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]),
  X.det ≠ 0 → Y.det ≠ 0 → Module.length ℤ_[2] (singularJ X Y) = ↑(X.det.valuation + Y.det.valuation)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.length_singularJ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 20. `singularBounds_of_det`

theorem; public.

```lean
singularBounds_of_det : ∀ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (cE : ℕ),
  X.det ≠ 0 → Y.det ≠ 0 → X.det.valuation ≤ cE → Y.det.valuation ≤ cE → SingularBounds X Y cE
```

```text
'ZInQ.Contrib.RC53Assist.Budget.singularBounds_of_det' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 21. `singularBounds_of_retained`

theorem; public.

```lean
singularBounds_of_retained : ∀ (X₀ Y₀ X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (cE : ℕ),
  (∀ (i j : Fin 2), X₀ i j - X i j ∈ Ideal.span {2 ^ (cE + 1)}) →
    (∀ (i j : Fin 2), Y₀ i j - Y i j ∈ Ideal.span {2 ^ (cE + 1)}) →
      X₀.det ≠ 0 → Y₀.det ≠ 0 → X₀.det.valuation ≤ cE → Y₀.det.valuation ≤ cE → SingularBounds X Y cE
```

```text
'ZInQ.Contrib.RC53Assist.Budget.singularBounds_of_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 22. `singular_finiteDimensional`

theorem; private helper.

```lean
@singular_finiteDimensional : ∀ {k : Type} [inst : Field k] (X Y : Matrix (Fin 2) (Fin 2) k) (n : ℤ),
  FiniteDimensional k ↑(homology (singularCx X Y) n)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singular_finiteDimensional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 23. `residual_singular_bound`

theorem; public.

```lean
@residual_singular_bound : ∀ {k : Type} [inst : Field k] (X Y : Matrix (Fin 2) (Fin 2) k),
  ∑ n, Module.finrank k ↑(homology (singularCx X Y) ↑↑n) ≤ 8
```

```text
'ZInQ.Contrib.RC53Assist.Budget.residual_singular_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 24. `isTorsion_of_length_le`

theorem; private helper.

```lean
@isTorsion_of_length_le : ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : Module ℤ_[2] M] (m : ℕ),
  Module.length ℤ_[2] M ≤ ↑m → Module.IsTorsion ℤ_[2] M
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.isTorsion_of_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 25. `budgetInputsAt_of_rankless`

theorem; public.

```lean
@budgetInputsAt_of_rankless : ∀ {S : Type} [inst : CommRing S] (B : SmithBlocks S OO) (dK hK cE tK : ℕ),
  ∑ k, Module.finrank ℤ_[2] (centralCx B fr₀ ↑k) ≤ 2 * dK + 12 →
    ∀ {H1C H2C J H3C : Type} [inst_1 : AddCommGroup H1C] [inst_2 : Module ℤ_[2] H1C] [inst_3 : AddCommGroup H2C]
      [inst_4 : Module ℤ_[2] H2C] [inst_5 : AddCommGroup J] [inst_6 : Module ℤ_[2] J] [inst_7 : AddCommGroup H3C]
      [inst_8 : Module ℤ_[2] H3C] (e : centralH B fr₀ 1 ≃ₗ[ℤ_[2]] H1C) (i : H2C →ₗ[ℤ_[2]] centralH B fr₀ 2)
      (j : centralH B fr₀ 2 →ₗ[ℤ_[2]] J) (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] centralH B fr₀ 3),
      Function.Injective ⇑i ∧
          Function.Exact ⇑i ⇑j ∧ Function.Exact ⇑j ⇑δ ∧ Function.Exact ⇑δ ⇑l ∧ Function.Surjective ⇑l →
        Module.length ℤ_[2] ↥(Submodule.torsion ℤ_[2] H1C) = ↑tK →
          Module.length ℤ_[2] H3C = ↑tK →
            Module.length ℤ_[2] ↥(Submodule.torsion ℤ_[2] H2C) = ↑hK →
              Module.length ℤ_[2] J ≤ 2 * ↑cE → BudgetInputsAt B fr₀ dK hK cE tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_of_rankless' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 26. `quotientEquivOfSurjective`

def; private helper.

```lean
@quotientEquivOfSurjective : {R : Type} →
  [inst : CommRing R] →
    {M N : Type} →
      [inst_1 : AddCommGroup M] →
        [inst_2 : Module R M] →
          [inst_3 : AddCommGroup N] →
            [inst_4 : Module R N] → (f : M →ₗ[R] N) → Function.Surjective ⇑f → (M ⧸ f.ker) ≃ₗ[R] N
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.quotientEquivOfSurjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 27. `linearHomologyQuotEquiv`

def; private helper.

```lean
@linearHomologyQuotEquiv : {R : Type} →
  [inst : CommRing R] →
    (S : ShortComplex (ModuleCat R)) →
      (↥(ModuleCat.Hom.hom S.g).ker ⧸ bdrySub (ModuleCat.Hom.hom S.f) (ModuleCat.Hom.hom S.g)) ≃ₗ[R] ↑S.homology
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.linearHomologyQuotEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 28. `relationHomologyQuotEquiv`

def; private helper.

```lean
@relationHomologyQuotEquiv : {R : Type} →
  [inst : CommRing R] →
    (A : GCx R) →
      (i' i j : ℤ) →
        (hi : i' + 1 = i) →
          (hj : i + 1 = j) → (↥(A.d i j hj).ker ⧸ bdrySub (A.d i' i hi) (A.d i j hj)) ≃ₗ[R] ↑(homology A.toCC i)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.relationHomologyQuotEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 29. `dualRestrict`

def; private helper.

```lean
@dualRestrict : {k : Type} →
  [inst : CommRing k] →
    {U V W : Type} →
      [inst_1 : AddCommGroup U] →
        [inst_2 : Module k U] →
          [inst_3 : AddCommGroup V] →
            [inst_4 : Module k V] →
              [inst_5 : AddCommGroup W] →
                [inst_6 : Module k W] →
                  (f : U →ₗ[k] V) → (g : V →ₗ[k] W) → ↥f.dualMap.ker →ₗ[k] Module.Dual k (↥g.ker ⧸ bdrySub f g)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.dualRestrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 30. `dualRestrict_surjective`

theorem; private helper.

```lean
@dualRestrict_surjective : ∀ {k : Type} [inst : CommRing k] {U V W : Type} [inst_1 : AddCommGroup U]
  [inst_2 : Module k U] [inst_3 : AddCommGroup V] [inst_4 : Module k V] [inst_5 : AddCommGroup W] [inst_6 : Module k W],
  IsField k → ∀ (f : U →ₗ[k] V) (g : V →ₗ[k] W), (∀ (a : U), g (f a) = 0) → Function.Surjective ⇑(dualRestrict f g)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.dualRestrict_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 31. `ker_dualRestrict`

theorem; private helper.

```lean
@ker_dualRestrict : ∀ {k : Type} [inst : CommRing k] {U V W : Type} [inst_1 : AddCommGroup U] [inst_2 : Module k U]
  [inst_3 : AddCommGroup V] [inst_4 : Module k V] [inst_5 : AddCommGroup W] [inst_6 : Module k W],
  IsField k → ∀ (f : U →ₗ[k] V) (g : V →ₗ[k] W), (dualRestrict f g).ker = bdrySub g.dualMap f.dualMap
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.ker_dualRestrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 32. `ker_zsmul_eq`

theorem; private helper.

```lean
@ker_zsmul_eq : ∀ {k : Type} [inst : CommRing k] {A B : Type} [inst_1 : AddCommGroup A] [inst_2 : Module k A]
  [inst_3 : AddCommGroup B] [inst_4 : Module k B] (L : A →ₗ[k] B) {c : ℤ}, c * c = 1 → (c • L).ker = L.ker
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.ker_zsmul_eq' depends on axioms: [propext,
 Quot.sound]
```

## 33. `range_zsmul_eq`

theorem; private helper.

```lean
@range_zsmul_eq : ∀ {k : Type} [inst : CommRing k] {A B : Type} [inst_1 : AddCommGroup A] [inst_2 : Module k A]
  [inst_3 : AddCommGroup B] [inst_4 : Module k B] (L : A →ₗ[k] B) {c : ℤ}, c * c = 1 → (c • L).range = L.range
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.range_zsmul_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 34. `neg_sgn_square`

theorem; private helper.

```lean
neg_sgn_square : ∀ (n : ℤ), -sgn n * -sgn n = 1
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.neg_sgn_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 35. `dualHomologyEquiv`

def; public.

```lean
@dualHomologyEquiv : {k : Type} →
  [inst : CommRing k] →
    IsField k → (A : GCx k) → (m n : ℤ) → ↑(homology (dualCx A m).toCC n) ≃ₗ[k] Module.Dual k ↑(homology A.toCC (m - n))
```

```text
'ZInQ.Contrib.RC53Assist.Budget.dualHomologyEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 36. `residualKummerProfile_of_selfDuality`

theorem; public.

```lean
@residualKummerProfile_of_selfDuality : ∀ {k : Type} [inst : CommRing k],
  IsField k →
    ∀ (C : GCx k) (γ : C.toCC ⟶ (dualCx C 3).toCC),
      QuasiIso γ →
        ∀ (e0 : ↑(homology C.toCC 0) ≃ₗ[k] Fin 2 → k) [Module.Finite k ↑(homology C.toCC 1)], ResidualKummerProfile C
```

```text
'ZInQ.Contrib.RC53Assist.Budget.residualKummerProfile_of_selfDuality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 37. `ArithmeticComparison.quotient_zero`

theorem; private helper.

```lean
@ArithmeticComparison.quotient_zero : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) {cE : ℕ},
  SingularBounds A.X A.Y cE → ∀ (n : ℤ), n = 0 ∨ n = 1 ∨ n = 3 → Subsingleton ↑(homology A.integral.X₃ n)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.quotient_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 38. `ArithmeticComparison.exact_sequence`

theorem; public.

```lean
@ArithmeticComparison.exact_sequence : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) (cE : ℕ),
  SingularBounds A.X A.Y cE →
    Function.Injective ⇑A.i ∧
      Function.Exact ⇑A.i ⇑A.j ∧ Function.Exact ⇑A.j ⇑A.delta ∧ Function.Exact ⇑A.delta ⇑A.l ∧ Function.Surjective ⇑A.l
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.exact_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 39. `ArithmeticComparison.h1Equiv`

def; public.

```lean
@ArithmeticComparison.h1Equiv : {S : Type} →
  [inst : CommRing S] →
    {B : SmithBlocks S OO} →
      (A : ArithmeticComparison B) →
        (cE : ℕ) → SingularBounds A.X A.Y cE → centralH B fr₀ 1 ≃ₗ[ℤ_[2]] ↑(homology A.integral.X₁ 1)
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.h1Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 40. `ArithmeticComparison.singular_length`

theorem; public.

```lean
@ArithmeticComparison.singular_length : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) (cE : ℕ),
  SingularBounds A.X A.Y cE → Module.length ℤ_[2] ↑(homology A.integral.X₃ 2) ≤ 2 * ↑cE
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.singular_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 41. `residuallyMinimal_of_positive`

theorem; public.

```lean
@residuallyMinimal_of_positive : ∀ {S : Type} [inst : CommRing S] (B : SmithBlocks S OO),
  (∀ (i : ℕ) (j : Fin (B.m i)), 1 ≤ (B.s i j).valuation) → ResiduallyMinimal B
```

```text
'ZInQ.Contrib.RC53Assist.Budget.residuallyMinimal_of_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 42. `torsionMap_injective`

theorem; private helper.

```lean
@torsionMap_injective : ∀ {R : Type} [inst : CommRing R] {M N : Type} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
  [inst_3 : AddCommGroup N] [inst_4 : Module R N] (f : M →ₗ[R] N),
  Function.Injective ⇑f → Function.Injective ⇑(torsionMap f)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.torsionMap_injective' depends on axioms: [propext,
 Quot.sound]
```

## 43. `ArithmeticComparison.rank_budget`

theorem; public.

```lean
@ArithmeticComparison.rank_budget : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B),
  ResiduallyMinimal B →
    ResidualKummerProfile A.ordinaryRed → ∑ n, Module.finrank ℤ_[2] (centralCx B fr₀ ↑n) ≤ 2 * A.dK + 12
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.rank_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 44. `ArithmeticComparison.length_parameters`

theorem; public.

```lean
@ArithmeticComparison.length_parameters : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) (cE : ℕ),
  SingularBounds A.X A.Y cE →
    Module.length ℤ_[2] ↥(Submodule.torsion ℤ_[2] ↑(homology A.integral.X₁ 1)) = ↑A.tK ∧
      Module.length ℤ_[2] ↥(Submodule.torsion ℤ_[2] ↑(homology A.integral.X₁ 2)) = ↑A.hK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.length_parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 45. `budgetInputsAt_of_comparison`

theorem; public.

```lean
@budgetInputsAt_of_comparison : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (cE : ℕ),
  ResiduallyMinimal B →
    ResidualKummerProfile A.ordinaryRed →
      SingularBounds A.X A.Y cE → IntegralKummerLengthComparison A.integral.X₁ → BudgetInputsAt B fr₀ A.dK A.hK cE A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_of_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 46. `budgetInputsAt_of_selfDuality`

theorem; public.

```lean
@budgetInputsAt_of_selfDuality : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (cE : ℕ),
  ResiduallyMinimal B →
    ∀ (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC),
      QuasiIso γ →
        ∀ (e0 : ↑(homology A.ordinaryRed.toCC 0) ≃ₗ[ZMod 2] Fin 2 → ZMod 2)
          [Module.Finite (ZMod 2) ↑(homology A.ordinaryRed.toCC 1)],
          SingularBounds A.X A.Y cE →
            IntegralKummerLengthComparison A.integral.X₁ → BudgetInputsAt B fr₀ A.dK A.hK cE A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_of_selfDuality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 47. `budgetInputsAt_of_retained`

theorem; public.

```lean
@budgetInputsAt_of_retained : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (cE : ℕ),
  ResiduallyMinimal B →
    ∀ (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC),
      QuasiIso γ →
        ∀ (e0 : ↑(homology A.ordinaryRed.toCC 0) ≃ₗ[ZMod 2] Fin 2 → ZMod 2)
          [Module.Finite (ZMod 2) ↑(homology A.ordinaryRed.toCC 1)] (X₀ Y₀ : Matrix (Fin 2) (Fin 2) ℤ_[2]),
          (∀ (i j : Fin 2), X₀ i j - A.X i j ∈ Ideal.span {2 ^ (cE + 1)}) →
            (∀ (i j : Fin 2), Y₀ i j - A.Y i j ∈ Ideal.span {2 ^ (cE + 1)}) →
              X₀.det ≠ 0 →
                Y₀.det ≠ 0 →
                  X₀.det.valuation ≤ cE →
                    Y₀.det.valuation ≤ cE →
                      IntegralKummerLengthComparison A.integral.X₁ → BudgetInputsAt B fr₀ A.dK A.hK cE A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_of_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 48. `ArithmeticComparison.free_ranks`

theorem; public.

```lean
@ArithmeticComparison.free_ranks : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (cE : ℕ),
  SingularBounds A.X A.Y cE →
    Module.finrank ℤ_[2] ↑(homology A.integral.X₁ 1) = 1 ∧ Module.finrank ℤ_[2] ↑(homology A.integral.X₁ 2) = 1
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.free_ranks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 49. `ArithmeticComparison.smith_budget`

theorem; public.

```lean
@ArithmeticComparison.smith_budget : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) (cE : ℕ),
  (∀ (i : ℕ), 3 ≤ i → i < B.n → B.m i = 0) →
    ResiduallyMinimal B →
      ResidualKummerProfile A.ordinaryRed →
        SingularBounds A.X A.Y cE →
          IntegralKummerLengthComparison A.integral.X₁ → B.mTot ≤ A.dK + 5 ∧ B.hSmith ≤ A.hK + 2 * cE + 2 * A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.smith_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 50. `ArithmeticComparison.parameters_eq`

theorem; public.

```lean
@ArithmeticComparison.parameters_eq : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) {S' : Type} [inst_1 : CommRing S'] {B' : SmithBlocks S' OO}
  (A' : ArithmeticComparison B') (e1 : ↑(homology A.integral.X₁ 1) ≃ₗ[ℤ_[2]] ↑(homology A'.integral.X₁ 1))
  (e2 : ↑(homology A.integral.X₁ 2) ≃ₗ[ℤ_[2]] ↑(homology A'.integral.X₁ 2))
  (er : ↑(homology A.ordinaryRed.toCC 1) ≃ₗ[ZMod 2] ↑(homology A'.ordinaryRed.toCC 1)),
  A.dK = A'.dK ∧ A.hK = A'.hK ∧ A.tK = A'.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.ArithmeticComparison.parameters_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 51. `GenuineComparison.toArithmetic`

def; public.

```lean
@GenuineComparison.toArithmetic : {K : Type} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      {supp : Set (HeightOneSpectrum (𝓞 K))} →
        {T : Type} →
          [inst_2 : AddCommGroup T] →
            [inst_3 : Module ℤ_[2] T] →
              [inst_4 : DistribMulAction (GKS K supp) T] →
                [inst_5 : SMulCommClass (GKS K supp) ℤ_[2] T] →
                  [inst_6 : TopologicalSpace T] →
                    [inst_7 : ContinuousAdd T] →
                      [inst_8 : ContinuousConstSMul ℤ_[2] T] →
                        [inst_9 : ContinuousSMul (GKS K supp) T] →
                          {W : Type} →
                            [inst_10 : AddCommGroup W] →
                              [inst_11 : Module (ZMod 2) W] →
                                [inst_12 : DistribMulAction (GKS K supp) W] →
                                  [inst_13 : SMulCommClass (GKS K supp) (ZMod 2) W] →
                                    [inst_14 : TopologicalSpace W] →
                                      [inst_15 : DiscreteTopology W] →
                                        [inst_16 : ContinuousSMul (GKS K supp) W] →
                                          {S : Type} →
                                            [inst_17 : CommRing S] →
                                              {B : SmithBlocks S OO} →
                                                {Δ Δp : GaloisLocalConditions K supp ℤ_[2] T} →
                                                  {Δr Δrp : GaloisLocalConditions K supp (ZMod 2) W} →
                                                    {F : GaloisCondInclusion K supp ℤ_[2] T Δ Δp} →
                                                      {Fr : GaloisCondInclusion K supp (ZMod 2) W Δr Δrp} →
                                                        GenuineComparison K supp T W B Δ Δp Δr Δrp F Fr →
                                                          ArithmeticComparison B
```

```text
'ZInQ.Contrib.RC53Assist.Budget.GenuineComparison.toArithmetic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 52. `GenuineComparison.budgetInputsAt`

theorem; public.

```lean
@GenuineComparison.budgetInputsAt : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {supp : Set (HeightOneSpectrum (𝓞 K))} {T : Type} [inst_2 : AddCommGroup T] [inst_3 : Module ℤ_[2] T]
  [inst_4 : DistribMulAction (GKS K supp) T] [inst_5 : SMulCommClass (GKS K supp) ℤ_[2] T] [inst_6 : TopologicalSpace T]
  [inst_7 : ContinuousAdd T] [inst_8 : ContinuousConstSMul ℤ_[2] T] [inst_9 : ContinuousSMul (GKS K supp) T] {W : Type}
  [inst_10 : AddCommGroup W] [inst_11 : Module (ZMod 2) W] [inst_12 : DistribMulAction (GKS K supp) W]
  [inst_13 : SMulCommClass (GKS K supp) (ZMod 2) W] [inst_14 : TopologicalSpace W] [inst_15 : DiscreteTopology W]
  [inst_16 : ContinuousSMul (GKS K supp) W] {S : Type} [inst_17 : CommRing S] {B : SmithBlocks S OO}
  {Δ Δp : GaloisLocalConditions K supp ℤ_[2] T} {Δr Δrp : GaloisLocalConditions K supp (ZMod 2) W}
  {F : GaloisCondInclusion K supp ℤ_[2] T Δ Δp} {Fr : GaloisCondInclusion K supp (ZMod 2) W Δr Δrp}
  (G : GenuineComparison K supp T W B Δ Δp Δr Δrp F Fr) (cE : ℕ),
  ResiduallyMinimal B →
    ∀
      (γ :
        (selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC ⟶
          (dualCx (selCx (galoisSelData K supp (ZMod 2) W Δr)) 3).toCC),
      QuasiIso γ →
        ∀ (e0 : ↑(homology (selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC 0) ≃ₗ[ZMod 2] Fin 2 → ZMod 2)
          [Module.Finite (ZMod 2) ↑(homology (selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC 1)]
          (X₀ Y₀ : Matrix (Fin 2) (Fin 2) ℤ_[2]),
          (∀ (i j : Fin 2), X₀ i j - G.X i j ∈ Ideal.span {2 ^ (cE + 1)}) →
            (∀ (i j : Fin 2), Y₀ i j - G.Y i j ∈ Ideal.span {2 ^ (cE + 1)}) →
              X₀.det ≠ 0 →
                Y₀.det ≠ 0 →
                  X₀.det.valuation ≤ cE →
                    Y₀.det.valuation ≤ cE →
                      IntegralKummerLengthComparison (selCx (galoisSelData K supp ℤ_[2] T Δ)).toCC →
                        BudgetInputsAt B fr₀ G.toArithmetic.dK G.toArithmetic.hK cE G.toArithmetic.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.GenuineComparison.budgetInputsAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 53. `genuine_residual_profile`

theorem; public.

```lean
genuine_residual_profile : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] (supp : Set (HeightOneSpectrum (𝓞 K)))
  {W V : Type} [inst_2 : AddCommGroup W] [inst_3 : Module (ZMod 2) W] [inst_4 : DistribMulAction (GKS K supp) W]
  [inst_5 : SMulCommClass (GKS K supp) (ZMod 2) W] [inst_6 : TopologicalSpace W] [inst_7 : DiscreteTopology W]
  [inst_8 : ContinuousSMul (GKS K supp) W] [inst_9 : AddCommGroup V] [inst_10 : Module (ZMod 2) V]
  [inst_11 : DistribMulAction (GKS K supp) V] [inst_12 : SMulCommClass (GKS K supp) (ZMod 2) V]
  [inst_13 : TopologicalSpace V] [inst_14 : DiscreteTopology V] [inst_15 : ContinuousSMul (GKS K supp) V]
  (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] V) (hβ : ∀ (g : GKS K supp) (a b : W), (β (g • a)) (g • b) = g • (β a) b)
  (Δ : GaloisLocalConditions K supp (ZMod 2) W) (I : GaloisTruncIsotropyData K supp (ZMod 2) β hβ Δ Δ)
  (tr : ↑((galoisCompactTT K supp (ZMod 2) β hβ Δ Δ I).X 3) →ₗ[ZMod 2] ZMod 2)
  (htr :
    ∀ (z : ↑((galoisCompactTT K supp (ZMod 2) β hβ Δ Δ I).X 2)),
      tr (((galoisCompactTT K supp (ZMod 2) β hβ Δ Δ I).d 2 3 ⋯) z) = 0),
  NekovarProp543 K →
    NekovarFiniteSetting K supp 2 (ZMod 2) →
      ∀ [Finite W],
        Function.Bijective ⇑β →
          Function.Bijective ⇑β.flip →
            IsCyclotomicTwist K supp (ZMod 2) V →
              InducesIsoH3 tr →
                OrthogonalComplementsT K β hβ Δ Δ I tr htr →
                  ∀ (e0 : ↑(homology (selCx (galoisSelData K supp (ZMod 2) W Δ)).toCC 0) ≃ₗ[ZMod 2] Fin 2 → ZMod 2)
                    [Module.Finite (ZMod 2) ↑(homology (selCx (galoisSelData K supp (ZMod 2) W Δ)).toCC 1)],
                    ResidualKummerProfile (selCx (galoisSelData K supp (ZMod 2) W Δ))
```

```text
'ZInQ.Contrib.RC53Assist.Budget.genuine_residual_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 54. `quotientRangeEquiv`

def; private helper.

```lean
@quotientRangeEquiv : {R : Type} →
  [inst : CommRing R] →
    {U V U' V' : Type} →
      [inst_1 : AddCommGroup U] →
        [inst_2 : Module R U] →
          [inst_3 : AddCommGroup V] →
            [inst_4 : Module R V] →
              [inst_5 : AddCommGroup U'] →
                [inst_6 : Module R U'] →
                  [inst_7 : AddCommGroup V'] →
                    [inst_8 : Module R V'] →
                      (f : U →ₗ[R] V) →
                        (g : U' →ₗ[R] V') →
                          (eu : U ≃ₗ[R] U') →
                            (ev : V ≃ₗ[R] V') →
                              (∀ (x : U), ev (f x) = g (eu x)) → moduleQuot f.range ≃ₗ[R] moduleQuot g.range
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.quotientRangeEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 55. `dualFunEquiv`

def; private helper.

```lean
@dualFunEquiv : {R : Type} → [inst : CommRing R] → (n : ℕ) → Module.Dual R (Fin n → R) ≃ₗ[R] Fin n → R
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.dualFunEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 56. `dualFunEquiv_apply`

theorem; private helper.

```lean
@dualFunEquiv_apply : ∀ {R : Type} [inst : CommRing R] (n : ℕ) (φ : Module.Dual R (Fin n → R)) (j : Fin n),
  (dualFunEquiv n) φ j = φ (Pi.single j 1)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.dualFunEquiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 57. `topHomologyEquiv`

def; private helper.

```lean
@topHomologyEquiv : {R : Type} →
  [inst : CommRing R] →
    (C : GCx R) → (n : ℤ) → C.d n (n + 1) ⋯ = 0 → ↑(homology C.toCC n) ≃ₗ[R] moduleQuot (C.d (n - 1) n ⋯).range
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.topHomologyEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 58. `firstSmithDualCokerEquiv`

def; private helper.

```lean
@firstSmithDualCokerEquiv : {R : Type} →
  [inst : CommRing R] →
    {U V M : Type} →
      [inst_1 : AddCommGroup U] →
        [inst_2 : Module R U] →
          [inst_3 : AddCommGroup V] →
            [inst_4 : Module R V] →
              [inst_5 : AddCommGroup M] →
                [inst_6 : Module R M] →
                  (n : ℕ) →
                    (s : Fin n → R) →
                      (e0 : U ≃ₗ[R] Fin n → R) →
                        (e1 : V ≃ₗ[R] (Fin n → R) × M) →
                          (f : U →ₗ[R] V) →
                            (∀ (x : U), e1 (f x) = ((Matrix.diagonal s).mulVec (e0 x), 0)) →
                              moduleQuot f.dualMap.range ≃ₗ[R] moduleQuot (Matrix.diagonal s).mulVecLin.range
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.firstSmithDualCokerEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 59. `IntegralFirstSmithModel.dual_e2`

def; private helper.

```lean
@IntegralFirstSmithModel.dual_e2 : {S : Type} →
  [inst : CommRing S] →
    {B : SmithBlocks S OO} →
      {A : ArithmeticComparison B} →
        (P : IntegralFirstSmithModel A) → ↑((dualCx P.C.toGCx 3).X 2) ≃ₗ[ℤ_[2]] Module.Dual ℤ_[2] ↑(P.C.toGCx.X 1)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.IntegralFirstSmithModel.dual_e2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 60. `IntegralFirstSmithModel.dual_e3`

def; private helper.

```lean
@IntegralFirstSmithModel.dual_e3 : {S : Type} →
  [inst : CommRing S] →
    {B : SmithBlocks S OO} →
      {A : ArithmeticComparison B} →
        (P : IntegralFirstSmithModel A) → ↑((dualCx P.C.toGCx 3).X 3) ≃ₗ[ℤ_[2]] Module.Dual ℤ_[2] ↑(P.C.toGCx.X 0)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.IntegralFirstSmithModel.dual_e3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 61. `IntegralFirstSmithModel.dual_top_zero`

theorem; private helper.

```lean
@IntegralFirstSmithModel.dual_top_zero : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  {A : ArithmeticComparison B} (P : IntegralFirstSmithModel A), (dualCx P.C.toGCx 3).d 3 4 ⋯ = 0
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.IntegralFirstSmithModel.dual_top_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 62. `IntegralFirstSmithModel.dual_h3_length`

theorem; public.

```lean
@IntegralFirstSmithModel.dual_h3_length : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  {A : ArithmeticComparison B} (P : IntegralFirstSmithModel A),
  Module.length ℤ_[2] ↑(homology (dualCx P.C.toGCx 3).toCC 3) = ↑(∑ j, (σ B 0 j).valuation)
```

```text
'ZInQ.Contrib.RC53Assist.Budget.IntegralFirstSmithModel.dual_h3_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 63. `IntegralFirstSmithModel.length_comparison`

theorem; public.

```lean
@IntegralFirstSmithModel.length_comparison : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  {A : ArithmeticComparison B} (P : IntegralFirstSmithModel A) (cE : ℕ),
  SingularBounds A.X A.Y cE → IntegralModelDuality P.C → IntegralKummerLengthComparison A.integral.X₁
```

```text
'ZInQ.Contrib.RC53Assist.Budget.IntegralFirstSmithModel.length_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 64. `budgetInputsAt_of_integralModel`

theorem; public.

```lean
@budgetInputsAt_of_integralModel : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (P : IntegralFirstSmithModel A) (cE : ℕ),
  ResiduallyMinimal B →
    ResidualKummerProfile A.ordinaryRed →
      SingularBounds A.X A.Y cE → IntegralModelDuality P.C → BudgetInputsAt B fr₀ A.dK A.hK cE A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_of_integralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 65. `singular_chain_free`

theorem; private helper.

```lean
@singular_chain_free : ∀ {R : Type} [inst : CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) (n : ℤ),
  Module.Free R ↑((singularCx X Y).X n)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singular_chain_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 66. `singular_chain_finite`

theorem; private helper.

```lean
@singular_chain_finite : ∀ {R : Type} [inst : CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) (n : ℤ),
  Module.Finite R ↑((singularCx X Y).X n)
```

```text
'_private.ZInQKernel.Contrib.RC53Assist.Budget.ArithmeticBudget.0.ZInQ.Contrib.RC53Assist.Budget.singular_chain_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 67. `singular_chain_total_rank`

theorem; public.

```lean
@singular_chain_total_rank : ∀ {R : Type} [inst : CommRing R] [StrongRankCondition R] (X Y : Matrix (Fin 2) (Fin 2) R),
  ∑ n, Module.finrank R ↑((singularCx X Y).X ↑↑n) = 8
```

```text
'ZInQ.Contrib.RC53Assist.Budget.singular_chain_total_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 68. `SmallGradedModel.rank_budget`

theorem; public.

```lean
@SmallGradedModel.rank_budget : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} {A : ArithmeticComparison B}
  (D : SmallGradedModel A),
  ResidualKummerProfile A.ordinaryRed → ∑ n, Module.finrank ℤ_[2] (centralCx B fr₀ ↑n) ≤ 2 * A.dK + 12
```

```text
'ZInQ.Contrib.RC53Assist.Budget.SmallGradedModel.rank_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 69. `budgetInputsAt_of_smallGradedModel`

theorem; public.

```lean
@budgetInputsAt_of_smallGradedModel : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) (D : SmallGradedModel A) (P : IntegralFirstSmithModel A) (cE : ℕ),
  ResidualKummerProfile A.ordinaryRed →
    SingularBounds A.X A.Y cE → IntegralModelDuality P.C → BudgetInputsAt B fr₀ A.dK A.hK cE A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_of_smallGradedModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 70. `smith_budget_of_smallGradedModel`

theorem; public.

```lean
@smith_budget_of_smallGradedModel : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (D : SmallGradedModel A) (P : IntegralFirstSmithModel A) (cE : ℕ),
  (∀ (i : ℕ), 3 ≤ i → i < B.n → B.m i = 0) →
    ResidualKummerProfile A.ordinaryRed →
      SingularBounds A.X A.Y cE → IntegralModelDuality P.C → B.mTot ≤ A.dK + 5 ∧ B.hSmith ≤ A.hK + 2 * cE + 2 * A.tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.smith_budget_of_smallGradedModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 71. `budgetInputsAt_with_parameters`

theorem; public.

```lean
@budgetInputsAt_with_parameters : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (dK hK cE tK : ℕ),
  ParameterAgreement A dK hK tK → BudgetInputsAt B fr₀ A.dK A.hK cE A.tK → BudgetInputsAt B fr₀ dK hK cE tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_with_parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 72. `torsionIdentificationOfExact`

def; public.

```lean
@torsionIdentificationOfExact : {R : Type} →
  [inst : CommRing R] →
    [IsDomain R] →
      {T M V : Type} →
        [inst_2 : AddCommGroup T] →
          [inst_3 : Module R T] →
            [inst_4 : AddCommGroup M] →
              [inst_5 : Module R M] →
                [inst_6 : AddCommGroup V] →
                  [inst_7 : Module R V] →
                    [Module.IsTorsionFree R V] →
                      (i : T →ₗ[R] M) →
                        (j : M →ₗ[R] V) →
                          Function.Injective ⇑i →
                            Function.Exact ⇑i ⇑j → Module.IsTorsion R T → T ≃ₗ[R] ↥(Submodule.torsion R M)
```

```text
'ZInQ.Contrib.RC53Assist.Budget.torsionIdentificationOfExact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 73. `dK_of_selmer_identification`

theorem; public.

```lean
@dK_of_selmer_identification : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (Sel2 : ModuleCat (ZMod 2)) (e : ↑(homology A.ordinaryRed.toCC 1) ≃ₗ[ZMod 2] ↑Sel2),
  A.dK = Module.finrank (ZMod 2) ↑Sel2
```

```text
'ZInQ.Contrib.RC53Assist.Budget.dK_of_selmer_identification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 74. `tK_of_coefficient_exact`

theorem; public.

```lean
@tK_of_coefficient_exact : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)
  (Tor V : ModuleCat ℤ_[2]) [Module.IsTorsionFree ℤ_[2] ↑V] (i : ↑Tor →ₗ[ℤ_[2]] ↑(homology A.integral.X₁ 1))
  (j : ↑(homology A.integral.X₁ 1) →ₗ[ℤ_[2]] ↑V),
  Function.Injective ⇑i → Function.Exact ⇑i ⇑j → Module.IsTorsion ℤ_[2] ↑Tor → A.tK = (Module.length ℤ_[2] ↑Tor).toNat
```

```text
'ZInQ.Contrib.RC53Assist.Budget.tK_of_coefficient_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 75. `RetainedSingularStage.bounds`

theorem; public.

```lean
@RetainedSingularStage.bounds : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO} {A : ArithmeticComparison B}
  {cE : ℕ} (R : RetainedSingularStage A cE), SingularBounds A.X A.Y cE
```

```text
'ZInQ.Contrib.RC53Assist.Budget.RetainedSingularStage.bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 76. `budgetInputsAt_from_selmer_models`

theorem; public.

```lean
@budgetInputsAt_from_selmer_models : ∀ {S : Type} [inst : CommRing S] {B : SmithBlocks S OO}
  (A : ArithmeticComparison B) (D : SmallGradedModel A) (P : IntegralFirstSmithModel A) (dK hK cE tK : ℕ)
  (R : RetainedSingularStage A cE) (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC),
  QuasiIso γ →
    ∀ (e0 : ↑(homology A.ordinaryRed.toCC 0) ≃ₗ[ZMod 2] Fin 2 → ZMod 2)
      [Module.Finite (ZMod 2) ↑(homology A.ordinaryRed.toCC 1)],
      IntegralModelDuality P.C → ParameterAgreement A dK hK tK → BudgetInputsAt B fr₀ dK hK cE tK
```

```text
'ZInQ.Contrib.RC53Assist.Budget.budgetInputsAt_from_selmer_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
