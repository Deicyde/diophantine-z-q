
section Act
variable {K : Type*} [Field K]

/-- The cocycle identity: acting by `M` then by `N` is acting by `M * N`. -/
theorem actC_actC (f : Fin 7 → K) (a b c d e a' b' c' d' e' : K) :
    actC (actC f a b c d e) a' b' c' d' e' =
      actC f (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') (e * e') := by
  funext i; fin_cases i <;> simp [actC] <;> ring

theorem actC_scale (f : Fin 7 → K) (a b c d e : K) :
    actC f a b c d e = fun i => e * actC f a b c d 1 i := by
  funext i; fin_cases i <;> simp [actC] <;> ring

end Act
