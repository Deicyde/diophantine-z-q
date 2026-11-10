-- to be appended to ZInQKernel/External/GreenTaoDense.lean once the library builds
/-- **Green–Tao, dense form** (`ZInQ.GreenTaoDense`), from the vendored proof of Green–Tao. -/
theorem _root_.ZInQ.greenTaoDense : ZInQ.GreenTaoDense := by
  intro A hA hd k
  obtain ⟨c₁, hc₁, hwin⟩ := frequently_window hd
  obtain ⟨a, d, hd0, h⟩ :=
    containsAP_of_frequently_window hasPrimeModulusSubweightCounts hA hc₁ hwin k
  exact ⟨a, d, hd0, h⟩
