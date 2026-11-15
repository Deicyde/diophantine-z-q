# triage2 pass 1 (11-15 ~06:00 PST, base 9a100aa7): ranked tasks (details: docs/research/triage2.md §1)
1. Semantic prune (−2, T2): deligneComponentsX6PrintedAb + geomConnOfAlgClosure feed only R1pi0Props (last conjunct of
   R1R2fpRep), which no live constant reads (compiled probe scratch/triage2/Pi0Use.lean). NB geomConnOfAlgClosure is held
   (cloud batch 2): lead to decide.
2. semistablePersistsSHcp (−1, T2/T3): prove ReductSplit.SemistablePersistsDVR from SGA3_VIB_3_10 + SGA7_IX_3_3 +
   GeomConnOfRationalPoint via the proved identityComponentBaseChangeDVRRange_of + fibre transport; plain field replacement.
3. babaGranathRationalAb (−1, T2/T3): = ElkiesEquationsX6Ab (derived) + CMPairsExist; CMPairsExist from ModuliAtUnits of
   shimuraMainThmIDeligneY3AbU + HomLatticeCorr + descend_main copy. Fallback T1: weaker leaf CMPairsExist.
4. gonzalezRotgerProp56X6 (−1, T3, bypass): in nocm_on_witness identify R ∈ {ℤ[i], ℤ[√−6]} by norm forms instead of the count.
5. deligneComponentsY3PrintedAb (−1, T3, bypass): only Y3Connected is used; prove it from shimuraMainThmIDeligneY3AbU + a
   (𝒪/3)^× decide at K = ℚ(i).
6. gaudronRemondThm14 one-direction narrowing (0 fields, T1/T2) via milneIsogenyQuasiInverse.
All other in-scope statements (r9a, r9b, HT, dR, DS965, Bost, Javanpeykar, Pazuki, GR X6Ab, Raynaud, SGA7 3.3/3.5, hCM, h33): keep, T4.
