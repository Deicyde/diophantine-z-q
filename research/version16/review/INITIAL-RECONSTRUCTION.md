# Independent initial source reconstruction

Reviewer: /root/v16_correction_review. Date: 2026-11-11.
Scope: the horizontal normalization and its finite-cover consumer, two auxiliary Faltings-height citations, and the fixed extra factor in the Tao--Ziegler W construction. This is a bounded component review, not an assembled-proof or publication decision. No proposed Version 16 file has been read at this stage.

Baseline: work/version15-protocold-222-20261110/repository/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex. Raw-file SHA-256: 44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74.

I read the actual baseline passages 26620--26965, 27465--27560, 30570--30690, 19980--20110, and bibliography 39311--39314 and 39718--39737. I also read AGENTS.md, docs/audit-history/PROTOCOL.md, and the relevant research protocol and Astra policy. A broad filename/search output exposed historical report paths and inventory headlines, but I have not used those reports or inventory entries to reconstruct the following requirements. This is source-first, not a claim of blindness to the assigned concerns.

## H1: lifting horizontal torus identities before passing to a cover

Available: at 26724--26734 the lattice-compatible map phi: U -> G and the torus surjection provide chosen preimages only in horizontal tori. At 26736--26743 horizontal Taylor maps are homomorphisms, and multiplying by c^(binom(n,i)) inserts the i-th horizontal vector. Integer changes of variables at 26745--26752 preserve the torus identities but do not automatically preserve chosen real representatives.

Needed: before using powers M of the remaining generator images at 26880--26888, the horizontal Taylor vector of the actual orbit must equal the sum of the chosen real frequencies times the generator horizontal vectors. Equality modulo the old Gamma-horizontal lattice does not imply equality modulo the smaller Gamma'-horizontal lattice. Dividing torus roots alone cannot repair an uncontrolled old-lattice discrepancy.

Direct connecting argument: for every weight i choose actual real lifts t_(h,i,a) of the current frequency representatives. Their weighted sum differs from the Taylor vector by an element of the horizontal image of Gamma intersect G_i. Lift that difference to lambda_(h,i) in Gamma intersect G_i. Right multiplication of g_h(n) by the inverse of the ordered product over i of lambda_(h,i)^(binom(n,i)) preserves g_h(n)Gamma exactly. The product is polynomial by the Taylor criterion and product closure. Horizontal homomorphism cancels exactly the chosen discrepancies in every weight. This construction must be repeated after any new choice of real representatives that reintroduces a lattice discrepancy, before the next cover is used. It costs no Lipschitz loss because it does not change the old orbit or test. Unbounded internal lambda values cause no new test-function bound.

For a cover choose the divided real representatives t/M and map the new letter to phi(e)^M. The vector identity M pi(phi(e)) (t/M) = pi(phi(e)) t is then exact. The new lattice map lands in Gamma'. Integer-character independence survives multiplication by the fixed common denominator. Bracket-linear representatives should be divided as real beta/M, with the existing fixed-box Freiman refinement. Arbitrary torus roots would need compatible lifts; they are not by themselves the vector argument.

Related existing normalization: 27526--27534 already gives this lattice-polynomial correction for the comparison orbit a_h, and 27536--27554 consumes exact vector equalities to prove membership in H. This is prior justification for the normalization device. Whether it was previously incorporated at the earlier finite-cover application is a separate question. The baseline finite-cover paragraph does not state the needed vector correction at that application.

Immediate consumers to check: small and rational coordinate removal at 26815--26899; the frequency annihilator/coset passage at 26902--26954; quadruple construction beginning 26956; comparison-group polynomial membership at 27526--27554. The correction should not alter the original nilcharacter, its vertical law, or the claimed degree/rank.

## H2: auxiliary height citations

At 30624--30633 the proof needs additivity of stable Faltings height and the original-normalization bound h_F(E) >= -log(pi sqrt(2)) dim(E), including E of dimension zero. At 30645--30647 it needs h_F(A) <= h_F(B) + (1/2) log(deg(B -> A)). The source and target are over L', and the preceding 2023 isogeny theorem and simple-factor construction are separate inputs. The key gr2014 currently identifies the Duke paper Polarisations et isogenies. The proposed CMH paper must be checked for the exact sections and normalization; replacing the existing bibliography entry would incorrectly alter other gr2014 applications at 1322, 1599, and 1616. Use a distinct key for these two auxiliary uses and retain the Duke entry.

## H3: fixed extra factor in W

At 20036--20044, W = D product_(p<=v,p does not divide D) p with fixed D. For v past every prime divisor of D, W = E product_(p<=v) p with fixed E = product_(p|D) p^(v_p(D)-1). The proof at 20067--20074 uses a local divisor-sum argument: unit b modulo W makes every small-prime divisibility event impossible, and primes not dividing W see the same invertible coefficient situation. The fixed E is absorbed in the stated coefficient bounds.

The source-use distinction matters: the fixed E extension is an adaptation of the published proof of the majorant estimates, not an exact instance of a theorem whose W has been defined as the squarefree primorial. The dense model and concatenation results can consume the adapted majorant once its hypotheses hold. An accurate revision must say this without implying that naming the adaptation supplies any omitted uniform estimates. The bounded review must compare the actual local factors and the fixed-data / v / n limit order with the source proof.

No final acceptance is recorded here. Exact proposed-file binding and primary-source checks remain pending. Astra eligibility is a controller-trusted run property, not established by this report.
