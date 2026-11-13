# Author serialization notes

This is an additive manuscript serialization. It changes no frozen polynomial,
proof, application contract, source theorem, reviewer record, or acceptance.
The 214 packet source commit is `110cf72565be326fd567cd1a64a3b2e00213dcd1`.
The current upstream foundation is the Version 16 target selected by
`docs/current-manuscript.json`, SHA-256
`aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74`.
The explicit source/consumer transition is
`../quartic214-manuscript-review/FOUNDATION_TRANSITION.md`.

`assemble.py` uses the Python standard library and makes no network requests,
symbolic expansions, TeX builds, or acceptance records. Its `--check` mode
reconstructs both generated files in memory and compares their exact bytes.
`quartic214.tex` is the complete, standalone TeX source. `SOURCE_SPANS.json`
binds input byte hashes and source-line or JSON-pointer spans to its TeX lines.

Part I contains the new theorem, notation, all 214 coordinate names, all 188
primitive integral quadratic rows, every line of the public assembly and
proof files, every selected Markdown/TeX source fragment, the raw224 proof,
finite-certificate links and hashes, and the complete primary-source metadata.
The polynomial is specified exactly as the unweighted sum of these 188 row
squares. Long row coefficients are printed as exact base-ten block sums;
the assembler does not expand the 2919-monomial quartic.

Part II retains the entire current Version 16 mathematical body with its
bibliography and historical provenance. Its original `maketitle` and duplicate
table of contents are publication wrappers replaced by the unified front
matter. Its original abstract is retained. Its section and equation counters
are restored; separate hyperlink namespaces prevent collisions with Part I.
Only line endings are normalized in the retained mathematical body. Four
separate invisible navigation labels locate corrected applications; the exact
mapped source blocks concatenate to the complete original mathematical body.
Generated PDF destinations are unique without changing printed numbers. The
original byte hash remains separately bound. The frozen Version 15 source is
also byte-bound as historical provenance for the earlier author packets.

ASCII mathematics in the Markdown sources is typeset into mathematical TeX.
Balanced spans retain quantified conditions containing spaces. Script operands
retain their full grouping, including negative indexed exponents. Source set
braces are visible delimiters, while script braces remain grouping. Root
operands are explicit. Bare ASCII `Q`, `Z` and stars retain their source
notation rather than receiving a global semantic interpretation.

Several notation resolutions are source-specific and recorded in the map:
the summation Sigma in the different, metric and aggregate source files;
the aggregate function `F+` in its two proof occurrences; the metric source's
direct-image star and conjugate differentials; the evaluation/different
target projective line; degree-zero differential cohomology `H0(...)`; and the
uniform proof's `mathfrak_b` pole-input notation. Control sequences and their
space-separated arguments remain in the same mathematical span.
Selected TeX fragments have local labels/references namespaced and their
bibliography keys matched to the complete retained bibliography. Their
historical `Logs` citation resolves to the actual retained V15 logarithm
section. No substitute arithmetic theorem is introduced.

The operative averaging route is visibly the published product construction.
The old H3 quotient route and coarse conductor fragments are retained with
explicit supersession notices. Their historical scope statements are not
silently promoted to acceptance of this serialization. The theorem keeps its
fixed ineffective uniform threshold, and `N >= 53` remains coefficient-only.

The author lane ran no TeX build. The root lane owns bounded serial PDF
compilation, rendered inspection, release hashes and publication. Source-map
coverage, deterministic reconstruction, compilation and finite algebra checks
are bounded checks; they do not establish the arithmetic theorem or official
Protocol D acceptance. Required independent review is authored separately.

The 2026-11-12 PR30 F1/F2 author repair uses the versioned
`SOURCE_CORRECTIONS_V1.json` overlay. Each replacement binds an exact frozen
source hash, line number and complete original line. The frozen packets remain
unchanged. The corrected source line is recorded explicitly on its source-map
span, and the overlay itself is byte-bound in the source inventory. F1 groups
`D(mu_sigma)^(-1/4)`; F2 supplies the single math span
`Σ_j e_j f_j=d`. These repairs await fresh independent acceptance.

The bounded related-use review covered all 19 Markdown inputs selected by
`assemble()` in Part I, including the foundation transition, packet assembly,
13 proof files, three selected source fragments and raw224 proof. It searched
all power/slash adjacencies and summation/indexed-product forms and compared
the relevant source paragraphs with the generated passages. The only bare
numeric power followed by slash that denotes a rational exponent was F1.
The other hits `delta^10/F2(t)`, `g^4/f²`, `g^4/f^2`,
`Z0^4/R_s^10`, `Z1^2/R_s^5`, `F^2/R_s^4` and `gamma^2/4`
are genuine quotients in the contact, recovery, test-term and pole-input
arguments. Their contexts explicitly define the corresponding ratios or
limits; a global rational-exponent rewrite would change those assertions.
Grouped negative quarter-powers in height-supplier:45 and
conductor-sections1-3:48 already give the intended normalization. In M1,
D(c mu)=c^4 D(mu) and the positive root give the next cocycle identity;
M2 consumes the same a_sigma in t_sigma=a_sigma/b(sigma), and M6 consumes
its fourth-power determinant identity. At the identity D(1)=1 requires a_1=1;
the old /4 reading violates that test. This is prior intended justification
found, with inconsistent prior manuscript serialization, rather than a new
arithmetic argument.

For F2, height-different:15–23 includes every completed component above the
height-one point, with full residue degree (including inseparable degree).
Finite freeness and the uniformizer filtration give rank(U_j)=e_j f_j and
sum_j e_j f_j=d. Multiplication of the component estimate at line41 by every
f_j therefore yields line45's whole discriminant bound. Lines51 and113
separately sum over every prime/component with spaced indexed factors; the
height-assembly:39 consumer takes the same trace determinant and same fibre
order C. Those expressions, the metric sums at lines21,33,45,47, aggregate
sums, and the selected product_(...) expressions already retain their indices
and operands; no additional local correction was identified. This review
checks these serialization failure classes, not the full proof of their
source theorems. The finite regression checker distinguishes a fourth root
from reciprocal-then-division, exercises unequal residue-degree factors,
checks corrected rendered consumers and genuine quotients, and rejects a
stale original-source binding. It supplies no independent acceptance.

Fresh independent review subsequently found F3/F4. The earlier bounded scan
above did not establish correctness of extension subscripts or numeric indices
next to Unicode superscripts; its statement that no additional correction was
identified describes that earlier scan, not the current result. The overlay
now additionally records eight F3 source-line corrections and nine F4
source-line corrections. These remain author proposals for fresh review.

F3: read height-different §§2–3 in full and compared the tower consumer in
§5. D_{U/V} is the inverse fractional trace-dual ideal for the extension,
not D_U divided by V. The exact generic trace is Tr_{L/Frac(V)}. In the
complete DVR tower V⊂W⊂U, trace transitivity identifies
U^vee_V=α U^vee_W when W^vee_V=αW; inverse ideals give
D_{U/V}=D_{U/W} D_{W/V} U and
r_{U/V}=r_{U/W}+e_{U/W} r_{W/V}. Nonnegative exponents give the asserted
intermediate-field bound at every completion, which is the bound consumed for
every component of the primitive torsion quotient in §5. These exact labels
are grouped throughout lines31,65,83,85. The adjacent relative differential
and dualizing modules Ω_{E/V}, ω_{A/V}, Ω_{A/V} in lines61,63 likewise require
whole extension indices. The repeated relative model differential
ω_{𝒳/O_K} in metric:9 and assembly:21 receives the same explicit grouping.
These denote the same integral differential lattice used by evaluation,
metric and assembly, rather than a module divided by O_K. All three source
files remain frozen; only exact overlay lines change.

The expanded related-use inventory covered underscore/slash adjacencies in
all 19 selected Markdown inputs. Height-evaluation's already grouped
ω_{M_i/R}, ω_{Y/R}, ω_{Z/R}, ω_{P1_R/R} and Tr_{L/F}
need no correction. Genuine module quotients U_j/π_V U_j,
B_q/pB_q, C_p^vee/O_p, O_p/C_p, F_I/R^I and D_i/D_(i-1)
retain their quotients. U^vee_V, W^vee_V and U^vee_W retain distinct dual
and base indices; they are not extension-slash notation. Base declarations
A_f/Q, E_l/Q, A_a/L and E_t/V retain their over-base slash; the slash is
outside the already complete numeric/symbolic object name. Other arithmetic
ratios (including a_sigma/b, d_K/e and H_J/r) remain unchanged.

F4: existence:31 defines A_i=f(U_i), C_i=L_i-L_i', B_i=σf(V_i);
its five factors at lines33–37 therefore square C_2,A_3,A_2,A_4,C_3,C_4,A_1.
The local valuation consumer at line84 uses that same A_2. Uniform-existence
§P05 repeats these factors with ASCII powers and already prints the indices
correctly; the overlay reconciles the repetitions. Assembly:9 and
existence:19 define stored inverse powers s_1,s_2,s_4, so their squared
right sides must retain the numeric indices too. Height-different:95 defines
c_4=-48a and then j=c_4^3/Δ; the cube has the same indexed invariant, and
its denominator Δ remains a genuine quotient. A complete scan of the same
19 Markdown inputs for ASCII letter+digits followed by Unicode powers
¹²³⁴ found exactly these nine affected source lines. Each receives an explicit
source-local grouped index and ASCII exponent; no global tokenizer change
or polynomial edit is made. The checker now asserts literal rendered TeX for
all corrected extension labels and all numeric indexed powers, rejecting
baseline digits under the powers. This is finite serialization regression
evidence, not independent mathematical acceptance.

F5 was found in the next independent rendered review, after the F3/F4 scan.
Height-different:61 is now a combined F3/F5 overlay: its original correction
ID remains F3-2, with explicit finding_ids [F3,F5] in both sidecar and map.
The source-local math span `[n]^{*}ω=nω` protects the pullback star from
Markdown emphasis parsing, and Ω_{[n]} groups the morphism's complete bracket
label as the differential-module index. No frozen line or global parser
rule changes. Evaluation-sections1-4.tex:373–382 gives the actual earlier
argument: multiplication by n differentiates as n on invariant differential
bases, its relative differential presentation has Fitting ideal (n), and
zero-section base change retains that ideal. Height-different:61–71 uses
this exact scalar to identify the trace-normalized fractional dual with
n^{-1}A; lines79,85,111–115 then consume its component and intermediate-field
different bounds. The scalar is n rather than the degree n². This is prior
justification found with a failed manuscript serialization, not a new proof.

The renewed bounded search of selected Markdown star exponents and bracket
subscripts found the one ungrouped Ω_[n] and the four star contexts named
by the reviewer. Height-evaluation:45 is authored display TeX and preserves
its a_i^*ω pullback; height-evaluation:48 prints α^{*}E; the conductor
fragment:27 prints Q_{11}^{*}, a multiplicative group. Metric p*ω has its
existing explicit source-local pushforward adapter p_*ω and is not a
pullback exponent. These meanings are retained. Indexed torsion points
E[n], A[11], and multiplication maps [n] elsewhere are bracketed arguments
or morphism names, not truncated subscript operands. Regression checks now
assert the exact pullback formula, whole bracketed differential index,
absence of emphasis and empty exponent on the corrected line, preservation
of the three other star-exponent uses, and combined F3/F5 traceability.
No independent acceptance is implied.
