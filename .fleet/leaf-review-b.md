# leaf-review-b (fleet summary)

**Main result.** Independent statement review of leaf-fold3's groups B, C, D, E, G (41 bundle fields
of `HDec.HSyn.sixContactMin_of_open3`): **8 PUBLISHED-FORM, 33 CONSEQUENCE, 0 STRONGER-THAN-SOURCE,
0 NOT-A-PUBLISHED-STATEMENT**, so no repaired text is proposed. Report: `docs/research/leaf-review-b.md`
(one row per field: field, Lean name and line, cited source, verdict, reason/derivation).

PUBLISHED-FORM: t11b, serreRigidity3, r7a, t41, r9a, r9b, r19, t33. All others CONSEQUENCE, each with
its derivation (mostly base change to k̄, Néron/semistable reduction bookkeeping, HT-convention checks).

Shared premises flagged (not statement errors): (1) the D rows read heights through the project's
`stableFaltingsHeight` (inf over metrized models), assumed equal to the published stable Faltings
height (H5 argument; definition read, not re-proved); (2) locators unread even by the repo audit:
Faltings 1983 Lemma 5 (r20), Bost's display (r21 holds in either normalization), Pan's JAMS
numbering (r11r12); (3) R22's theta-coordinate identification (UNVERIFIED in its own docstring);
t10's action directions checked by hand only.

**What compiles.** `scratch/leaf-review-b/run_check.sh` (Leaves3.lean + `PrintFields.lean.tail`, a
`#lrb_fields` metaprogram printing every field's type and head-definition body): exit 0, 0 errors;
the 41 fields resolve to the definitions named in the report.

**Declarations proved:** none (review task; no Lean deliverable beyond the check file).
**Remains:** nothing in scope; primary texts could not be read (no network).
