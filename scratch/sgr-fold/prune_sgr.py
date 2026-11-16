"""sgr-fold step B: after the reroute (step A), PruneScan reports OpenAddedLeaves17.shimuraIntegralModelRep and
OpenGlue7.quotientP1Coordinate unused; its prune set (prune-set-stepA.txt, 12 FIELD lines) is deleted here, with
every assignment into a pruned field. Off-chain cascade: addedLeaves11_of_open12 (TailZ22, used by the off-chain
sixContactMin_of_open16) reads OpenAddedLeaves12.shimuraGoodReductionNoGuard, so the field is also deleted from the
off-chain OpenAddedLeaves11 and OpenAddedLeaves10 (both wholly unused per unused-all-stepA.txt) with their
assignments; addedLeaves5_of_open6 (TailO, referenced only by its #print) reads OpenAddedLeaves6.shimuraGoodReduction
and is deleted as a dead reader. Deletions only. Prints every deleted line."""
import sys
sys.path.insert(0, 'scratch/sgr-fold')
import prune_lib as P
NG = 'shimuraGoodReductionNoGuard'
P.drop_field('TailO', 'OpenAddedLeaves6', 'shimuraGoodReduction')
P.drop_field('TailO', 'OpenGlue6', 'modelCoordinateResidue')
P.drop_field('TailX', 'OpenAddedLeaves7', NG)
P.drop_field('TailX', 'OpenGlue7', 'quotientP1Coordinate')
for f, s in [('TailZ4', 'OpenAddedLeaves8'), ('TailZ13', 'OpenAddedLeaves9'), ('TailZ17', 'OpenAddedLeaves10'),
             ('TailZ18', 'OpenAddedLeaves11'), ('TailZ22', 'OpenAddedLeaves12'), ('TailZ24', 'OpenAddedLeaves13'),
             ('TailZ26', 'OpenAddedLeaves14'), ('TailZ30', 'OpenAddedLeaves15'), ('TailZ31', 'OpenAddedLeaves16')]:
    P.drop_field(f, s, NG)
P.drop_field('TailZ34', 'OpenAddedLeaves17', 'shimuraIntegralModelRep')
# assignments into pruned fields
P.drop_assign('TailX', 'theorem addedLeaves6_of_open7 ', 'shimuraGoodReduction',
  '  shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (LeafAdopt.R1R2fp_of_rep r.r1r2)\n    l.shimuraGoodReductionNoGuard')
P.drop_assign('TailX', 'theorem glue6_of_open7 ', 'modelCoordinateResidue',
  "  modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate")
for f, h, src in [('TailZ4', 'theorem addedLeaves7_of_open8 ', 'l'), ('TailZ13', 'theorem addedLeaves8_of_open9 ', 'l'),
                  ('TailZ17', 'theorem addedLeaves9_of_open10 ', 'l'), ('TailZ18', 'theorem addedLeaves10_of_open11 ', 'l'),
                  ('TailZ22', 'theorem addedLeaves11_of_open12 ', 'l'), ('TailZ23', 'theorem addedLeaves9_of_open14 ', 'l'),
                  ('TailZ24', 'theorem addedLeaves12_of_open13 ', 'l'),
                  ('TailZ26', 'theorem openAddedLeaves13_of_OpenAddedLeaves14 ', 'n'),
                  ('TailZ30', 'theorem openAddedLeaves14_of_OpenAddedLeaves15 ', 'n'),
                  ('TailZ31', 'theorem openAddedLeaves15_of_OpenAddedLeaves16 ', 'n')]:
    P.drop_assign(f, h, NG, f'  {NG} := {src}.{NG}')
P.drop_assign('TailZ34', 'theorem openAddedLeaves16_of_OpenAddedLeaves17 ', NG,
  f'  {NG} := _root_.SGRSplit.shimuraGoodReductionNoGuard_of_printed n.shimuraIntegralModelRep')
P.drop_decl('TailO', 'addedLeaves5_of_open6')
for f, ls in P.files.items():
    open(P.H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(P.deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
