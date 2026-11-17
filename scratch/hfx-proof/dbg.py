exec(open('orbits.py').read().split('res = {}')[0])
for abc in [(1,1,1),(1,1,7),(3,1,1),(1,3,5)]:
    print(abc, orbits(unit_gens(abc)))
