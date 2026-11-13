# leaf-adopt3 results log

## Setup
- 01:16 merged origin/wip/g0-split, wip/h5-neron, wip/t10-etale (scratch + docs only; their .fleet notes dropped).
- Infrastructure: `scratch/leaf-adopt3/olean/HDPrefix.lean` = Leaves.lean lines 1-21087 (everything before HSyn),
  compiled to an olean so the tail can be iterated quickly (`import HDPrefix`, LEAN_PATH=olean dir).
