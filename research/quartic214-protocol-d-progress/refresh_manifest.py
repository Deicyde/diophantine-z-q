#!/usr/bin/env python3
"""Bind packet bytes after author integration; never creates a reviewer decision."""
import hashlib,json
from pathlib import Path
base=Path(__file__).resolve().parent
records=[]
for p in sorted(base.rglob('*')):
 if p.is_file()and p.name!='PACKET_MANIFEST.json':records.append({'path':str(p.relative_to(base)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
d={'schema':'q214-progress-packet/v1','role':'author file manifest; no independent approval','frozen_mathematical_source':'e3626cac202cdbcdfedc2bff1978dcd3ea3fd3ab','files':records,'self_hash':'not embedded; report external SHA256 of this file','scope':'Complete additive packet file inventory only; not complete mathematical or historical inventory.'}
p=base/'PACKET_MANIFEST.json';p.write_text(json.dumps(d,indent=2)+'\n');print('PACKET_MANIFEST.json',hashlib.sha256(p.read_bytes()).hexdigest(),'files',len(records),'bytes',sum(q['bytes']for q in records))
