"""Apply exact modulo and affine elimination to any compatible compiled IR."""
import argparse,json
from pathlib import Path
import modulo_search as M
import affine_search as A
import verify as V

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('source',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--orders',type=int,default=1)
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    snapshot=args.output/'source-ir.json'
    snapshot.write_bytes(args.source.read_bytes())
    M.SOURCE=snapshot;M.OUT=args.output;A.OUT=args.output
    data=json.loads(snapshot.read_text());prior=None
    for cycle in range(3):
        initial=len(data['coordinates']);M.c=M.C.Compiler(data)
        M.run(max_orders=args.orders,prior=prior)
        A.run()
        data=json.loads((args.output/'candidate-ir.json').read_text())
        prior=json.loads((args.output/'modulo-certificate.json').read_text())
        if len(data['coordinates'])==initial:break
    V.SOURCE=snapshot;V.HERE=args.output;V.verify()

if __name__=='__main__':main()
