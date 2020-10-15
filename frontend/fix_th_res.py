import argparse
import os

parser = argparse.ArgumentParser()
parser.add_argument("inputdir")
args = parser.parse_args()

files = [f for f in os.listdir(args.inputdir) if f.endswith('.out') and not os.path.exists(f[:-7] + '.res.th')]

for i, f in enumerate(files):
         with open(f[:-7] + '.log') as fp:
                 lines = fp.readlines()
         lemms = [l.split('proved: ')[1].strip() for l in lines if 'proved' in l]
         res = [f"(=> rule_{i}_{j} {l.split('=>')[0]} {l.split('=>')[1]})\n" for (j, l) in enumerate(lemms)]
         res_f = f[:-7] + '.res.th'
         with open(res_f, 'w') as fp:
                 fp.writelines(res)