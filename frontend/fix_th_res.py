"""
A patch that extracts discovered lemmas from timed-out results, since
these do not have a corresponding .res.th file.
"""

import argparse
import os
import os.path

parser = argparse.ArgumentParser()
parser.add_argument("inputdir")
args = parser.parse_args()

cwd = args.inputdir

files = [f for f in os.listdir(cwd) if f.endswith('.log')
         and not os.path.exists(os.path.join(cwd, os.path.join(f[:-4] + '.res.th')))]

for i, f in enumerate(files):
    print(f, end='')
    with open(os.path.join(cwd, f)) as fp:
        lines = fp.readlines()
    lemms = [l.split('proved: ')[1].strip() for l in lines if 'proved' in l]
    res = [f"(=> rule_{i}_{j} {l.split('=>')[0]} {l.split('=>')[1]})\n" for (j, l) in enumerate(lemms)]
    res_f = f[:-4] + '.res.th'
    print(' > ' + res_f)
    with open(os.path.join(cwd, res_f), 'w') as fp:
        fp.writelines(res)
