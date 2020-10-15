import sexpdata
import os
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("inputdir")
args = parser.parse_args()

files = [f for f in os.listdir(args.inputdir) if f.endswith('.res.th')]


def collect_symbols(sexp):
    if isinstance(sexp, sexpdata.Symbol):
        return {sexp.value()}
    if isinstance(sexp, int):
        if sexp > 0:
            return {'+' + str(sexp)}
        return {str(sexp)}
    if isinstance(sexp, str):
        return {sexp}
    res = set()
    for s in sexp:
        for sym in collect_symbols(s):
            res.add(sym)

    return res


def to_str_no_qm(sexp):
    if isinstance(sexp, sexpdata.Symbol):
        if sexp.value().startswith('?'):
            return sexp.value()[1:]
        return sexp.value()
    if not isinstance(sexp, list):
        if isinstance(sexp, int) and sexp > 0:
            return {'+' + str(sexp)}
        return str(sexp)
    children = [to_str_no_qm(c) for c in sexp]
    return f"({' '.join(children)})"


for f in files:
    f = os.path.join(args.inputdir, f)
    with open(f) as fp:
        rules = [sexpdata.loads(l, nil='nilSpec') for l in fp.readlines()]
    res = [f"(prove (forall ({' '.join([f'({s[1:]} U)' for s in sorted(collect_symbols(r[2]).union(collect_symbols(r[1]))) if s.startswith('?')])}) (= {to_str_no_qm(r[2])} {to_str_no_qm(r[3])})))\n" for r in rules]
    with open(f[:-7] + '.goal.th', 'w') as fp:
        fp.writelines(res)
