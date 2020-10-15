from .import_lemmas import TheoryDocument



def find_in_path(filename: str, path: [str]):
    import os.path
    for d in path:
        full = os.path.join(d, filename)
        if os.path.exists(full): return full
    return None


def main():
    BENCHMARK_DIRS = ['frontend/benchmarks/isaplanner/via_hipster']
    COGNATE_SMT_DIRS = ['frontend/benchmarks/isaplanner_smt_nosortnat']
    TARGET_DIRS = [] #'frontend/benchmarks/isaplanner']

    import os

    for td in TARGET_DIRS:
        try: os.makedirs(td)
        except FileExistsError: pass

    stats = {'theories': 0, 'lemmas': 0, 'mismatch': []}

    for d in BENCHMARK_DIRS:
        for fn in ['Prop_18.thy']: #os.listdir(d):
            if fn.endswith('.thy'):
                print('--  %s  --' % fn)
                infile = open(os.path.join(d, fn))

                doc = TheoryDocument(infile)

                print(doc.datatypes, doc.ctors, doc.funcs)

                if fn in UGLY_MANUAL_ALIASES:
                    cognate_aliases = UGLY_MANUAL_ALIASES[fn]
                else:
                    smtfn = find_in_path(fn.lower().replace('.thy', '.smt20.smt2'), COGNATE_SMT_DIRS)
                    if smtfn:
                        with open(smtfn) as smtfile:
                            cognate_aliases = get_func_aliases(fn, doc, smtfile, stats)
                    else:
                        cognate_aliases = None

                lemfn = os.path.join(d, fn + '.log')
                if os.path.exists(lemfn):
                    lemfile = open(lemfn)

                    doc = TheoryDocument(lemfile).merge(doc)
                    if cognate_aliases: doc.aliases = cognate_aliases
                    with open(os.path.join(d, fn.replace('.thy', '.goals.th')), 'w') as outf:
                        for t, lem in doc.lemmas:
                            goal = doc.export_lemma(lem, as_goal=True)
                            if goal:
                                print(f" - {goal}")
                                print(goal, file=outf)
                            #print(f" - {t} {lem}")
                            #print(f"   {doc.find_vars(lem[0])} {doc.export_lemma(lem)}")

                    with open(os.path.join(d, fn.replace('.thy', '.rules.th')), 'w') as outf:
                        for t, lem in doc.lemmas:
                            for rule in doc.export_rules(lem):
                                #print(f" + {rule}")
                                print(rule, file=outf)

                    if doc.lemmas:
                        stats['theories'] += 1
                        stats['lemmas'] += len(doc.lemmas)

    print(f"{stats['lemmas']} lemmas in {stats['theories']} theories")

    for (fn, th, smt) in stats['mismatch']:
        print(f"{fn}:  ", th, ' %% ', smt)


def grab_smt_declares(infile):
    import re
    decl = re.compile(r'\(declare-fun \|?(.*?)\|? ')
    for line in infile:
        mo = decl.match(line)
        if mo: yield mo.group(1)

def get_func_aliases(name, doc, infile, stats):
    cognate_funcs = [f for f in grab_smt_declares(infile)
                        if not f.startswith('apply')]
    print('%%', cognate_funcs)
    common = set(doc.funcs) & set(cognate_funcs)
    th, smt = [[f for f in l if f not in common]
                for l in [doc.funcs, cognate_funcs]]
    if len(th) != len(smt):
        stats['mismatch'].append((name, th, smt))

    return dict(zip(th, smt))


UGLY_MANUAL_ALIASES = {
    'Prop_02.thy': {'x': '==', 'y': '++', 'twoSpec': '+2'},
    'Prop_03.thy': {'x': '==', 'y': '++', 'twoSpec': '<=2'},
    'Prop_18.thy': {'twoSpectwoSpec': '+2', 'twoSpec': '<=2'},
    'Prop_21.thy': {'twoSpectwoSpec': '+2', 'twoSpec': '<=2'},
    'Prop_55.thy': {'x': '++', 'twoSpec': '-2'},
    'Prop_65.thy': {'twoSpec': '<2', 'twoSpectwoSpec': '+2'},
    'Prop_69.thy': {'twoSpec': '<=2', 'twoSpectwoSpec': '+2'},
    'Prop_54.thy': {'twoSpec': '-2', 'twoSpectwoSpec': '+2'},
    'Prop_72.thy': {'x': '++', 'twoSpec': '-2'},
    'Prop_75.thy': {'x': '==', 'twoSpec': '+2'},
    'Prop_76.thy': {'y': '++', 'x': '=='},
    'Prop_78.thy': {'x': '&&', 'twoSpec': '<=2'}
}


main()