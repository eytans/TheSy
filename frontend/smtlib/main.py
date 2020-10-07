from import_smtlib import SmtLibDocument
from case_splits import ExtractCaseSplits



def main():
    BENCHMARK_DIRS = ['benchmarks/cvc4-conj/original/benchmarks-dt/isaplanner']
    TARGET_DIR = '/tmp/thesy'

    import os

    try: os.makedirs(TARGET_DIR)
    except FileExistsError: pass

    for d in BENCHMARK_DIRS:
        for fn in ['goal3.smt2']: #os.listdir(d):
            print('--  %s --' % fn)
            infile = open(os.path.join(d, fn))

            doc = SmtLibDocument(infile)
            with open(os.path.join(TARGET_DIR, fn + '.th'), 'w') as outf:
                for el in doc:
                    print(el)
                    print(el, file=outf)

                for srule in ExtractCaseSplits(doc).guess_rules():
                    print(srule)
                    print(srule, file=outf)

            print(';', set(doc.iter_used_symbols()))
            print(';', set(doc.iter_used_types()))



if __name__ == '__main__':
    main()

