from .import_smtlib import SmtLibDocument
from .case_splits import ExtractCaseSplits
import traceback
from pysmt.environment import reset_env

def main():
    # BENCHMARK_DIRS = ['benchmarks/cvc4-conj/original/benchmarks-dt/leon']
    BENCHMARK_DIRS = ['/home/eytan.s/Apps/benchmarks/benchmarks/isaplanner_smt']
    TARGET_DIRS = ['/home/eytan.s/Apps/benchmarks/benchmarks/isaplanner_smt_thy']

    import os

    for td in TARGET_DIRS:
        try: os.makedirs(td)
        except FileExistsError: pass

    for (d, target_dir) in zip(BENCHMARK_DIRS, TARGET_DIRS):
        for fn in os.listdir(d):

            print('--  %s --' % fn)
            infile = open(os.path.join(d, fn))

            reset_env()
            try:
                doc = SmtLibDocument(infile)
            except:
                print(f"bad {fn}")
                print(traceback.format_exc())
                continue

            with open(os.path.join(target_dir, fn + '.th'), 'w') as outf:
                for el in doc:
                    print(el)
                    print(el, file=outf)

                # for srule in ExtractCaseSplits(doc).guess_rules():
                #     print(srule)
                #     print(srule, file=outf)

            print(';', set(doc.iter_used_symbols()))
            print(';', set(doc.iter_used_types()))


if __name__ == '__main__':
    main()

