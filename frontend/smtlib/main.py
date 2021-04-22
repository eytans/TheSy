from .import_smtlib import SmtLibDocument
from .case_splits import ExtractCaseSplits
import traceback
import argparse
from pysmt.environment import reset_env

def main(benchmark_dir, target_dir):
    # BENCHMARK_DIRS = ['benchmarks/cvc4-conj/original/benchmarks-dt/leon']
    # BENCHMARK_DIRS = ['/home/eytan.s/Apps/benchmarks/benchmarks/isaplanner_smt']
    # TARGET_DIRS = ['/home/eytan.s/Apps/benchmarks/benchmarks/isaplanner_smt_th']
    BENCHMARK_DIRS = [benchmark_dir]
    TARGET_DIRS = [target_dir]

    import os

    for td in TARGET_DIRS:
        try: os.makedirs(td)
        except FileExistsError: pass

    for (d, target_dir) in zip(BENCHMARK_DIRS, TARGET_DIRS):
        for fn in os.listdir(d):
            if os.path.isdir(os.path.join(d, fn)):
                continue
            print('--  %s  --' % fn)
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
    parser = argparse.ArgumentParser()
    parser.add_argument("benchmark_dir")
    parser.add_argument("target_dir")
    args = parser.parse_args()
    main(args.benchmark_dir, args.target_dir)

