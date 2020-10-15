import os
import os.path



def main():
    THESY_DIR = 'frontend/benchmarks/isaplanner_smt_nosortnat_th'
    INPUT_THEORY = 'prop_%s.smt20.smt2.th'
    OUTPUT_THESY = 'prop_%s.smt20.smt2.res.th'
    HIPSTER_DIR = 'frontend/benchmarks/isaplanner/via_hipster'
    OUTPUT_HIPSTER = 'Prop_%s.goals.th'

    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('benchmarks', nargs='+')
    a = a.parse_args()

    for bm in a.benchmarks:
        preamble_fn = os.path.join(THESY_DIR, INPUT_THEORY % bm)
        thesy_rules_fn = os.path.join(THESY_DIR, OUTPUT_THESY % bm)
        hipster_goals_fn = os.path.join(HIPSTER_DIR, OUTPUT_HIPSTER % bm)

        tmp_fn = f'/tmp/task-{bm}.th'
        with open(tmp_fn, 'w') as outf:
            for fn in [preamble_fn, thesy_rules_fn, hipster_goals_fn]:
                print(open(fn).read(), file=outf)
        
        os.system('./target/release/TheSy -c ' + tmp_fn)

        print(open(hipster_goals_fn).read())


main()
