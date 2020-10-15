import re
import sys
import os
import os.path
import subprocess
import json

BUILD_CMD = ["cargo", "build", "--release", "--features", "stats", "--package", "TheSy", "--bin", "TheSy"]



def main():
    THESY_DIR = 'frontend/benchmarks/isaplanner_smt_nosortnat_th'
    INPUT_THEORY = 'prop_%s.smt20.smt2.th'
    OUTPUT_THESY = 'prop_%s.smt20.smt2.res.th'
    HIPSTER_DIR = 'frontend/benchmarks/isaplanner/via_hipster'
    OUTPUT_HIPSTER = 'Prop_%s.goals.th'

    prepare()

    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('benchmarks', nargs='*')
    a.add_argument('--show-all', action='store_true')
    a = a.parse_args()

    results = ResultStore()

    for bm in expand_benchmarks(a.benchmarks):
        preamble_fn = os.path.join(THESY_DIR, INPUT_THEORY % bm)
        thesy_rules_fn = os.path.join(THESY_DIR, OUTPUT_THESY % bm)
        hipster_goals_fn = os.path.join(HIPSTER_DIR, OUTPUT_HIPSTER % bm)

        for fn in [preamble_fn, thesy_rules_fn, hipster_goals_fn]:
            print(fn)
        print

        tmp_fn = f'/tmp/task-{bm}.th'
        with open(tmp_fn, 'w') as outf:
            for fn in [preamble_fn, thesy_rules_fn, hipster_goals_fn]:
                print(open(fn).read(), file=outf)
        
        goals = get_goals(open(hipster_goals_fn).read())

        for g in goals: print(f" (?)  {g}")

        p = subprocess.run(['./target/release/TheSy', '-c', tmp_fn], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
        print(p.stderr.decode(), file=sys.stderr)
        proved = get_proved(p.stdout.decode())

        print(f"Prop_{bm}    {len(proved)}/{len(goals)}")
        r = results.get(bm)
        r['hipster < thesy'] = {
            'summary': f"{len(proved)}/{len(goals)}", 'goals': goals, 'proved': proved
        }
        results.save()

    if a.show_all:
        if a.benchmarks: print('-' * 60)
        stats = {'goals': 0, 'proved': 0, 'theories': 0}
        for k, v in results.d.items():
            if 'hipster < thesy' in v:
                print(f"Prop_{k}       ", v['hipster < thesy']['summary'])
                stats['theories'] += 1
                stats['goals'] += len(v['hipster < thesy']['goals'])
                stats['proved'] += len(v['hipster < thesy']['proved'])

        print()
        print(f"Proved {stats['proved']}/{stats['goals']} lemmas in {stats['theories']} theories")


def prepare():
    p = subprocess.run(BUILD_CMD, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    if p.returncode != 0:
        print(p.stderr.decode())
        print(p.stdout.decode())
        exit()

def expand_benchmarks(bms):
    for bm in bms:
        if '..' in bm:
            f, t = bm.split('..')
            for i in range(int(f), int(t) + 1): yield '%02d' % i
        else:
            yield bm

def get_proved(out_text):
    PR_RE = re.compile(r'^proved: (.*)', re.MULTILINE)
    return list(PR_RE.findall(out_text))

def get_goals(goals_text):
    GOAL_RE = re.compile(r'^\(prove (.*)\)', re.MULTILINE)
    return list(GOAL_RE.findall(goals_text))



class ResultStore:
    def __init__(self, fn='head_to_head.json'):
        if os.path.exists(fn):
            self.d = json.load(open(fn))
        else:
            self.d = {}
        self.filename = fn
    
    def get(self, key):
        if key not in self.d: self.d[key] = {}
        return self.d[key]

    def put(self, key, value):
        self.d[key] = value
        self.save()

    def save(self):
        with open(self.filename, 'w') as outf:
            json.dump(self.d, outf)


main()
