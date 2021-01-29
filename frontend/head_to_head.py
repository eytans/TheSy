import re
import sys
import os
import os.path
import subprocess
import json

import argparse


BUILD_CMD = ["cargo", "build", "--release", "--features", "stats",
             "--package", "TheSy", "--bin", "TheSy"]


THESY_DIR = 'frontend/benchmarks/isaplanner_smt_nosortnat_th'
THESY_PREAMBLE = 'prop_%s.smt20.smt2.th'
THESY_RULES = 'prop_%s.smt20.smt2.res.th'
THESY_GOALS = 'prop_%s.smt20.smt2.goal.th'
HIPSTER_DIR = 'frontend/benchmarks/isaplanner/via_hipster'
HIPSTER_RULES = 'Prop_%s.rules.th'
HIPSTER_GOALS = 'Prop_%s.goals.th'

THESY_STATS = 'prop_%s.smt20.smt2.stats.json'
HIPSTER_TIME = 'Prop_%s.thy.time'


def main():
    a = argparse.ArgumentParser()
    a.add_argument('benchmarks', nargs='*')
    a.add_argument('--dir', default='both',
                   help="direction: h-t (hipster < thesy), t-h (thesy < hipster), " +
                        "or both [default: both]")
    a.add_argument('--show-all', action='store_true',
                   help="print accumulated results in a (plain-text) table")
    a.add_argument('--build', action=YesNo, default=True, 
                   help="build first, using cargo [default: yes]")
    a.add_argument('--scatter', action='store_true')
    a.add_argument('--cactus', action='store_true',
                   help="generate cactus plot 🌵")
    a = a.parse_args()

    if a.build: prepare()

    results = ResultStore()

    for bm in expand_benchmarks(a.benchmarks):
        preamble_fn = os.path.join(THESY_DIR, THESY_PREAMBLE % bm)
        thesy_rules_fn = os.path.join(THESY_DIR, THESY_RULES % bm)
        thesy_goals_fn = os.path.join(THESY_DIR, THESY_GOALS % bm)
        hipster_rules_fn = os.path.join(HIPSTER_DIR, HIPSTER_RULES % bm)
        hipster_goals_fn = os.path.join(HIPSTER_DIR, HIPSTER_GOALS % bm)

        r = results.get(bm)
        if a.dir == 'h-t' or a.dir == 'both':
            r['hipster < thesy'] = compare_theories(bm, preamble_fn, thesy_rules_fn, hipster_goals_fn)
        if a.dir == 't-h' or a.dir == 'both':
            r['thesy < hipster'] = compare_theories(bm, preamble_fn, hipster_rules_fn, thesy_goals_fn)
        results.save()

    extract_times(results)

    if a.show_all:
        if a.benchmarks: print('-' * 60)
        show_all_results(results)
        export_csv(results)
    
    if a.scatter:
        generate_scatter(results)
        
    if a.cactus:
        generate_cactus(results)
        


def prepare():
    p = subprocess.run(BUILD_CMD, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    if p.returncode != 0:
        print(p.stderr.decode())
        print(p.stdout.decode())
        exit()

    if not os.path.exists('/tmp/thesy'): os.makedirs('/tmp/thesy')


def expand_benchmarks(bms):
    for bm in bms:
        if '..' in bm:
            f, t = bm.split('..')
            for i in range(int(f), int(t) + 1): yield '%02d' % i
        else:
            yield bm


def extract_times(results):
    for k, v in results.d.items():
        v['thesy time'] = get_time_from_json(os.path.join(THESY_DIR, THESY_STATS % k))
        v['hipster time'] = get_time_from_hms(os.path.join(HIPSTER_DIR, HIPSTER_TIME % k))


def show_all_results(results):
    stats = {d: {'goals': 0, 'proved': 0, 'theories': 0} 
             for d in ['hipster < thesy', 'thesy < hipster']}
    def accumulate_stats(d, item):
        stats[d]['theories'] += 1
        stats[d]['goals'] += len(item['goals'])
        stats[d]['proved'] += len(item['proved'])

    print('Benchmark    Hipster < TheSy          TheSy < Hipster     TheSy Time     Hipster Time')
        
    for k, v in results.d.items():
        cells = []
        for d in ['hipster < thesy', 'thesy < hipster']:
            if d in v:
                cells += [v[d]['summary']]
                accumulate_stats(d, v[d])
            else:
                cells += ['??']
        
        thesy_time = get_time_from_json(os.path.join(THESY_DIR, THESY_STATS % k))
        cells += [thesy_time or 't/o']

        hipster_time = get_time_from_hms(os.path.join(HIPSTER_DIR, HIPSTER_TIME % k))
        cells += [hipster_time or 't/o']

        print(f"Prop_{k}        {' '.join('%12s' % s for s in cells)}")

    print()
    for d, st in stats.items():
        print(f"{d}:  Proved {st['proved']}/{st['goals']} lemmas in {st['theories']} theories")


def export_csv(results, out_filename="head_to_head.csv"):
    export_data = []
    for k, v in results.d.items():
        export_cells = [f"Prop_{k}"]
        for d in ['hipster < thesy', 'thesy < hipster']:
            if d in v:
                export_cells += [len(v[d]['goals']), len(v[d]['proved'])]

        thesy_time = get_time_from_json(os.path.join(THESY_DIR, THESY_STATS % k))
        export_cells += [thesy_time or 3600]

        hipster_time = get_time_from_hms(os.path.join(HIPSTER_DIR, HIPSTER_TIME % k))
        export_cells += [hipster_time or 3600]

        export_data.append(export_cells)
    
    import csv
    with open(out_filename, 'w') as csvout:
        w = csv.writer(csvout)
        w.writerow(['Benchmark', 'Hipster found', 'Hipster < TheSy', 'TheSy found', 'TheSy < Hipster', 'TheSy Time', 'Hipster Time'])
        for row in export_data:
            w.writerow(row)


def compare_theories(bm, preamble_fn, assumed_rules_fn, goals_fn):
    for fn in [preamble_fn, assumed_rules_fn, goals_fn]:
        print(fn)
    print()

    tmp_fn = f'/tmp/thesy/task-{bm}.th'
    with open(tmp_fn, 'w') as outf:
        for fn in [preamble_fn, assumed_rules_fn, goals_fn]:
            print(open(fn).read(), file=outf)
    
    goals = get_goals(open(goals_fn).read())

    for g in goals: print(f" (?)  {g}")

    p = subprocess.run(['./target/release/TheSy', '-c', tmp_fn],
                       stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    print(p.stderr.decode(), file=sys.stderr)
    proved = get_proved(p.stdout.decode())

    for l in proved: print(f" (!)  {l}")

    print(f"Prop_{bm}    {len(proved)}/{len(goals)}")
    return {
        'summary': f"{len(proved)}/{len(goals)}", 'goals': goals, 'proved': proved
    }


def generate_scatter(results):
    print("h-t      t-h")
    for k, v in results.d.items():
        cells = []
        for d in ['hipster < thesy', 'thesy < hipster']:
            if d in v:
                nom, den = len(v[d]['proved']), len(v[d]['goals'])
                cells += [nom / den if den else 1.0]

        print("%5.5f   %5.5f" % tuple(cells))
        

def generate_cactus(results):
    TIMEOUT = 3600
    data = {}
    for sy in ['thesy', 'hipster']:
        key = '{} time'.format(sy)
        bm_time = [v[key] or TIMEOUT for v in results.d.values()]
        acc = [0]
        for tm in sorted(bm_time): acc.append(acc[-1] + tm)
        data[sy] = acc

    print("n      thesy        hipster")
    for i, row in enumerate(zip(data['thesy'], data['hipster'])):
        print("%4d  %10.2f  %15.2f" % ((i,) + row))
        

# Some low-level utils

def get_proved(out_text):
    PR_RE = re.compile(r'^proved: (.*)', re.MULTILINE)
    return list(PR_RE.findall(out_text))

def get_goals(goals_text):
    GOAL_RE = re.compile(r'^\(prove (.*)\)', re.MULTILINE)
    return list(GOAL_RE.findall(goals_text))

def get_time_from_json(json_fn):
    if os.path.exists(json_fn):
        r = json.load(open(json_fn))
        tm = r['total_time']
        return tm['secs'] + tm['nanos'] * 1e-9
    else:
        return None

def get_time_from_hms(hms_fn):
    import datetime
    if os.path.exists(hms_fn):
        hms = datetime.datetime.strptime(open(hms_fn).read(),  "%H:%M:%S.%f")
        return hms.hour * 3600 + hms.minute * 60 + hms.second + hms.microsecond * 1e-6
    else:
        return None


# https://stackoverflow.com/a/20422915/37639
class YesNo(argparse.Action):
    def __init__(self, option_strings, dest, default=None, required=False, help=None):

        if default is None:
            raise ValueError('Must provide a default with yes/no action')
        if len(option_strings) != 1:
            raise ValueError('Only single argument is allowed with yes/no action')
        opt = option_strings[0]
        if not opt.startswith('--'):
            raise ValueError('Yes/no arguments must be prefixed with --')

        opt = opt[2:]
        opts = ['--' + opt, '--no-' + opt]
        super(YesNo, self).__init__(opts, dest, nargs=0, const=None, 
                default=default, required=required, help=help)
    def __call__(self, parser, namespace, values, option_strings=None):
        if option_strings.startswith('--no-'):
            setattr(namespace, self.dest, False)
        else:
            setattr(namespace, self.dest, True)


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
