import pandas
import os
import argparse
import json

from collections import Counter


def create_stats(path):
    keys_assertions = ['equiv_red_iterations', 'total_time', 'goals_proved', 'conjectures_proved', 'filtered_lemmas', 'total_allocated', 'max_allocated', 'file_name']

    jsons = []
    for fn in os.listdir(path):
        if fn.endswith(".stats.json"):
            with open(os.path.join(path, fn)) as f:
                d = json.load(f)
                d['file_name'] = fn
                if any(map(lambda k: not k in d, keys_assertions)):
                    print(f"missing key. keys: {list(d.keys())}")
                    continue
                count = 0
                had_vacuity = False
                if 'case_split_stats' in d and 'known_splits_text' in d['case_split_stats']:
                    count = len(d['case_split_stats']['known_splits_text'])
                    if 'vacuos_cases' in d['case_split_stats']:
                        had_vacuity = any(lambda x: x > 0, d['case_split_stats']['vacuos_cases'])
                d['case_split_root_count'] = count
                d['case_split_had_vacuity'] = had_vacuity
                del d['case_split_stats']
                jsons.append(d)

    df = pandas.DataFrame(jsons)
    res = pandas.DataFrame()
    res['time'] = None
    res['stop_reasons'] = None
    res['success'] = None
    res['lemma_count'] = None
    res['proofs_later_filtered'] = None
    res['case_split_root_count'] = None
    res['case_split_had_vacuity'] = None
    res['total_allocated'] = None
    res['max_allocated'] = None
    res['file_name'] = None
    if jsons:
        # Fix for empty dirs
        res['time'] = df['total_time'].apply(lambda d: d['secs'] + d['nanos']*10**-9)
        res['stop_reasons'] = df.equiv_red_iterations.apply(lambda v: sorted(Counter([list(v1[-1]['stop_reason'].keys())[0] if v1[-1]['stop_reason'] != "Saturated" else "Saturated" for v1 in v]).keys()))
        res['success'] = df['goals_proved'].apply(lambda gp: len(gp) > 0)
        res['lemma_count'] = df['conjectures_proved'].apply(len)
        res['proofs_later_filtered'] = df['filtered_lemmas'].apply(len)
        res['case_split_root_count'] = df['case_split_root_count']
        res['case_split_had_vacuity'] = df['case_split_had_vacuity']
        res['total_allocated'] = df['total_allocated']
        res['max_allocated'] = df['max_allocated']
        res['file_name'] = df['file_name']
    return res


def write_stats(path):
    res = create_stats(path)
    res.to_csv(os.path.join(path, 'stats.csv'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('path')
    args = parser.parse_args()
    write_stats(args.path)
