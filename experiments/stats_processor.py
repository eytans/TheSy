import pandas
import os
import argparse
import json

from collections import Counter


def create_stats(path):
    jsons = []
    for fn in os.listdir(path):
        if fn.endswith(".json"):
            with open(os.path.join(path, fn)) as f:
                d = json.load(f)
                d['file_name'] = fn
                jsons.append(d)

    df = pandas.DataFrame(jsons)
    res = pandas.DataFrame()
    print(df.columns)
    res['time'] = df['total_time'].apply(lambda d: d['secs'] + d['nanos']*10**-9)
    res['stop_reasons'] = df.equiv_red_iterations.apply(lambda v: sorted(Counter([list(v1[-1]['stop_reason'].keys())[0] if v1[-1]['stop_reason'] != "Saturated" else "Saturated" for v1 in v]).keys()))
    res['proved_count'] = df['conjectures_proved'].apply(lambda cs: len(cs))
    res['success'] = df['goals_proved'].apply(lambda gp: len(gp) > 0)
    res['lemma_count'] = df['conjectures_proved'].apply(len)
    res['proofs_later_filtered'] = df['filtered_lemmas'].apply(len)
    res['file_name'] = df['file_name']

    res.to_csv(os.path.join(path, 'stats.csv'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('path')
    args = parser.parse_args()

    create_stats(args.path)