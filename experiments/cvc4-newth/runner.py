import datetime
import shutil
import pandas

from argparse import ArgumentParser

from experiments.stats_processor import create_stats
from experiments.thesy_runner import run_all
from experiments import experiments_dir, project_root, copy_tree_th_only, thesy_runner

current_exp = experiments_dir / 'cvc4-newth'
tests_dir = current_exp / 'testcases'
res_path = current_exp / 'stats.csv'

# take time now into format suiting to dirs
now = datetime.datetime.now()
now_str = now.strftime("%Y-%m-%d_%H-%M-%S")
def results_dir(features):
    return current_exp / now_str / f"case_split_proof_{'_'.join(features)}"


def run(prove_timeout=None, rerun=None, features=None):
    if features is None:
        features = []
    if prove_timeout is None:
        prove_timeout = 10
    copy_tree_th_only(tests_dir, results_dir(features))

    tests_subdirs = [d for d in tests_dir.iterdir() if d.is_dir()]
    tests_subdirs = tests_subdirs + [d for x in tests_subdirs for d in x.iterdir() if d.is_dir()]
    print(f"Running with features: {features} on testcases: {tests_subdirs}")
    run_all(tests_subdirs, mode=thesy_runner.ThesyMode.CheckEquiv, timeout=prove_timeout, rerun=rerun, prover_split_d="4",
            memorylimit=8, multiprocess=False, processnum=1, features=" ".join(features), base_path=tests_dir, out_path=results_dir(features))
    tests_stats = pandas.concat([create_stats(d) for d in tests_subdirs], keys=[d.name for d in tests_subdirs])
    fixed_res_path = results_dir(features) / res_path.name
    tests_stats.to_csv(fixed_res_path)


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('-t', '--timeout', default=None, type=int)
    parser.add_argument('-n', '--norerun', action='store_true', default=False)
    args = parser.parse_args()

    todo_features = [["split_colored"], ["split_no_cremove"], ["split_no_cmemo"], ["split_clone"],
                     ["split_clone", "keep_splits"]]
    todo_features = [fs + ["stats"] for fs in todo_features]

    for features in todo_features:
        run(rerun=not args.norerun, features=features)
