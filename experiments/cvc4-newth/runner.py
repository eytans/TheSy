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


def results_dir(features, split_depth):
    """Return path to results dir for given features"""
    return current_exp / now_str / f"case_split_proof_split_{split_depth}_{'_'.join(features)}"


def run(prove_timeout=None, rerun=None, features=None, split_depth=None):
    """Run the experiment with given features, timeout, and split depth"""
    if features is None:
        features = []
    if prove_timeout is None:
        prove_timeout = 10
    if split_depth is None:
        split_depth = 4
    res_dir = results_dir(features, split_depth)
    copy_tree_th_only(tests_dir, res_dir)

    tests_subdirs = [d for d in res_dir.iterdir() if d.is_dir()]
    tests_subdirs = tests_subdirs + [d for x in tests_subdirs for d in x.iterdir() if d.is_dir()]
    print(f"Running with features: {features} on testcases: {tests_subdirs}")
    run_all(tests_subdirs,
            mode=thesy_runner.ThesyMode.CheckEquiv,
            timeout=prove_timeout,
            rerun=rerun,
            prover_split_d=str(split_depth),
            memorylimit=8,
            multiprocess=False,
            processnum=1,
            features=" ".join(features))
            # memorylimit=8, multiprocess=False, processnum=1, features=" ".join(features), base_path=tests_dir, out_path=res_dir)
    tests_stats = pandas.concat([create_stats(d) for d in tests_subdirs], keys=[d.name for d in tests_subdirs])
    fixed_res_path = res_dir / res_path.name
    tests_stats.to_csv(fixed_res_path)


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('-t', '--timeout', default=None, type=int)
    parser.add_argument('-n', '--norerun', action='store_true', default=False)
    args = parser.parse_args()

    todo_features = [["split_colored"], ["split_no_cremove"], ["split_no_cmemo"], ["split_clone"]]
    todo_features = [fs + ["stats"] for fs in todo_features]

    split_depths = [1, 2, 3, 4, 5, 6]

    for split_depth in split_depths:
        for features in todo_features:
            run(rerun=not args.norerun, features=features, split_depth=split_depth)
