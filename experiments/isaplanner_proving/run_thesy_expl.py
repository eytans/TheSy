import shutil
import pathlib

from experiments import copy_tree_th_only
from experiments.thesy_runner import run_all
from experiments.stats_processor import write_stats


experiment_folder = pathlib.Path(__file__).parent
isaplanner_tests = experiment_folder / "isaplanner"
runner_path = experiment_folder.parent.parent / 'thesy_runner.py'

thesy_with_cs = experiment_folder / 'isaplanner_with_cs'
thesy_no_cs = experiment_folder / 'isaplanner_no_cs'
backup = experiment_folder / 'backup'
if not backup.exists():
    backup.mkdir()

if __name__ == '__main__':
    if thesy_no_cs.exists() or thesy_with_cs.exists():
        shutil.rmtree(backup)
        backup.mkdir()
    if thesy_no_cs.exists():
        shutil.move(thesy_no_cs, backup / thesy_no_cs.name)
    if thesy_with_cs.exists():
        shutil.move(thesy_with_cs, backup / thesy_with_cs.name)

    # Default proof mode is false so we are doing exploration
    copy_tree_th_only(isaplanner_tests, thesy_no_cs)
    run_all([thesy_no_cs], features='no_split')
    write_stats(thesy_no_cs)
    copy_tree_th_only(isaplanner_tests, thesy_with_cs)
    run_all([thesy_with_cs])
    write_stats(thesy_with_cs)

