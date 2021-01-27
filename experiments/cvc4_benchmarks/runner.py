import shutil
import pandas

from experiments.stats_processor import create_stats
from experiments.thesy_runner import run_all
from experiments import experiments_dir, project_root, copy_tree_th_only

current_exp = experiments_dir / 'cvc4_benchmarks'
tests_dir = current_exp / 'tests'
explr_dir = current_exp/ 'expl'
proof_after_expl_dir = current_exp/ 'proof_after_expl'
orig_tests = project_root / 'frontend' / 'benchmarks' / 'cvc4_translated'
res_path = current_exp / 'stats.csv'


def run():
    if explr_dir.exists():
        shutil.rmtree(explr_dir)
    copy_tree_th_only(orig_tests, explr_dir)
    expl_subdirs = [d for d in explr_dir.iterdir() if d.is_dir()]
    run_all(expl_subdirs, prove=False, timeout=180)
    expl_stats = pandas.concat([create_stats(d) for d in expl_subdirs], keys=[d.name for d in expl_subdirs])
    if tests_dir.exists():
        shutil.rmtree(tests_dir)
    copy_tree_th_only(orig_tests, tests_dir)
    tests_subdirs = [d for d in tests_dir.iterdir() if d.is_dir()]
    run_all(tests_subdirs, prove=True, timeout=5)
    tests_stats = pandas.concat([create_stats(d) for d in tests_subdirs], keys=[d.name for d in tests_subdirs])
    if proof_after_expl_dir.exists():
        shutil.rmtree(proof_after_expl_dir)
    copy_tree_th_only(orig_tests, proof_after_expl_dir)
    all_res_paths = explr_dir.glob("**/*.res.th")
    for p in all_res_paths:
        # Move results into proof file
        rel = p.relative_to(explr_dir)
        to_update = proof_after_expl_dir / rel.with_name(rel.name[:-6] + 'th')
        with to_update.open('a') as updated:
            new_rules = p.read_text()
            updated.write(new_rules)
    proof_expl_subdirs = [d for d in proof_after_expl_dir.iterdir() if d.is_dir()]
    run_all(proof_expl_subdirs, prove=True, timeout=5)
    all_stats = pandas.concat([create_stats(d) for d in proof_expl_subdirs], keys=[d.name for d in proof_expl_subdirs])
    concated = pandas.concat([tests_stats, expl_stats, all_stats], keys=['no expl proofs', 'expl', 'with expl proofs'])
    concated.to_csv(res_path)


if __name__ == '__main__':
    run()
