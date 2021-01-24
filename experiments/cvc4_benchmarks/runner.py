import argparse
import shutil
import pathlib

from thesy_runner import run_all
from ... import experiments_dir, project_root

tests_dir = experiments_dir / 'cvc4_benchmarks' / 'tests'
explr_dir = experiments_dir / 'cvc4_benchmarks' / 'expl'
proof_after_expl_dir = experiments_dir / 'cvc4_benchmarks' / 'proof_after_expl'
orig_tests = project_root / 'frontend' / 'benchmarks' / 'cvc4_translated'


def run():
    if tests_dir.exists():
        shutil.rmtree(tests_dir)
    shutil.copytree(orig_tests, tests_dir)
    run_all([d for d in tests_dir.iterdir() if d.is_dir()], True, timeout=5)
    if explr_dir.exists():
        shutil.rmtree(explr_dir)
    shutil.copytree(orig_tests, explr_dir)
    run_all([d for d in explr_dir.iterdir() if d.is_dir()], False, timeout=180)
    if proof_after_expl_dir.exists():
        shutil.rmtree(proof_after_expl_dir)
    shutil.copytree(orig_tests, proof_after_expl_dir)
    all_res_paths = explr_dir.glob("**/*.res.th")
    for p in all_res_paths:
        # Move results into proof file
        rel = p.relative_to(explr_dir)
        to_update = proof_after_expl_dir / rel.with_name(rel.name[:-6] + 'th')
        with to_update.open('a') as updated:
            new_rules = p.read_text()
            updated.write(new_rules)
    run_all([d for d in proof_after_expl_dir.iterdir() if d.is_dir()], True, timeout=5)