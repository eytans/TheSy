from unittest import TestCase
from experiments import experiments_dir
from pathlib import Path

from experiments.stats_processor import create_stats
from experiments.thesy_runner import run_all


class Test(TestCase):
    def test_run_all(self):
        no_split_path = experiments_dir / 'test' / 'no_split'
        rest_path = experiments_dir / 'test' / 'rest'
        run_all([no_split_path], True, 'no_split')
        self.assertFalse(create_stats(no_split_path).iloc[0]['success'])
        run_all([no_split_path], True)
        self.assertTrue(create_stats(no_split_path).iloc[0]['success'])
        run_all([no_split_path], False, 'no_split')
        self.assertFalse(create_stats(no_split_path).iloc[0]['success'])

