from unittest import TestCase
from experiments import experiments_dir
from pathlib import Path

from experiments.stats_processor import create_stats
from experiments.cvc4_newth_alltogether.similar_cases import main


class Test(TestCase):
    def test_find_similar(self):
        in_dir = experiments_dir / 'test' / 'similar'
        main(in_dir)
        out_file = in_dir / 'subdir' / 'bsearch-tree-goal1.at'
        self.assertTrue(out_file.exists())
        self.assertTrue(len(out_file.read_text()) > 1)