# Tests for stats_processor.py. 
# Mainly testing that create_stats from experiments/tests/stats/ will work correctly.

import unittest
import pandas
import pathlib
import json
from collections import Counter

from experiments import experiments_dir
from experiments.stats_processor import create_stats

class TestStatsProcessor(unittest.TestCase):

    def test_create_stats(self):
        path = experiments_dir / 'test' / 'stats'
        stats = create_stats(path)
        self.assertTrue(stats['time'].apply(lambda x: x > 0).any())
        # self.assertTrue(stats['stop_reason'].apply(lambda x: x != "").any())
        self.assertTrue(stats['case_split_root_count'].apply(lambda x: x > 0).any())
        # self.assertTrue(stats['case_split_had_vacuity'].apply(lambda x: x > 0).any())
        self.assertTrue(stats['max_allocated'].apply(lambda x: x > 0).all())
        self.assertTrue(stats['total_allocated'].apply(lambda x: x > 0).all())
        