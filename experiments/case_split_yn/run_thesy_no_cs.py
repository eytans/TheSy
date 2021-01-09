import sys
import os
from os import system
from argparse import ArgumentParser

dir_no_s = 'experiments/case_split_yn/isaplanner_tests_no_expl_split/'
dir_yes_s = 'experiments/case_split_yn/isaplanner_tests/'

parser = ArgumentParser()
parser.add_argument('split', choices=['yes', 'no'])
args = parser.parse_args()

split = args.split == 'yes'
if split:
    dir = dir_yes_s
    features = ''
else:
    dir = dir_no_s
    features = '--features no_expl_split'

# files = open('experiments/case_split_yn/isaplanner_with_cs').read().strip().split()
# skip_files = [f for f in os.listdir(dir) if f.endswith('.th') and (not f.endswith('res.th')) and f.strip() not in files]

system(f'python thesy_runner.py {dir} {features}')