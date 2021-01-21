import sys
import os
from os import system
from argparse import ArgumentParser

dir_half_s = r'D:\work\synthesis\TheSy_dev\experiments\case_split_yn\clam_no_expl_split/'
dir_yes_s = r'D:\work\synthesis\TheSy_dev\experiments\case_split_yn\clam_full_cs'
dir_no_s = r'D:\work\synthesis\TheSy_dev\experiments\case_split_yn\clam_no_cs'

if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('split', choices=['yes', 'half', 'no'])
    parser.add_argument('-n', '--processnum', default=8)
    args = parser.parse_args()

    if args.split == 'yes':
        dir = dir_yes_s
        features = ''
    elif args.split == 'half':
        dir = dir_half_s
        features = '--features no_expl_split'
    else:
        dir = dir_no_s
        features = '--features no_split'


    # files = open('experiments/case_split_yn/isaplanner_with_cs').read().strip().split()
    # skip_files = [f for f in os.listdir(dir) if f.endswith('.th') and (not f.endswith('res.th')) and f.strip() not in files]

    system(f'python thesy_runner.py -m 16 -t 15 -n {args.processnum} {dir} {features}')