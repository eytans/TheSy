import os
import sys
import subprocess

from argparse import ArgumentParser

experiment_folder = os.path.dirname(sys.argv[0])
isaplanner_tests = os.path.join(experiment_folder, "isaplanner")
runner_path = os.path.join(experiment_folder, os.path.pardir, os.path.pardir, 'thesy_runner.py')

if __name__ == '__main__':
    # parser = ArgumentParser()
    # args = parser.parse_args()

    # Default proof mode is false so we are doing exploration
    subprocess.run(['python', runner_path, isaplanner_tests])
