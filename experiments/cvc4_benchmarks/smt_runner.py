import subprocess
import argparse
import pathlib
import multiprocessing
import time
import csv

parser = argparse.ArgumentParser()
parser.add_argument('exec')
parser.add_argument('run_type', choices=['cvc4', 'cvc4_ig', 'z3'])
parser.add_argument('run_folder')
parser.add_argument('--threads', default=None)
args = parser.parse_args()

CMD_CVC4_IG = [args.exec, '--lang', 'smtlib2', '--tlimit=300000',  '--quant-ind', '--quant-cf', '--conjecture-gen', '--conjecture-gen-per-round=3', '--full-saturate-quant']
CMD_CVC4 = [args.exec, '--lang', 'smtlib2', '--tlimit=300000', '--quant-cf', '--full-saturate-quant']
CMD_Z3 = [args.exec, '-smt2', '-T:300']
if args.run_type == 'cvc4_ig':
    CMD = CMD_CVC4_IG
elif args.run_type == 'cvc4':
    CMD = CMD_CVC4
elif args.run_type == 'z3':
    CMD = CMD_Z3
path = pathlib.Path(args.run_folder)
todo = list(path.glob('**/*.smt2'))

def run_cvc4(f):
    start = time.time()
    res = subprocess.check_output(CMD + [f]).decode('utf-8')
    return (time.time() - start, res.strip() == 'unsat')

pool = multiprocessing.Pool(int(args.threads))
result = pool.map(run_cvc4, todo) 
with open(f'results_{args.run_type}.csv', 'w+', newline ='') as f:
    write = csv.writer(f) 
    write.writerows([[x, y, z] for ((x, y), z) in zip(result, todo)])