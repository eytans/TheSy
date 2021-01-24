import os
import argparse
import shutil
import subprocess
import multiprocessing
import pathlib

from datetime import datetime
from cgroups import Cgroup
from . import executable_release, project_root, cargo_path

project_dir = project_root

BUILD_CMD = [str(cargo_path), "build", "--release", "--features", "stats", "--package", "TheSy", "--bin", "TheSy"]
CMD = [str(executable_release)]

# First we create the cgroup 'charlie' and we set it's cpu and memory limits
cg = Cgroup('thesy_cgroup')


# Then we a create a function to add a process in the cgroup
def in_my_cgroup():
    pid = os.getpid()
    cg = Cgroup('thesy_cgroup')
    cg.add(pid)


def run_thesy(fn_to):
    fn, to = fn_to
    in_my_cgroup()
    print(f"running {fn}")
    try:
        cmd = [s for s in CMD]
        cmd.append(fn)
        print(cmd)
        res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=to)
        out = res.stdout.decode("utf8")
        error = res.stderr.decode("utf8")
    except subprocess.TimeoutExpired:
        out = ""
        error = "Timeout Exception"
    with open(fn + ".out", 'w') as f:
        f.write(out)
    with open(fn + ".err", 'w') as f:
        f.write(error)
    print("Done with " + os.path.basename(fn))
    # with open(fn + ".json", 'w') as f:


def run_all(dirs, prove=False, features="", skip=None, timeout=60, processnum=20, memorylimit=32):
    if skip is None:
        skip = []
    to = timeout * 60
    if prove:
        CMD.append('--prove')
    BUILD_CMD[4] = (BUILD_CMD[4] + " " + features).strip()
    p = subprocess.run(BUILD_CMD, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    if p.returncode != 0:
        print(p.stderr.decode())
        print(p.stdout.decode())
        exit()
    print("Build done")
    inputdirs = dirs
    files = [(os.path.join(folder, fn), to) for folder in inputdirs for fn in os.listdir(folder) if fn.endswith(".th") and (not fn.endswith("res.th")) and fn not in skip]
    # isa_files = ["./temp/" + f for f in isa_files]
    cg.set_memory_limit(memorylimit, 'gigabytes')
    pn = processnum
    pool = multiprocessing.Pool(pn)
    pool.map(run_thesy, files)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("inputdir", nargs='+')
    parser.add_argument('-p', '--prove', action='store_true', default=False)
    parser.add_argument('-f', '--features', default="")
    parser.add_argument('--skip', nargs='*', default=None)
    parser.add_argument('-t', '--timeout', default=60)
    parser.add_argument('-n', '--processnum', default=20)
    parser.add_argument('-m', '--memorylimit', default=32)

    args = parser.parse_args()

    run_all(args.inputdir, args.prove, args.features, args.skip, args.timeout, args.processnum, args.memorylimit)
