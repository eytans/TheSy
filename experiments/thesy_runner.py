import enum
import os
import argparse
import shutil
import subprocess
import multiprocessing
import pathlib
from collections import namedtuple

from datetime import datetime
from experiments import executable_release, project_root, cargo_path

cgroups_disabled = os.name == 'nt' or os.name == "darwin" or os.name == "posix"
if not cgroups_disabled:
    from cgroups import Cgroup

RunParams = namedtuple('RunParams', ['fn', 'timeout', 'proof_mode'])

project_dir = project_root

BUILD_CMD = [str(cargo_path), "build", "--release", "--features", "stats", "--package", "TheSy", "--bin", "TheSy"]
CMD = [str(executable_release)]


# First we create the cgroup 'charlie' and we set it's cpu and memory limits
if not cgroups_disabled:
    cg = Cgroup('thesy_cgroup')


# Then we a create a function to add a process in the cgroup
def in_my_cgroup():
    if not cgroups_disabled:
        pid = os.getpid()
        cg = Cgroup('thesy_cgroup')
        cg.add(pid)


def run_thesy(params: RunParams):
    in_my_cgroup()
    print(f"running {params.fn}")
    try:
        cmd = [s for s in CMD]
        if params.proof_mode:
            cmd.append('--prove')
        cmd.append(params.fn)
        print(cmd)
        res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=params.timeout)
        out = res.stdout.decode("utf8")
        error = res.stderr.decode("utf8")
    except subprocess.TimeoutExpired:
        out = ""
        error = "Timeout Exception"
    with open(params.fn + ".out", 'w') as f:
        f.write(out)
    with open(params.fn + ".err", 'w') as f:
        f.write(error)
    print("Done with " + os.path.basename(params.fn))
    # with open(fn + ".json", 'w') as f:


def run_all(dirs, prove=False, features="", skip=None, timeout=60, processnum=15, memorylimit=32, multiprocess=True, rerun=True):
    if skip is None:
        skip = []
    to = timeout * 60
    build_cmd = [c for c in BUILD_CMD]
    build_cmd[4] = (build_cmd[4] + " " + features).strip()
    p = subprocess.run(build_cmd, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    if p.returncode != 0:
        print(p.stderr.decode())
        print(p.stdout.decode())
        exit()
    print("Build done")
    inputdirs = dirs
    files = [RunParams(os.path.join(folder, fn), timeout=to, proof_mode=prove) for folder in inputdirs for fn in os.listdir(folder) if fn.endswith(".th") and (not fn.endswith("res.th")) and fn not in skip]
    if not rerun:
        files = [p for p in files if not pathlib.Path(p.fn).with_suffix('.stats.json').exists()]
    # isa_files = ["./temp/" + f for f in isa_files]
    if not cgroups_disabled:
        cg.set_memory_limit(memorylimit, 'gigabytes')
    pn = processnum
    if multiprocess:
        pool = multiprocessing.Pool(pn)
        pool.map(run_thesy, files)
    else:
        for f in files:
            run_thesy(f)


class ThesyMode(enum.Enum):
    Run = 1
    Prove = 2
    CheckEquiv = 3
    CENoCaseSplit = 4


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("inputdir", nargs='+')
    # Add argument for thesy mode
    parser.add_argument("--mode", type=ThesyMode, choices=list(ThesyMode), default=ThesyMode.Run)
    parser.add_argument('-s', '--singlethread', action='store_false', default=True)
    parser.add_argument('-f', '--features', default="")
    parser.add_argument('--skip', nargs='*', default=None)
    parser.add_argument('-t', '--timeout', default=60)
    parser.add_argument('-n', '--processnum', default=15)
    parser.add_argument('-m', '--memorylimit', default=32)
    parser.add_argument('--norerun', action='store_true', default=False)

    args = parser.parse_args()
    rerun = not args.norerun

    run_all(args.inputdir, args.prove, args.features, args.skip, args.timeout, args.processnum, args.memorylimit, args.singlethread, rerun)
