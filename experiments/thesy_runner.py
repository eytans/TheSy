import enum
import os
import argparse
import shutil
import subprocess
import multiprocessing
import pathlib
from collections import namedtuple

from datetime import datetime
from pathlib import Path
from experiments import executable_release, project_root, cargo_path

RunParams = namedtuple('RunParams', ['fn', 'timeout', 'proof_mode', 'memorylimit', 'prover_split_d', 'prover_split_i', 'base_path', 'out_path'])

project_dir = project_root


def create_build_cmd(additional_features):
    return [str(cargo_path), "build", "--release", "--features", f"stats {' '.join(additional_features)}",
            "--package", "TheSy", "--bin", "TheSy"]


CMD = [str(executable_release)]


def run_thesy(params: RunParams):
    print(f"running {params.fn}")
    try:
        cmd = [s for s in CMD]
        if params.proof_mode:
            cmd.append(f'--mode={str(params.proof_mode).replace("ThesyMode.", "")}')
        cmd.append(f'--limit={int(params.memorylimit) * 1024}')
        cmd.append('--no_invariants')
        cmd.append(f"--prover_split_d={params.prover_split_d}")
        cmd.append(f"--prover_split_i={params.prover_split_i}")
        cmd.append(params.fn)
        print(cmd)
        res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=params.timeout)
        out = res.stdout.decode("utf8")
        error = res.stderr.decode("utf8")
    except subprocess.TimeoutExpired:
        out = ""
        error = "Timeout Exception"
    fixed_fn: Path = params.fn
    if params.base_path:
        extra = 1 if params.fn.endswith("/") else 0
        fixed_fn = Path(str(params.out_path) + params.fn[len(str(params.base_path)) + extra:])
    fixed_fn.parent.mkdir(parents=True, exist_ok=True)
    with fixed_fn.with_suffix(".out").open('w') as f:
        f.write(out)
    with fixed_fn.with_suffix(".err").open('w') as f:
        f.write(error)
    print("Done with " + os.path.basename(params.fn))
    # with open(fn + ".json", 'w') as f:


class ThesyMode(enum.Enum):
    Run = 1
    Prove = 2
    CheckEquiv = 3
    CENoCaseSplit = 4


def run_all(dirs, mode=ThesyMode.Run, features="", skip=None, timeout=60, processnum=15, memorylimit=32,
            multiprocess=True, rerun=True, prover_split_d="1", prover_split_i="4", out_path=None, base_path=None):
    assert out_path is None or base_path is not None
    if skip is None:
        skip = []
    to = timeout * 60
    build_cmd = [c for c in create_build_cmd(features.split(" ")) if c != ""]
    p = subprocess.run(build_cmd, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    if p.returncode != 0:
        print(p.stderr.decode())
        print(p.stdout.decode())
        exit()
    print("Build done")
    inputdirs = dirs
    files = [RunParams(os.path.join(folder, fn), timeout=to, proof_mode=mode, memorylimit=memorylimit,
                       prover_split_d=prover_split_d, prover_split_i=prover_split_i, base_path=base_path,
                       out_path=out_path) for folder in inputdirs for fn in
             os.listdir(folder) if fn.endswith(".th") and (not fn.endswith("res.th")) and fn not in skip]
    if not rerun:
        files = [p for p in files if not pathlib.Path(p.fn).with_suffix('.stats.json').exists()]
    # isa_files = ["./temp/" + f for f in isa_files]
    pn = processnum
    if multiprocess:
        pool = multiprocessing.Pool(pn)
        pool.map(run_thesy, files)
    else:
        for f in files:
            run_thesy(f)


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
    parser.add_argument('-o', '--outputdir', default=None)
    parser.add_argument('--prover_split_d', default="1")
    parser.add_argument('--prover_split_i', default="4")
    args = parser.parse_args()
    rerun = not args.norerun

    outputdir = Path(args.outputdir) if args.outputdir is not None else Path.cwd() / (
            "results_" + datetime.now().strftime("%Y-%m-%d_%H-%M-%S"))
    os.makedirs(outputdir, exist_ok=True)
    # Copy all input dirs to outputdir and collect to inputdirs
    inputdirs = []
    for inputdir in args.inputdir:
        new_inputdir = Path(outputdir / inputdir.name)
        assert inputdir.is_dir()
        shutil.copytree(inputdir, new_inputdir)
        inputdirs.append(new_inputdir)

    run_all(inputdirs, args.mode, args.features, args.skip, int(args.timeout), int(args.processnum), args.memorylimit,
            args.singlethread, rerun)
