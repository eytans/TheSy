# For some weird reason we need to be inside the hol library directory when running isabelle for this to work
import os
import argparse
import shutil
import subprocess
import multiprocessing
from datetime import datetime

from cgroups import Cgroup

BUILD_CMD = [r"/home/eytan.s/.cargo/bin/cargo", "build", "--release", "--features", "stats", "--package", "TheSy", "--bin", "TheSy"]
CMD = [r"/home/eytan.s/CLionProjects/TheSy/target/release/TheSy"]

# First we create the cgroup 'charlie' and we set it's cpu and memory limits
cg = Cgroup('thesy_cgroup')


# Then we a create a function to add a process in the cgroup
def in_my_cgroup():
    pid = os.getpid()
    cg = Cgroup('thesy_cgroup')
    cg.add(pid)


def run_thesy(fn):
    in_my_cgroup()
    print(f"running {fn}")
    try:
        res = subprocess.run(CMD + [fn], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60*60*3)
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


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("inputdir")
    args = parser.parse_args()
    p = subprocess.run(BUILD_CMD, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    if p.returncode != 0:
        print(p.stderr.decode())
        print(p.stdout.decode())
        exit()
    print("Build done")
    files = [os.path.join(args.inputdir, fn) for fn in os.listdir(args.inputdir) if fn.endswith(".th") and not fn.endswith("res.th")]
    # isa_files = ["./temp/" + f for f in isa_files]
    cg.set_memory_limit(32, 'gigabytes')
    pn = 32
    pool = multiprocessing.Pool(pn)
    pool.map(run_thesy, files)
