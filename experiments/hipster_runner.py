# For some weird reason we need to be inside the hol library directory when running isabelle for this to work
import os
import argparse
import shutil
import subprocess
import multiprocessing
from datetime import datetime

from cgroups import Cgroup

HOL_LIB_DIR = r"/home/eytan.s/Apps/Isabelle2019/src/HOL/Library/"
CMD = [r"/home/eytan.s/Apps/Isabelle2019/bin/isabelle", "process", "-o", "quick_and_dirty=true", "-T"]
BENCHMARK_DIR = r"/home/eytan.s/Apps/benchmarks/benchmarks/isaplannerthy/"
TARGET_DIR = r"/home/eytan.s/Apps/benchmarks/benchmarks/isaplannerthy_results/"

if not os.path.exists(TARGET_DIR):
    os.makedirs(TARGET_DIR)


# First we create the cgroup 'charlie' and we set it's cpu and memory limits
cg = Cgroup('hipster_cgroup')


# Then we a create a function to add a process in the cgroup
def in_my_cgroup():
    pid = os.getpid()
    cg = Cgroup('hipster_cgroup')
    cg.add(pid)


def run_isabelle(fn):
    try:
        in_my_cgroup()
        print(f"running {fn}")
        os.chdir(HOL_LIB_DIR)
        with open(fn) as f:
            lines = f.readlines()
            assert lines[0].startswith("theory")
            for i in range(len(lines)):
                if "hipster" in lines[i] and "(*" in lines[i].split("hipster")[0]:
                    lines[i] = lines[i].replace("(*", "")
                    for j in range(i, len(lines)):
                        if "*)" in lines[j]:
                            lines[j] = lines[j].replace("*)", "")
                            break
                    break

            lines[0] = f"theory {os.path.basename(fn)[:-4]}\n"
            lines.insert(2, '        "$HIPSTER_HOME/IsaHipster"\n')
            stripped = [l.strip() for l in lines]
        if all([not "hipster" in l for l in lines]):
            func_decs = [l.split()[1] for l in stripped if l.startswith("fun ")]
            index = stripped.index("end")
            lines.insert(index, "hipster " + " ".join(func_decs) + "\n")
        for i in range(len(lines)):
            if lines[i].startswith("datatype"):
                splitted = lines[i].split()
                for s in splitted[1:]:
                    if not s.startswith("'") and not s.startswith("("):
                        print(f"replacing {s}")
                        # TODO: replace only if not surrounded by [a-zA-Z]
                        lines = lines[:4] + [l.replace(s, s[0].upper() + s[1:] + "Special") for l in lines[4:]]
                        break
                # TODO: replace constructors
        for i in range(4, len(lines)):
            lines[i] = lines[i].replace("2", 'twoSpec')
        with open(fn, 'w') as f:
            f.writelines(lines)

        start_time = datetime.now()
        try:
            res = subprocess.run(CMD + [fn[:-4]], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60*60*3)
            out = res.stdout.decode("utf8")
            error = res.stderr.decode("utf8")
        except subprocess.TimeoutExpired:
            out = ""
            error = "Timeout Exception"
        end_time = datetime.now()
        out_fn = os.path.join(TARGET_DIR, os.path.basename(fn))
        shutil.copyfile(fn, out_fn)
        with open(out_fn + ".log", 'w') as f:
            f.write(out)
        with open(out_fn + ".err", 'w') as f:
            f.write(error)
        with open(out_fn + ".time", 'w') as f:
            f.write(str(end_time-start_time))
        print("Done with " + os.path.basename(fn))
    except:
        pass
    # with open(fn + ".json", 'w') as f:


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputdir", default=BENCHMARK_DIR)
    args = parser.parse_args()
    if os.path.isdir(HOL_LIB_DIR + "temp"):
        shutil.rmtree(HOL_LIB_DIR + "temp")
    shutil.copytree(args.inputdir, HOL_LIB_DIR + "temp")
    file_dir = HOL_LIB_DIR + "temp/"
    isa_files = [fn for fn in os.listdir(args.inputdir) if fn.endswith(".thy")]
    for f in isa_files:
        if f[0].islower():
            shutil.move(os.path.join(file_dir, f), os.path.join(file_dir, f[0].upper() + f[1:]))
    isa_files = ["./temp/" + f[0].upper() + f[1:] for f in isa_files]
    # isa_files = ["./temp/" + f for f in isa_files]
    cg.set_memory_limit(32, 'gigabytes')
    pn = 15
    pool = multiprocessing.Pool(pn)
    pool.map(run_isabelle, isa_files)
