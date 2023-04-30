import pathlib
import shutil

project_root = pathlib.Path(__file__).parent.parent
experiments_dir = project_root / "experiments"
theories_dir = project_root / "theories"
cargo_path = pathlib.Path.home() / ".cargo/bin/cargo"

executable_release = project_root / "target/release/TheSy"
expl_executable_release = project_root / "target/release/expl_experiment"


def copy_tree_th_only(src, dest):
    def th_predicate(src_dir, files):
        p = pathlib.Path(src_dir)
        return [f for f in files if (p / f).is_file() and ((p / f).suffix != '.th' or '.res' in (p / f).suffixes)]
    shutil.copytree(src, dest, ignore=th_predicate)