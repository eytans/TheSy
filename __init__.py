import pathlib

project_root = pathlib.Path(__file__).parent
experiments_dir = project_root / "experiments"
theories_dir = project_root / "theories"
cargo_path = pathlib.Path.home() / ".cargo/bin/cargo"

executable_release = project_root / "target/release/TheSy"