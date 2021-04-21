# TheSy

TheSy is short for theory synthesizer and is a theory exploration tool.
You can either run TheSy with cargo or compile and run the executable.
For your convenience you may use the available [docker image](https://hub.docker.com/r/eytansingher/thesy) which contains 
the source code and an installed version of TheSy. 
For more information see [Installation](#Installation) section.

## Installation

TheSy uses cargo as the build system. 
To build from the source:

    git clone -b releases/cav2021 https://github.com/eytans/TheSy thesy
    cd thesy
    cargo build --release --features "stats"

The executable will be available in target/release.
To install you need to run `cargo install --path .` command, 
after which TheSy will be available as part of the relevant cargo repos bin folder
(usually ~/.cargo/bin/TheSy).

Optionally you can retrieve a docker image containing an installed version of TheSy 
without building it yourself. 
This is available using `docker pull eytansingher/thesy:latest`.

## Usage

TheSy has a few compilation flags and run modes.
Mainly it can be run in exploration mode (default), or in proof mode when proof goals are available.
Compilation flags are used for different experiment configurations. 
They are passed to `cargo` commands using `--features "<flag 1> <flag2>"`.

* stats - collect statistics during run and export them to json file in same directory as input path
* no_expl_split - Do not use case split during theory exploration but allow prover case split
* no_split - Do not use case split at all