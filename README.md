# TheSy

TheSy is short for theory synthesizer and is a theory exploration tool.
You can either run TheSy with cargo or compile and run the executable.
For your convenience you may use the available [docker image](https://hub.docker.com/r/eytansingher/thesy) which contains 
the source code and an installed version of TheSy. 
For more information see [Installation](#Installation) section.
It is recommended to use a machine with at least 32GB memory; 
still, most cases will pass with less.

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
If you have an image in tar format, use `docker load -i <tar file>`, 
and then run the loaded image
using `docker run --memory="32g" -it --entrypoint bash <image name>`.

## Usage

TheSy has a few compilation flags and run modes.
Mainly it can be run in exploration mode (default), or in proof mode when proof goals are available.
Compilation flags are used for different experiment configurations. 
They are passed to `cargo` commands using `--features "<flag 1> <flag2>"`.

* stats - collect statistics during run and export them to json file in same directory as input path
* no_expl_split - Do not use case split during theory exploration but allow prover case split
* no_split - Do not use case split at all

--  Note that running cargo with different features recompiles TheSy! 
Remember to add `--release` flag for compilation optimizations, 
and to use the new compiled version (i.e. `cargo run`)    

In addition TheSy can receive flags to control the run mode. 
Mainly the relevant modes are:

* Exploration - default mode used, will run theory exploration based 
  on provided definitions and report found lemmas.
* Proof - when given a proof instruction in the definition file TheSy will 
  attempt to prove the goal after each lemma found until success or saturation.
  Usage: `-p` or `--prove`, when using cargo needs to be used after providing -- 
  `cargo run --release --features "stats" -- -p <path>`
* Equivalence Check - attempt to prove equality of terms given as goals in the definitions file.
  This is done without inductive exploration, only with rewriting and case splitting.
  Usage: `-c` or `check-equiv`, when using cargo needs to be used after providing --
  `cargo run --release --features "stats" -- -c <path>`
  
Note: TheSy might differ between different runs. 
For example a single run (experiments/cvc4_benchmarks/tests/clam/goal6.smt2.th) might finish
in 14 seconds and might finish in ~550 seconds.
This instability, while not common, can greatly affect memory usage (longer runs equal more memory usage).
 
## TheSy Format
Input files, with the ".th" extension, use a specific format
to allow easy case definition and experimentation.

### Format details 
The format supports: 

#### Datatype definitions
`(datatype <name> <params (currently unused)> <constructors>)`
Where constructor is `<name> <param typess> <return type>`.
Example: `(datatype Lst () ((cons Nat Lst Lst) (nil Lst)))`

#### Function definitions
`(declare-fun <name> <params types> <return type>)`
Example: `(declare-fun append (Lst Lst) Lst)`

#### Rewrite rules
There are a few types of rewrite rule definitions to handle different situations.
A rewrite is built of two parts: 
a pattern to match and a result pattern to add to the graph.

`(=> app_ind1 (append (cons ?x ?y) ?z) (cons ?x (append ?y ?z)))` - a rewrite rule named app_base which
rewrites `(append (cons <hole 1> <hole 2>) <hole 3>)` to `(cons <hole 1> (append <hole 2> <hole 3>)))` 
where `hole i` can match any expression. 
After rewriting the resulting expressions are merged. 
Meaning they are now considered equal, but both exist)

`(<=> app_ind (append (cons ?x ?y) ?z) (cons ?x (append ?y ?z)))` -
Same as before but now is bidirectional.

`(=|> <name> <pattern> <result>)` - 
Acts as previous rewrite rule definitions but does not merge the expressions.

#### Goals
`(prove (forall (<var definitions>) (= <term1> <term2>)))`
Example: `(prove (forall ((n Nat)(xs list)) (= (++ (take n xs) (drop n xs)) xs)))`

#### Preconditions
Both directional rewrites and goals support preconditions. 
Preconditioned expressions are given as - 
`(=> (condition) (= (term1) (term2)))`.
A rewrite will only be applied if the condition is matched.
A goal will be attempted assuming the condition is equal true.

### Translation from SMTLIB
We have a translation script from the smt2.6 format used in 
some [CVC4 benchmarks](http://lara.epfl.ch/~reynolds/VMCAI2015-ind/).
The translation script may not work for other smt2 files.

Usage: `python3 ./frontend/smtlib/main <dir to translate> <output dir>`.
Requires python3 and pysmt to be installed.

## Experimentation
Every experiment is contained in a folder under experiments.
Each experiment has a single python runner, 
but there is no single interface for all of them.
Requires: python3 pandas

Note: when using docker, please ensure enough ram is available by passing 
the --memory="32g" parameter to `docker run`.

#### Lemma quality
We compare lemma quality over the isaplanner benchmarks.
To run TheSy on said benchmarks, from TheSy's root directory use 
```
python3 -m experiments.isaplanner_proving.run_thesy_expl -t <timeout>
```
The default timeout is 60 minutes per test (i.e. -t 60), 
to get a runtime of ~4 hours use a 5 minute timeout (i.e. -t 5) 

The results will be in 
"experiments/isaplanner_proving/isaplanner_no_cs/stats.csv" 
and in "experiments/isaplanner_proving/isaplanner_with_cs/stats.csv".
The directory "experiments/isaplanner_proving/via_hipster"
contains the results from running Hipster on the same benchmarks.
These results are used to create the comparison
The lemma quality comparison is in "head_to_head.csv" and in "head_to_head-no-cs.csv"
where no-cs means no case split was used.
To create head_to_head comparison you can use the script
"frontend/head_to_head.py", but be aware that Hipster may change some function names and it needs addressing.

#### Comparison to CVC4 results
From TheSy's root directory (this might be long): 
```
python3 -m experiments.cvc4_benchmarks.runner -t 1
```
This experiment runs TheSy three times, in the CAV2021 paper we only used tests.
The results of the run appear in "experiments/cvc4_benchmarks/stats.csv" where only results under 'no expl proofs' are interesting.

