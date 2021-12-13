import os
import traceback
from sys import stdout

from pysmt.environment import reset_env
from argparse import ArgumentParser
from pathlib import Path
from glob import glob

from .translators import ThesyFromSmt, NewThesyFromSmt
from .case_splits import ExtractCaseSplits


def main():
    parser = ArgumentParser(description='Extract thesy from SMT-LIB files')
    parser.add_argument('smtlib_in', nargs='*', help='SMT-LIB file or directory to extract thesy from (default: stdin)')
    parser.add_argument('--output', '-o', help='Output directory according to input (default: stdout)')
    parser.add_argument('--thesy_version', '-v', help='Thesy version to use (default: 2)', choices=[1, 2], default=2)
    args = parser.parse_args()

    files = []
    for inp in args.smtlib_in:
        if Path(inp).is_dir():
            for f in glob(inp + '**/*.smt2'):
                files.append((Path(inp), Path(f)))
        else:
            files.append((Path(inp).absolute().parent.relative_to(os.getcwd()), Path(inp)))

    for d, fn in files:
        print('--  %s  --' % fn)
        with fn.open('r') as infile:
            reset_env()
            try:
                if args.thesy_version == 1:
                    doc = ThesyFromSmt(infile)
                elif args.thesy_version == 2:
                    doc = NewThesyFromSmt(infile)
                else:
                    raise NotImplementedError("Only support to thesy formats")
            except:
                print(f"bad {fn}")
                print(traceback.format_exc())
                continue

        out = stdout
        if args.output:
            out = open(Path(args.output) / fn.relative_to(d), 'w')

        try:
            for el in doc:
                print(el)
                print(el, file=out)

            # for srule in ExtractCaseSplits(doc).guess_rules():
            #     print(srule)
            #     print(srule, file=outf)
        finally:
            if args.output:
                out.close()

        print(';', set(doc.iter_used_symbols()))
        print(';', set(doc.iter_used_types()))


if __name__ == '__main__':
    main()

