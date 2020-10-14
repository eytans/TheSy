from .import_lemmas import TheoryDocument



def main():
    BENCHMARK_DIRS = ['thesy-results/isaplannerthy_results']
    LEMMA_DIR = 'thesy-results/isaplannerthy_lemmas'
    TARGET_DIRS = [] #'frontend/benchmarks/isaplanner']

    import os

    for td in TARGET_DIRS:
        try: os.makedirs(td)
        except FileExistsError: pass

    for d in BENCHMARK_DIRS:
        for fn in os.listdir(d):
            if fn.endswith('.thy'):
                print('--  %s --' % fn)
                infile = open(os.path.join(d, fn))

                doc = TheoryDocument(infile)

                print(doc.datatypes, doc.ctors, doc.funcs)

                lemfn = os.path.join(LEMMA_DIR, fn.replace('.thy', ' lemmas.txt'))
                if os.path.exists(lemfn):
                    lemfile = open(lemfn)

                    doc = TheoryDocument(lemfile).merge(doc)
                    for t, lem in doc.lemmas:
                        print(f" - {t} {lem}")
                        print(f"   {doc.find_vars(lem[0])} {doc.export_lemma(lem)}")

main()