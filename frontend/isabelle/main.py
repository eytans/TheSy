from .import_lemmas import TheoryDocument



def main():
    BENCHMARK_DIRS = ['thesy-results/isaplannerthy_results']
    TARGET_DIRS = [] #'frontend/benchmarks/isaplanner']

    import os

    for td in TARGET_DIRS:
        try: os.makedirs(td)
        except FileExistsError: pass

    stats = {'theories': 0, 'lemmas': 0}

    for d in BENCHMARK_DIRS:
        for fn in os.listdir(d):
            if fn.endswith('.thy'):
                print('--  %s  --' % fn)
                infile = open(os.path.join(d, fn))

                doc = TheoryDocument(infile)

                print(doc.datatypes, doc.ctors, doc.funcs)

                lemfn = os.path.join(d, fn + '.log')
                if os.path.exists(lemfn):
                    lemfile = open(lemfn)

                    doc = TheoryDocument(lemfile).merge(doc)
                    for t, lem in doc.lemmas:
                        print(f" - {doc.export_lemma(lem)}")
                        #print(f" - {t} {lem}")
                        #print(f"   {doc.find_vars(lem[0])} {doc.export_lemma(lem)}")
                    
                    if doc.lemmas:
                        stats['theories'] += 1
                        stats['lemmas'] += len(doc.lemmas)

    print(f"{stats['lemmas']} lemmas in {stats['theories']} theories")


main()