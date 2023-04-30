import re


def extract_rewrites(test_case):
    """
    Extracts rewrite rules from a given test case.

    Args:
        test_case (str): Test case string.

    Returns:
        list: List of extracted rewrite rules.
    """
    rewrites = []
    lines = test_case.split("\n")
    for line in lines:
        line = line.strip()
        if line.startswith("rw"):
            rewrites.append(line)
    return rewrites


def extract_prove_statement(test_case):
    """
    Extracts prove statement from a given test case.

    Args:
        test_case (str): Test case string.

    Returns:
        str: Extracted prove statement.
    """
    lines = test_case.split("\n")
    for line in lines:
        line = line.strip()
        if line.startswith("prove"):
            return line
    return None


def extract_sexp_from_prove(prove_statement):
    """
    Extracts sexp from a given prove statement.

    Args:
        prove_statement (str): Prove statement string.

    Returns:
        str: Extracted sexp.
    """
    assert prove_statement.startswith("prove")
    res = []
    rest = " ".join(prove_statement.split(" ")[1:]).strip()
    if rest.startswith("if"):
        rest = rest[2:].strip()  # Remove "if"
        end = extract_between_paran(rest)
        res.append(rest[:end])
        # remove then
        rest = rest[end + 5:].strip()
    # Take the next sexp. Need to match parentheses.
    end = extract_between_paran(rest)
    res.append(rest[:end])
    rest2 = rest[end:].strip()
    if rest2.startswith("="):
        res.append(rest2[1:].strip())
    return res


def extract_between_paran(rest):
    assert rest.startswith("(")
    end = 1
    p_count = 1
    while p_count > 0:
        if rest[end] == "(":
            p_count += 1
        elif rest[end] == ")":
            p_count -= 1
        end += 1
    return end


def clean_annotation(sexp: str):
    """
    Cleans annotation from a given sexp.

    Args:
        sexp (str): Sexp string.

    Returns:
        str: Sexp string without annotation.
    """
    pattern = r'\(\?(\w+)\s*:\s*\w+\s*\)'
    res = re.sub(pattern, r'\1', sexp)
    assert '?' not in res
    return res


def find_similar_test_cases(test_cases):
    """
    Identifies similar test cases based on the intersection of their extracted rewrite rules.

    Args:
        test_cases (list): List of test case strings.

    Returns:
        list: List of tuples, where the first element is the test case itself, and the second element is a list of
        prove statements from other similar test cases.
    """
    test_rewrites = {}
    prove_statements = {}
    similar_test_cases = []

    # Extract rewrite rules and prove statements for each test case
    for i, test_case in enumerate(test_cases):
        test_rewrites[i] = set(" ".join(rw.split()[2:]) for rw in extract_rewrites(test_case))
        prove_statements[i] = extract_prove_statement(test_case)

    # Find similar test cases
    for i, test_case in enumerate(test_cases):
        similar_prove_statements = []
        for j, other_test_case in enumerate(test_cases):
            if i != j:
                intersection = test_rewrites[i].intersection(test_rewrites[j])
                if len(intersection) >= 2:
                    similar_prove_statements.append(prove_statements[j])
        similar_test_cases.append((test_case, similar_prove_statements))

    return similar_test_cases


def clean_and_extract(prove_statements):
    """
    Cleans and extracts sexp from a given proof statements.

    Args:
        prove_statements: List[str]. All prove statements from similar test cases.

    Returns:
        list: List of extracted sexp.
    """
    return [clean_annotation(x) for p in prove_statements for x in extract_sexp_from_prove(p)]
    


from pathlib import Path

# Directory containing test cases
testcases_dir = Path(__file__).resolve().parent / "testcases"


def main(indir: Path):
    # Find similar test cases for each subdirectory
    for subdir_path in indir.iterdir():
        if subdir_path.is_dir():
            test_cases = []
            for file_path in subdir_path.iterdir():
                if file_path.name.endswith(".at"):
                    continue
                with open(file_path, "r") as f:
                    test_case = f.read()
                    test_cases.append((file_path.name, test_case))  # Include filename with test case

            similar_test_cases = find_similar_test_cases([test_case for _, test_case in test_cases])
            files = [f for (f, _) in test_cases]
            clean_and_extracted = [clean_and_extract(prove_statements) for (_, prove_statements) in similar_test_cases]
            # Write prove statements to file
            for (file, cleaned) in zip(files, clean_and_extracted):
                output_file = (subdir_path / file).with_suffix(".at")
                with open(output_file, "w") as f:
                    for prove_statement in cleaned:
                        f.write(f"{prove_statement}\n")  # Write prove statement without filename

if __name__ == "__main__":
    main(testcases_dir)