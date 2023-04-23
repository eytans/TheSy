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
                # TODO: ignore rw name
                intersection = test_rewrites[i].intersection(test_rewrites[j])
                if len(intersection) >= 2:
                    similar_prove_statements.append(prove_statements[j])
        similar_test_cases.append((test_case, similar_prove_statements))

    return similar_test_cases


from pathlib import Path

# Directory containing test cases
testcases_dir = Path(__file__).resolve().parent / "testcases"


def main():
    # Find similar test cases for each subdirectory
    for subdir_path in testcases_dir.iterdir():
        if subdir_path.is_dir():
            test_cases = []
            for file_path in subdir_path.iterdir():
                with open(file_path, "r") as f:
                    test_case = f.read()
                    test_cases.append((file_path.name, test_case))  # Include filename with test case

            similar_test_cases = find_similar_test_cases([test_case for _, test_case in test_cases])

            # Write prove statements to file
            for (file, _), prove_statements in zip(test_cases, similar_test_cases):
                output_file = (subdir_path / file).with_suffix(".at")
                with open(output_file, "w") as f:
                    for prove_statement in prove_statements:
                        f.write(f"{prove_statement}\n")  # Write prove statement without filename
