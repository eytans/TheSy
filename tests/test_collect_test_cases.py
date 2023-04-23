from unittest import TestCase

import experiments
from experiments import similar_cases


class Test(TestCase):
    # Sample 1
    sample1 = """
    datatype Nat () := (succ : (x_0 : Nat) -> (res : Nat)) (zero : (res : Nat))
    fun plus (x_0 : Nat) (x_1 : Nat) -> Nat
    fun mult (x_0 : Nat) (x_1 : Nat) -> Nat
    fun tri (x_0 : Nat) -> Nat
    fun cubes (x_0 : Nat) -> Nat
    rw rule0 (plus zero ?n) => ?n
    rw rule1 (plus (succ ?n) ?m) => (succ (plus ?n ?m))
    rw rule2 (succ (plus ?n ?m)) => (plus (succ ?n) ?m)
    rw rule3 (mult zero ?n) => zero
    rw rule4 (mult (succ ?n) ?m) => (plus (mult ?n ?m) ?m)
    rw rule5 (plus (mult ?n ?m) ?m) => (mult (succ ?n) ?m)
    prove x
    """

    # Sample 2
    sample2 = """
    datatype Nat () := (succ : (x_0 : Nat) -> (res : Nat)) (zero : (res : Nat))
    fun plus (x_0 : Nat) (x_1 : Nat) -> Nat
    fun mult (x_0 : Nat) (x_1 : Nat) -> Nat
    fun tri (x_0 : Nat) -> Nat
    fun cubes (x_0 : Nat) -> Nat
    rw rule0x (plus zero ?n) => ?n
    rw rule1x (plus (succ ?n) ?m) => (succ (plus ?n ?m))
    rw rule2x (succ (plus ?n ?m)) => (plus (succ ?n) ?m)
    rw rule6x (tri zero) => zero
    rw rule7x zero => (tri zero)
    rw rule8x (tri (succ ?n)) => (plus (tri ?n) (succ ?n))
    rw rule9x (plus (tri ?n) (succ ?n)) => (tri (succ ?n))
    prove y
    """

    # Sample 3
    sample3 = """
    datatype Nat () := (succ : (x_0 : Nat) -> (res : Nat)) (zero : (res : Nat))
    fun plus (x_0 : Nat) (x_1 : Nat) -> Nat
    fun mult (x_0 : Nat) (x_1 : Nat) -> Nat
    fun tri (x_0 : Nat) -> Nat
    fun cubes (x_0 : Nat) -> Nat
    rw rule10 (cubes zero) => zero
    rw rule11 zero => (cubes zero)
    rw rule12 (cubes (succ ?n)) => (plus (cubes ?n) (mult (succ ?n) (mult (succ ?n) (succ ?n))))
    rw rule13 (plus (cubes ?n) (mult (succ ?n) (mult (succ ?n) (succ ?n)))) => (cubes (succ ?n))
    prove z
    """

    def test_find_similar_test_cases(self):
        similars = similar_cases.find_similar_test_cases([self.sample1, self.sample2, self.sample3])
        self.assertTrue(len(similars) == 3)
        self.assertTrue(len(similars[2][1]) == 0)
        self.assertTrue(len(similars[0][1]) == 1)
        self.assertTrue(similars[0][1][0] == similar_cases.extract_prove_statement(self.sample2))
