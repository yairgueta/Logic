# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: test_chapter03.py

"""Tests all Chapter 3 tasks."""

from propositions.syntax_test import *
from propositions.semantics_test import *
from propositions.operators_test import *

def test_before_tasks(debug=False):
    assert is_binary('+'), 'Change is_binary() before testing Chapter 3 tasks.'
    test_operators_defined(debug)

def test_task1(debug=False):
    test_repr(debug)
    test_repr_all_operators(debug)
    test_variables(debug)
    test_variables_all_operators(debug)
    test_operators(debug)
    test_operators_all_operators(debug)
    test_parse_prefix(debug)
    test_parse_prefix_all_operators(debug)
    test_is_formula(debug)
    test_is_formula_all_operators(debug)
    test_parse(debug)
    test_parse_all_operators(debug)
         
def test_task2(debug=False):
    test_evaluate(debug)
    test_evaluate_all_operators(debug)
    test_truth_values(debug)
    test_is_tautology(debug)
    test_is_contradiction(debug)
    test_is_satisfiable(debug)
    test_is_tautology_all_operators(debug)
    test_print_truth_table(debug)

def test_task3(debug=False):
    test_substitute_variables(debug)

def test_task4(debug=False):
    test_substitute_operators(debug)

def test_task5(debug=False):
    test_to_not_and_or(debug)

def test_task6a(debug=False):
    test_to_not_and(debug)

def test_task6b(debug=False):
    test_to_nand(debug)

def test_task6c(debug=False):
    test_to_implies_not(debug)

def test_task6d(debug=False):
    test_to_implies_false(debug)


test_before_tasks()
test_task1()
test_task2()
test_task3()
test_task4()
test_task5()
test_task6a()
test_task6b()
test_task6c()
test_task6d()

