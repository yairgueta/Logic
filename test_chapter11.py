# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: test_chapter11.py

"""Tests all Chapter 11 tasks."""

from predicates.deduction_test import *
from predicates.prenex_test import *
from predicates.some_proofs_test import *

def test_task1(debug=False):
    test_remove_assumption(debug)

def test_task2(debug=False):
    test_proof_by_way_of_contradiction(debug)

def test_task3(debug=False):
    test_is_quantifier_free(debug)
    test_is_in_prenex_normal_form(debug)

def test_task4(debug=False):
    test_not_exists_not_implies_all_proof(debug)
    test_exists_not_implies_not_all_proof(debug)
    test_not_all_iff_exists_not_proof(debug)

def test_task5(debug=False):
    test_uniquely_rename_quantified_variables(debug)

def test_task6(debug=False):
    test_pull_out_quantifications_across_negation(debug)

def test_task7(debug=False):
    test_pull_out_quantifications_from_left_across_binary_operator(debug)
    test_pull_out_quantifications_from_right_across_binary_operator(debug)

def test_task8(debug=False):
    test_pull_out_quantifications_across_binary_operator(debug)

def test_task9(debug=False):
    test_to_prenex_normal_form_from_uniquely_named_variables(debug)

def test_task10(debug=False):
    test_to_prenex_normal_form(debug)

test_task1()
test_task2()
test_task3()
test_task4() # Optional
test_task5()
test_task6()
test_task7()
test_task8()
test_task9()
test_task10()
