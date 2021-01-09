# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: test_chapter12.py

"""Tests all Chapter 12 tasks."""

from predicates.syntax_test import *
from predicates.completeness_test import *

def test_task1(debug=False):
    test_is_primitively_closed(debug)
    test_is_universally_closed(debug)
    test_is_existentially_closed(debug)

def test_task2(debug=False):
    test_find_unsatisfied_quantifier_free_sentence(debug)

def test_task3(debug=False):
    test_model_or_inconsistency(debug)

def test_task4(debug=False):
    test_combine_contradictions(debug)

def test_task5(debug=False):
    test_eliminate_universal_instantiation_assumption(debug)

def test_task6(debug=False):
    test_universal_closure_step(debug)

def test_task7(debug=False):
    test_replace_constant(debug)
    test_eliminate_existential_witness_assumption(debug)

def test_task8(debug=False):
    test_existential_closure_step(debug)

test_task1()
test_task2()
test_task3()
test_task4()
test_task5()
test_task6()
test_task7()
test_task8()

# f = Formula.parse("Ex[Ey[Ez[Plus(z,x,y)]]]")
# print("the formula: ", f, "its free variables: ", f.free_variables())
# f=f.predicate
# print("the formula: ", f, "its free variables: ", f.free_variables())
# f=Formula.parse(str(f))
# print("the formula: ", f, "its free variables: ", f.free_variables())
