# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
import itertools
from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple
from functools import reduce

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    if is_constant(formula.root):
        return formula.root == "T"
    elif is_variable(formula.root):
        return model[formula.root]
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    else:  # Dealing with binary
        a = evaluate(formula.first, model)
        b = evaluate(formula.second, model)
        if formula.root == '&':
            return a and b
        elif formula.root == '|':
            return a or b
        elif formula.root == '->':
            return (not a) or b
        elif formula.root == '+':
            return (not b) if a else b
        elif formula.root == '<->':
            return b if a else (not b)
        elif formula.root == '-&':
            return not (a and b)
        elif formula.root == '-|':
            return not (a or b)



def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    iterator = itertools.product({False, True}, repeat=len(variables))
    for i in iterator:
        yield dict(zip(variables, i))


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    for model in models:
        yield evaluate(formula, model)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    f_vars = sorted(formula.variables())
    headers = [*f_vars, str(formula)]
    format_h = "|" + "|".join("{:^" + str(len(i) + 2) + "}" for i in headers) + "|"
    format_s = "|" + "|".join("{:<" + str(len(i) + 2) + "}" for i in headers) + "|"
    print(format_h.format(*headers))
    print(format_s.format(*[""] * len(headers)).replace(" ", "-"))
    for model in all_models(list(f_vars)):
        print(format_s.format(*(" T" if i else " F" for i in (*model.values(), evaluate(formula, model)))))
        # print(format_s.format(*(" T" if model[var] else " F" for var in f_vars),
        #                       " T" if evaluate(formula, model) else " F"))


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    return reduce(lambda x, y: x and y, truth_values(formula, all_models(formula.variables())))


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    return not reduce(lambda x, y: x or y, truth_values(formula, all_models(formula.variables())))


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    for val in truth_values(formula, all_models(formula.variables())):
        if val:
            return True
    return False


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    vars_m = list(model.keys())
    assert is_model(model)
    assert len(vars_m) > 0

    if len(vars_m) == 1:
        f = Formula(vars_m[0])
        return f if model[vars_m[0]] else Formula('~', f)
    else:
        model1, model2 = dict(), dict()
        for i in range(len(vars_m)):
            if i < len(vars_m) // 2:
                model1[vars_m[i]] = model[vars_m[i]]
            else:
                model2[vars_m[i]] = model[vars_m[i]]
        return Formula("&", _synthesize_for_model(model1), _synthesize_for_model(model2))


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    var_0 = Formula(variables[0])
    f = Formula("&", var_0, Formula("~", var_0))  # Start from (v & ~v)
    for val, model in zip(values, all_models(variables)):
        if val:
            f = Formula("|", _synthesize_for_model(model), f)
    return f


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    vars_m = list(model.keys())
    assert is_model(model)
    assert len(vars_m) > 0

    if len(vars_m) == 1:
        f = Formula(vars_m[0])
        return Formula('~', f) if model[vars_m[0]] else f
    else:
        model1, model2 = dict(), dict()
        for i in range(len(vars_m)):
            if i < len(vars_m) // 2:
                model1[vars_m[i]] = model[vars_m[i]]
            else:
                model2[vars_m[i]] = model[vars_m[i]]
        return Formula("|", _synthesize_for_all_except_model(model1), _synthesize_for_all_except_model(model2))


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    var_0 = Formula(variables[0])
    f = Formula("|", var_0, Formula("~", var_0))  # Start from (v | ~v)
    for val, model in zip(values, all_models(variables)):
        if not val:
            f = Formula("&", _synthesize_for_all_except_model(model), f)
    return f


# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    for f in rule.assumptions:
        if not evaluate(f, model):
            return True
    return evaluate(rule.conclusion, model)


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    for model in all_models(list(rule.variables())):
        if not evaluate_inference(rule, model):
            return False
    return True

