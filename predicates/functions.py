# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Returns:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    new_relation_meanings = dict(**model.relation_meanings)
    for f_name, function in model.function_meanings.items():
        relation_set = set()
        for key, y in function.items():
            relation_set.add((y, *key))
        new_relation_meanings[
            function_name_to_relation_name(f_name)] = relation_set
    return Model(model.universe, model.constant_meanings, new_relation_meanings)


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2
    relation_meanings = dict(**model.relation_meanings)
    functions_map = dict()
    for f in original_functions:
        r_name = function_name_to_relation_name(f)
        function_map = dict()
        del relation_meanings[r_name]
        _input = []
        for relation in model.relation_meanings[r_name]:
            _input, _output = relation[1:], relation[0]
            if _input in function_map:
                return None
            function_map[_input] = _output
        if len(function_map) != len(model.universe) ** len(_input):
            return None
        functions_map[f] = function_map
    return Model(model.universe, model.constant_meanings, relation_meanings,
                 functions_map)


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert variable[0] != 'z'
    # Task 8.3
    formulas = []
    __compile_helper(term, formulas)
    return formulas


def __compile_helper(term, formulas):
    # Task 8.3 helper
    new_args = []
    for arg in term.arguments:
        if is_function(arg.root):
            new_args.append(__compile_helper(arg, formulas))
        else:
            new_args.append(arg)
    zi = Term(next(fresh_variable_name_generator))
    formulas.append(Formula('=', [zi, Term(term.root, new_args)]))
    return zi


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4
    return __replace_functions_helper(formula)


def __replace_functions_helper(formula : Formula) -> Formula:
    if is_unary(formula.root):
        return Formula(formula.root, __replace_functions_helper(formula.first))
    elif is_binary(formula.root):
        return Formula(formula.root, __replace_functions_helper(formula.first), __replace_functions_helper(formula.second))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, __replace_functions_helper(formula.predicate))
    else:
        return __convert_functions_in_relation(formula)


def __convert_functions_in_relation(formula : Formula) -> Formula:
    """formula must be a relation (or equality)!"""
    new_terms = []
    compiled = []
    for t in formula.arguments:
        if is_function(t.root):
            c = _compile_term(t)
            compiled.extend(c)
            new_terms.append(c[-1].arguments[0])
        else:
            new_terms.append(t)

    current_formula = Formula(formula.root, new_terms)
    while compiled:
        z, f = compiled.pop().arguments
        # print(z, f)
        relation = Formula(function_name_to_relation_name(f.root), [z] + list(f.arguments))
        current_formula = Formula("E", z.root, Formula("&", relation, current_formula))

    return current_formula



def replace_functions_with_relations_in_formulas(formulas:
AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    new_set = set()
    z1, z2 = Term("z1"), Term("z2")
    z1eqz2 = Formula("=", [z1, z2])
    for f in formulas:
        new_set.add(replace_functions_with_relations_in_formula(f))
        for name, num_parameters in f.functions():
            inputs = [Term("x"+str(i)) for i in range(1, num_parameters+1)]
            relation_name = function_name_to_relation_name(name)
            r1, r2 = Formula(relation_name, [z1]+inputs), Formula(relation_name, [z2]+inputs)

            inner1 = Formula("E", z1.root, r1)
            inner2 = Formula("A", z1.root, Formula("A", z2.root, Formula("->", Formula("&", r1, r2), z1eqz2)))

            for i in inputs:
                inner1 = Formula("A", i.root, inner1)
                inner2 = Formula("A", i.root, inner2)
            new_set.add(Formula("&", inner1, inner2))
    return new_set



def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    # Task 8.6
    relations_respects = set()
    x, y, z = Term('x'), Term("y"), Term("z")
    x_s_y, y_s_x, y_s_z, x_s_z = Formula("SAME", [x, y]), Formula("SAME", [y, x]), Formula("SAME", [y, z]), Formula("SAME", [x, z])
    basic_properties = {Formula("A", x.root, Formula("SAME", [x, x])),
                        Formula("A", x.root, Formula("A", y.root, Formula("&",
                                                                          Formula("->", x_s_y, y_s_x),
                                                                          Formula("->", y_s_x, x_s_y)))),
                        Formula("A", x.root,
                                Formula("A", y.root,
                                        Formula("A", z.root,
                                                Formula("->", Formula("&", x_s_y, y_s_z), x_s_z))))}
    for formula in formulas:
        basic_properties.add(__find_and_replace_equalities(formula, relations_respects))

    return basic_properties.union(relations_respects)


def __find_and_replace_equalities(formula: Formula, relations_respects) -> Formula:
    if is_unary(formula.root):
        return Formula(formula.root, __find_and_replace_equalities(formula.first, relations_respects))
    elif is_binary(formula.root):
        return Formula(formula.root, __find_and_replace_equalities(formula.first, relations_respects),
                       __find_and_replace_equalities(formula.second, relations_respects))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, __find_and_replace_equalities(formula.predicate, relations_respects))
    elif is_relation(formula.root):
        xs, ys = [], []
        respective_formula = None

        for i in range(1, len(formula.arguments)+1):
            xs.append(Term("x"+str(i)))
            ys.append(Term("y"+str(i)))
            if i > 1:
                respective_formula = Formula("&", Formula("SAME", [xs[-1], ys[-1]]), respective_formula)
            else:
                respective_formula = Formula("SAME", [xs[0], ys[0]])

        respective_formula = Formula("->", respective_formula, Formula("->",
                                                                       Formula(formula.root, xs),
                                                                       Formula(formula.root, ys)))
        for t in xs+ys:
            respective_formula = Formula("A", t.root, respective_formula)

        if respective_formula is not None:
            relations_respects.add(respective_formula)
        return formula
    else:
        return Formula("SAME", formula.arguments)

def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Returns:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    new_relations = dict(**model.relation_meanings)
    new_relations["SAME"] = {(x, x) for x in model.universe}
    return Model(model.universe, model.constant_meanings, new_relations, model.function_meanings)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
    new_constants = dict(**model.constant_meanings)
    new_relations = dict(**model.relation_meanings)
    same_relation = new_relations.pop("SAME")

    equivalence_classes = []
    uni = set(model.universe)

    while uni:
        x = uni.pop()
        cls = {x}
        for y in list(uni):
            if (x, y) in same_relation:
                cls.update(y)
                uni.remove(y)
        equivalence_classes.append(cls)

    shrink_universe = set()
    equivalence_mapping = dict()
    for cls in equivalence_classes:
        representative = cls.pop()
        equivalence_mapping.update({str(x): representative for x in cls})
        shrink_universe.update(representative)

    equivalence_others = equivalence_mapping.keys()
    for k, v in new_constants.items():
        if v in equivalence_others:
            new_constants[k] = equivalence_mapping[v]

    # new_constants.update(equivalence_mapping)
    # TODO: why not??

    copy_new_relations = dict()
    for name, relation in new_relations.items():
        new_relation = set()
        for args in relation:
            new_relation.add(tuple([equivalence_mapping.get(i, i) for i in args]))
        copy_new_relations[name] = new_relation

    new_functions = dict()
    for name, function in model.function_meanings.items():
        new_function = dict()
        for _input, _output in function.items():
            new_function[tuple([equivalence_mapping.get(i, i) for i in _input])] = equivalence_mapping.get(_output, _output)
        new_functions[name] = new_function

    # print(shrink_universe)
    # print(new_constants)
    return Model(shrink_universe, new_constants, copy_new_relations, new_functions)
