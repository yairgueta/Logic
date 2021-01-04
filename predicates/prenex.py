# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

ALL_AXIOMS = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    if is_equality(formula.root) or is_relation(formula.root):
        return True
    elif is_quantifier(formula.root):
        return False
    elif is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    elif is_unary(formula.root):
        return is_quantifier_free(formula.first)



def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)
    else:
        return is_quantifier_free(formula)

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def _uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.5
    prover = Prover(ALL_AXIOMS)
    if is_unary(formula.root):
        f, proof = _uniquely_rename_quantified_variables(formula.first)
        conclusion = Formula('~', f)
        step = prover.add_proof(proof.conclusion, proof)
        prover.add_tautological_implication(equivalence_of(formula, conclusion), {step})
        return conclusion, prover.qed()
    elif is_binary(formula.root):
        f1, proof1 = _uniquely_rename_quantified_variables(formula.first)
        f2, proof2 = _uniquely_rename_quantified_variables(formula.second)
        step1 = prover.add_proof(proof1.conclusion, proof1)
        step2 = prover.add_proof(proof2.conclusion, proof2)
        conclusion = Formula(formula.root, f1, f2)
        prover.add_tautological_implication(equivalence_of(formula, conclusion), {step1, step2})
        return conclusion, prover.qed()
    elif is_quantifier(formula.root):
        x = formula.variable
        Q = formula.root
        phi = formula.predicate
        z_phi, proof = _uniquely_rename_quantified_variables(phi)  # 1
        s1 = prover.add_proof(proof.conclusion, proof)
        z: str = next(fresh_variable_name_generator)
        formula_to_return = Formula(Q, z, z_phi.substitute({x: Term(z)}))
        conclusion = equivalence_of(formula, formula_to_return)
        instantiation_map = {'x': formula.variable, 'y': z,
                             'R': phi.substitute({x: Term('_')}),
                             'Q': formula_to_return.predicate.substitute(
                                 {z: Term('_')})}
        if formula.root == 'A':
            s = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]
        else:
            s = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
        s2 = prover.add_instantiated_assumption(Formula('->', proof.conclusion, conclusion), s,
                                                instantiation_map)
        prover.add_mp(conclusion, s1, s2)
        return formula_to_return, prover.qed()

    else:
        prover.add_tautological_implication(equivalence_of(formula, formula), set())
        return formula, prover.qed()


def __swap_quantifier(Q):
    if Q == 'A':
        return 'E'
    return 'A'


QUANTIFY_EQUIVALENT_AXIOMS_MAP = frozendict({'A': ADDITIONAL_QUANTIFICATION_AXIOMS[-2], 'E': ADDITIONAL_QUANTIFICATION_AXIOMS[-1]})
QUANTIFIER_TO_AXIOM_MAPS = tuple(frozendict({'A': ADDITIONAL_QUANTIFICATION_AXIOMS[i], 'E': ADDITIONAL_QUANTIFICATION_AXIOMS[i+1]})
                            for i in range(0, len(ADDITIONAL_QUANTIFICATION_AXIOMS) - 2, 2))


def __pull_out_quantifiers_across_all(formula, is_left, swap_function, axioms, parent_rec_function):
    if is_left:
        psi = None
        inner = formula.first
        if is_binary(formula.root):
            psi = formula.second
    else:
        inner, psi = formula.second, formula.first

    Q = inner.root
    prover = Prover(ALL_AXIOMS)
    if not is_quantifier(Q):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    if is_left:
        n_pred = Formula(formula.root, inner.predicate, psi)
    else:
        n_pred = Formula(formula.root, psi, inner.predicate)

    x = inner.variable

    axiom = axioms[Q]
    Qt = swap_function(Q)
    equiv_axiom = QUANTIFY_EQUIVALENT_AXIOMS_MAP[Qt]

    axiom_map = {'x': inner.variable, 'R': inner.predicate.substitute({inner.variable: Term('_')})}
    if psi is not None:
        axiom_map['Q'] = psi
    step_axiom = prover.add_instantiated_assumption(axiom.instantiate(axiom_map), axiom, axiom_map)

    pred_prime, pred_prime_proof = parent_rec_function(n_pred)
    step1 = prover.add_proof(pred_prime_proof.conclusion, pred_prime_proof)

    equiv_axiom_map = {'x': x, 'y': x, 'R': n_pred.substitute({x: Term('_')}),
                       'Q': pred_prime.substitute({x: Term('_')})}
    step_equiv_axiom = prover.add_instantiated_assumption(equiv_axiom.instantiate(equiv_axiom_map), equiv_axiom,
                                                          equiv_axiom_map)

    conclusion = Formula(Qt, x, pred_prime)
    prover.add_tautological_implication(equivalence_of(formula, conclusion), {step_axiom, step1, step_equiv_axiom})

    return conclusion, prover.qed()

def _pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    return __pull_out_quantifiers_across_all(formula, True, __swap_quantifier, QUANTIFIER_TO_AXIOM_MAPS[0],
                                             _pull_out_quantifications_across_negation)


def _pull_out_quantifications_from_left_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    operator = formula.root
    assert is_binary(operator)
    # Task 11.7.1
    operator_map = {'&': (lambda _q: _q, QUANTIFIER_TO_AXIOM_MAPS[1]),
                    '|': (lambda _q: _q, QUANTIFIER_TO_AXIOM_MAPS[3]),
                    '->': (__swap_quantifier, QUANTIFIER_TO_AXIOM_MAPS[5])}

    swap_function, axioms = operator_map[operator]

    return __pull_out_quantifiers_across_all(formula, True, swap_function,
                                             axioms, _pull_out_quantifications_from_left_across_binary_operator)




def _pull_out_quantifications_from_right_across_binary_operator(formula:
                                                                Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    operator = formula.root
    assert is_binary(operator)
    # Task 11.7.2
    operator_map = {'&': (lambda _q: _q, QUANTIFIER_TO_AXIOM_MAPS[2]),
                    '|': (lambda _q: _q, QUANTIFIER_TO_AXIOM_MAPS[4]),
                    '->': (lambda _q: _q, QUANTIFIER_TO_AXIOM_MAPS[6])}

    swap_function, axioms = operator_map[operator]

    return __pull_out_quantifiers_across_all(formula, False, swap_function,
                                             axioms, _pull_out_quantifications_from_right_across_binary_operator)


def _pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]
    ``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``
    [``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\
            `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\
         `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    left_pull, left_pull_proof = _pull_out_quantifications_from_left_across_binary_operator(formula)

    left_quantifiers = list()
    _pred = left_pull
    while is_quantifier(_pred.root):
        left_quantifiers.append((_pred.root, _pred.variable))
        _pred = _pred.predicate

    right_pull, right_pull_proof = _pull_out_quantifications_from_right_across_binary_operator(_pred)

    prover = Prover(ALL_AXIOMS)
    left_step = prover.add_proof(equivalence_of(formula, left_pull), left_pull_proof)
    right_step = prover.add_proof(equivalence_of(_pred, right_pull), right_pull_proof)

    quantifying_lines = []
    while len(left_quantifiers):
        Q, x = left_quantifiers.pop()
        axiom = QUANTIFY_EQUIVALENT_AXIOMS_MAP[Q]
        map = {'x': x, 'y': x, 'R': right_pull.substitute({x: Term('_')}),
                       'Q': _pred.substitute({x: Term('_')})}
        right_pull = Formula(Q, x, right_pull)
        _pred = Formula(Q, x, _pred)
        quantifying_lines.append(prover.add_instantiated_assumption(axiom.instantiate(map), axiom, map))

    prover.add_tautological_implication(equivalence_of(formula, right_pull), {*quantifying_lines, left_step, right_step})
    return right_pull, prover.qed()


def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    prover = Prover(ALL_AXIOMS)
    if is_relation(formula.root) or is_equality(formula.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    elif is_unary(formula.root):
        inner, inner_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        n_formula = Formula(formula.root, inner)
        fp, fp_proof = _pull_out_quantifications_across_negation(n_formula)

        step1 = prover.add_proof(equivalence_of(formula.first, inner), inner_proof)
        step2 = prover.add_proof(equivalence_of(n_formula, fp), fp_proof)
        prover.add_tautological_implication(equivalence_of(formula, fp), {step1, step2})
        return fp, prover.qed()

    elif is_binary(formula.root):
        inner1, inner1_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        inner2, inner2_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.second)

        n_formula = Formula(formula.root, inner1, inner2)
        fp, fp_proof = _pull_out_quantifications_across_binary_operator(n_formula)

        step1 = prover.add_proof(equivalence_of(formula.first, inner1), inner1_proof)
        step2 = prover.add_proof(equivalence_of(formula.second, inner2), inner2_proof)
        step3 = prover.add_proof(equivalence_of(n_formula, fp), fp_proof)
        prover.add_tautological_implication(equivalence_of(formula, fp), {step1, step2, step3})
        return fp, prover.qed()
    else:
        Q, x, _pred = formula.root, formula.variable, formula.predicate
        n_pred, n_pred_proof = _to_prenex_normal_form_from_uniquely_named_variables(_pred)
        axiom = QUANTIFY_EQUIVALENT_AXIOMS_MAP[Q]
        map = {'x': x, 'y': x, 'R': _pred.substitute({x: Term('_')}),
                       'Q': n_pred.substitute({x: Term('_')})}
        step1 = prover.add_instantiated_assumption(axiom.instantiate(map), axiom, map)
        step2 = prover.add_proof(equivalence_of(_pred, n_pred), n_pred_proof)

        conclusion = Formula(Q, x, n_pred)
        prover.add_tautological_implication(equivalence_of(formula, conclusion), {step1, step2})
        return conclusion, prover.qed()



def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.10
    uni_formula, uni_proof = _uniquely_rename_quantified_variables(formula)
    pnf_formula, pnf_proof = _to_prenex_normal_form_from_uniquely_named_variables(uni_formula)

    prover = Prover(ALL_AXIOMS)
    step1 = prover.add_proof(equivalence_of(formula, uni_formula), uni_proof)
    step2 = prover.add_proof(equivalence_of(uni_formula, pnf_formula), pnf_proof)
    prover.add_tautological_implication(equivalence_of(formula, pnf_formula), {step1, step2})
    return pnf_formula, prover.qed()
