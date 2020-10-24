# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    p = Formula('p')
    q = Formula('q')
    n_p = Formula('~', p)
    n_q = Formula('~', q)
    p_and_q = Formula('&', p, q)
    p_or_q = Formula('|', p, q)
    nand = Formula('~', p_and_q)
    nor = Formula('~', p_or_q)

    _map = {
        'F':    Formula('&', p, n_p),
        'T':    Formula('|', q, n_q),
        '->':   Formula('|', n_p, q),         # a->b = ~a | b
        '+':    Formula('&', nand, p_or_q),    # a+b = (a-&b)&(a|b)
        '<->':  Formula('|', nor, p_and_q),  # a<->b = (a-|b)|(a&b)
        '-&':   nand,
        '-|':   nor
    }
    return formula.substitute_operators(_map)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    p = Formula('p')
    q = Formula('q')
    n_p = Formula('~', p)
    n_q = Formula('~', q)
    _f = Formula('&', p, n_p)
    p_and_q = Formula('&', p, q)
    p_or_q = Formula('~', Formula('&', n_p, n_q))
    nand = Formula('~', p_and_q)
    nor = Formula('~', p_or_q)
    xor = Formula('&', nand, p_or_q)

    _map = {
        'F':    _f,
        'T':    Formula('~', _f),
        '|':    p_or_q,
        '->':   Formula('~', Formula('&', p, n_q)),   # a->b = ~(a&~b)
        '+':    xor,                                   # a+b = (a-&b)&(a|b)
        '<->':  Formula('~', xor),                   # a<->b = (a-|b)|(a&b)
        '-&':   nand,
        '-|':   nor
    }
    return formula.substitute_operators(_map)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    p = Formula('p')
    q = Formula('q')
    n_p = Formula('-&', p, p)
    n_q = Formula('-&', q, q)
    nand = Formula('-&', p, q)
    _t = Formula('-&', p, n_p)
    p_and_q = Formula('-&', nand, nand)
    p_or_q = Formula('-&', n_p, n_q)
    nor = Formula('~', p_or_q)
    xor = Formula('-&', Formula('-&', nand, p), Formula('-&', nand, q))

    _map = {
        'F':    Formula('-&', _t, _t),
        'T':    _t,
        '~':    n_p,
        '&':    p_and_q,
        '|':    p_or_q,
        '->':   Formula('-&', p, n_q),
        '+':    xor,
        '<->':  Formula('-&', xor, xor),
        '-|':   Formula('-&', p_or_q, p_or_q)
    }
    return formula.substitute_operators(_map)



def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    p = Formula('p')
    q = Formula('q')
    n_p = Formula('~', p)
    n_q = Formula('~', q)
    nand = Formula('->', p, n_q)
    p_or_q = Formula('->', n_p, q)
    _t = Formula('->', p, p)

    imp = Formula('->', p, q)
    imp_r = Formula('->', q, p)
    xor = Formula('->', imp, Formula('~', imp_r))

    _map = {
        'F':    Formula('~', _t),
        'T':    _t,
        '&':    Formula('~', nand),
        '|':    p_or_q,
        '+':    xor,
        '<->':  Formula('~', xor),
        '-&':   nand,
        '-|':   Formula('~', p_or_q)
    }
    return formula.substitute_operators(_map)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    p = Formula('p')
    q = Formula('q')
    _f = Formula('F')
    n_p = Formula('->', p, _f)
    n_q = Formula('->', q, _f)
    nand = Formula('->', p, n_q)
    p_or_q = Formula('->', n_p, q)
    _t = Formula('->', p, p)

    imp = Formula('->', p, q)
    imp_r = Formula('->', q, p)
    xor = Formula('->', imp, Formula('->', imp_r, _f))

    _map = {
        'T':    Formula('->', _f, _f),
        '~':    n_p,
        '&':    Formula('->', nand, _f),
        '|':    p_or_q,
        '+':    xor,
        '<->':  Formula('->', xor, _f),
        '-&':   nand,
        '-|':   Formula('->', p_or_q, _f)
    }
    return formula.substitute_operators(_map)
