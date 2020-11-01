# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *


def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable `x` that is assigned the
    value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    return [Formula.parse(f) if model[f] else Formula.parse('~' + f) for f in sorted(model.keys())]


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    value = evaluate(formula, model)

    if is_variable(formula.root):
        assumptions = formulas_capturing_model(model)
        conclusion = formula if value else Formula('~', formula)
        return Proof(InferenceRule(assumptions, conclusion), AXIOMATIC_SYSTEM, [Proof.Line(conclusion)])
    elif is_unary(formula.root):
        phi = formula.first
        if value:
            return prove_in_model(phi, model)
        else:
            phi_proof = prove_in_model(phi, model)
            nnphi = Formula('~', formula)
            return Proof(InferenceRule(phi_proof.statement.assumptions, nnphi), AXIOMATIC_SYSTEM,
                         list(phi_proof.lines) + [Proof.Line(Formula('->', phi, nnphi), NN, []),
                                                  Proof.Line(nnphi, MP,
                                                             [len(phi_proof.lines) - 1, len(phi_proof.lines)])])
    elif is_binary(formula.root):
        phi1, phi2 = formula.first, formula.second
        p1p2 = Formula('->', phi1, phi2)
        if value:
            if not evaluate(phi1, model):
                nphi1_proof = prove_in_model(phi1, model)
                return Proof(InferenceRule(nphi1_proof.statement.assumptions, formula),
                             AXIOMATIC_SYSTEM, list(nphi1_proof.lines) +
                             [Proof.Line(Formula('->', Formula('~', phi1), p1p2), I2, []),
                              Proof.Line(formula, MP, [len(nphi1_proof.lines) - 1, len(nphi1_proof.lines)])])
            else:
                phi2_proof = prove_in_model(phi2, model)
                return Proof(InferenceRule(phi2_proof.statement.assumptions, formula),
                             AXIOMATIC_SYSTEM, list(phi2_proof.lines) +
                             [Proof.Line(Formula('->', phi2, p1p2), I1, []),
                              Proof.Line(formula, MP, [len(phi2_proof.lines) - 1, len(phi2_proof.lines)])])
        else:
            phi1_proof, nphi2_proof = prove_in_model(phi1, model), prove_in_model(phi2, model)
            statement = InferenceRule(phi1_proof.statement.assumptions, Formula('~', p1p2))
            n1, n2 = len(phi1_proof.lines), len(nphi2_proof.lines)
            lines = _concat_proofs(phi1_proof, nphi2_proof) + \
                    [Proof.Line(NI.specialize({'p': phi1, 'q': phi2}).conclusion, NI, []),
                     Proof.Line(Formula.parse("(~q->~(p->q))").substitute_variables({'p': phi1, 'q': phi2}),
                                MP, [n1 - 1, n1 + n2]),
                     Proof.Line(Formula('~', p1p2), MP, [n1 + n2 - 1, n1 + n2 + 1])]

            return Proof(statement, AXIOMATIC_SYSTEM, lines)


def _concat_proofs(p1: Proof, p2: Proof) -> List[Proof.Line]:
    """from two proofs, cancats the lines of the first with the second and returns the list of the two."""
    n1 = len(p1.lines)
    new_lines = list(p1.lines)
    return new_lines + [l if l.is_assumption() else Proof.Line(l.formula, l.rule, [i + n1 for i in l.assumptions]) for l
                        in p2.lines]


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption` ``'`` instead of
            `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    new_statement = InferenceRule(proof_from_affirmation.statement.assumptions[:-1],
                                  proof_from_affirmation.statement.conclusion)
    new_rules = proof_from_affirmation.rules.union({MP, I0, I1, D, R})
    p1, p2 = remove_assumption(proof_from_affirmation), remove_assumption(proof_from_negation)
    n1, n2 = len(p1.lines), len(p2.lines)
    phi, psi = proof_from_affirmation.statement.assumptions[-1], proof_from_affirmation.statement.conclusion
    nphi_psi = p2.statement.conclusion
    new_lines = _concat_proofs(p1, p2)
    new_lines.append(Proof.Line(R.specialize({'p': psi, 'q': phi}).conclusion, R, []))
    new_lines.append(Proof.Line(Formula('->', nphi_psi, psi), MP, [n1 - 1, n1 + n2]))
    new_lines.append(Proof.Line(psi, MP, [n1 + n2 - 1, n1 + n2 + 1]))

    return Proof(new_statement, new_rules, new_lines)
    # Task 6.2


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    _vars = sorted(tautology.variables())
    keys = sorted(model.keys())
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert _vars[:len(model)] == keys
    if keys == _vars:
        return prove_in_model(tautology, model)
    else:
        n = len(keys)
        p1, p2 = prove_tautology(tautology, {**model, _vars[n]: True}), prove_tautology(tautology,
                                                                                        {**model, _vars[n]: False})
        return reduce_assumption(p1, p2)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    for model in all_models(formula.variables()):
        if not evaluate(formula, model):
            return model
    return prove_tautology(formula, {})


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    f = rule.conclusion
    for asm in reversed(rule.assumptions):
        f = Formula('->', asm, f)
    return f


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    assumptionless_proof = prove_tautology(encode_as_formula(rule))
    new_lines = list(assumptionless_proof.lines)

    current_formula = assumptionless_proof.statement.conclusion
    for a in rule.assumptions:
        n = len(new_lines)
        new_lines.append(Proof.Line(a))
        current_formula = current_formula.second
        new_lines.append(Proof.Line(current_formula, MP, [n, n - 1]))
    return Proof(rule, AXIOMATIC_SYSTEM, new_lines)


def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})
    _vars = set()
    for f in formulas:
        _vars = _vars.union(f.variables())
    for model in all_models(_vars):
        if all([evaluate(f, model) for f in formulas]):
            return model
    return prove_sound_inference(InferenceRule(formulas, Formula.parse('~(p->p)')))


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    value = evaluate(formula, model)

    if is_variable(formula.root):
        assumptions = formulas_capturing_model(model)
        conclusion = formula if value else Formula('~', formula)
        return Proof(InferenceRule(assumptions, conclusion), AXIOMATIC_SYSTEM_FULL, [Proof.Line(conclusion)])
    elif is_constant(formula.root):
        assumptions = formulas_capturing_model(model)
        conclusion, axiom = (formula, T) if value else (Formula('~', formula), NF)
        return Proof(InferenceRule(assumptions, conclusion), AXIOMATIC_SYSTEM_FULL, [Proof.Line(conclusion, axiom, [])])
    elif is_unary(formula.root):
        phi = formula.first
        if value:
            return prove_in_model_full(phi, model)
        else:
            phi_proof = prove_in_model_full(phi, model)
            nnphi = Formula('~', formula)
            return Proof(InferenceRule(phi_proof.statement.assumptions, nnphi), AXIOMATIC_SYSTEM_FULL,
                         list(phi_proof.lines) + [Proof.Line(Formula('->', phi, nnphi), NN, []),
                                                  Proof.Line(nnphi, MP,
                                                             [len(phi_proof.lines) - 1, len(phi_proof.lines)])])
    elif is_binary(formula.root):
        phi1, phi2 = formula.first, formula.second
        if formula.root == '->':
            p1p2 = Formula('->', phi1, phi2)
            if value:
                if not evaluate(phi1, model):
                    nphi1_proof = prove_in_model_full(phi1, model)
                    return Proof(InferenceRule(nphi1_proof.statement.assumptions, formula),
                                 AXIOMATIC_SYSTEM_FULL, list(nphi1_proof.lines) +
                                 [Proof.Line(Formula('->', Formula('~', phi1), p1p2), I2, []),
                                  Proof.Line(formula, MP, [len(nphi1_proof.lines) - 1, len(nphi1_proof.lines)])])
                else:
                    phi2_proof = prove_in_model_full(phi2, model)
                    return Proof(InferenceRule(phi2_proof.statement.assumptions, formula),
                                 AXIOMATIC_SYSTEM_FULL, list(phi2_proof.lines) +
                                 [Proof.Line(Formula('->', phi2, p1p2), I1, []),
                                  Proof.Line(formula, MP, [len(phi2_proof.lines) - 1, len(phi2_proof.lines)])])
            else:
                phi1_proof, nphi2_proof = prove_in_model_full(phi1, model), prove_in_model_full(phi2, model)
                statement = InferenceRule(phi1_proof.statement.assumptions, Formula('~', p1p2))
                n1, n2 = len(phi1_proof.lines), len(nphi2_proof.lines)
                lines = _concat_proofs(phi1_proof, nphi2_proof) + \
                        [Proof.Line(NI.specialize({'p': phi1, 'q': phi2}).conclusion, NI, []),
                         Proof.Line(Formula.parse("(~q->~(p->q))").substitute_variables({'p': phi1, 'q': phi2}),
                                    MP, [n1 - 1, n1 + n2]),
                         Proof.Line(Formula('~', p1p2), MP, [n1 + n2 - 1, n1 + n2 + 1])]
                return Proof(statement, AXIOMATIC_SYSTEM_FULL, lines)
        elif formula.root == '|':
            if value:
                if evaluate(phi1, model):
                    phi1_proof = prove_in_model_full(phi1, model)
                    return Proof(InferenceRule(phi1_proof.statement.assumptions, formula),
                                 AXIOMATIC_SYSTEM_FULL, list(phi1_proof.lines) +
                                 [Proof.Line(Formula('->', phi1, formula), O2, []),
                                  Proof.Line(formula, MP, [len(phi1_proof.lines) - 1, len(phi1_proof.lines)])])
                else:
                    phi2_proof = prove_in_model_full(phi2, model)
                    return Proof(InferenceRule(phi2_proof.statement.assumptions, formula),
                                 AXIOMATIC_SYSTEM_FULL, list(phi2_proof.lines) +
                                 [Proof.Line(Formula('->', phi2, formula), O1, []),
                                  Proof.Line(formula, MP, [len(phi2_proof.lines) - 1, len(phi2_proof.lines)])])
            else:
                nphi1_proof = prove_in_model_full(phi1, model)
                nphi2_proof = prove_in_model_full(phi2, model)
                np1p2 = Formula('~', formula)
                np1, np2 = Formula('~', phi1), Formula('~', phi2)
                n1, n2 = len(nphi1_proof.lines), len(nphi2_proof.lines)
                lines = _concat_proofs(nphi1_proof, nphi2_proof) + \
                        [Proof.Line(Formula('->', np1, Formula('->', np2, np1p2)), NO, []),
                         Proof.Line(Formula('->', np2, np1p2), MP, [n1-1, n1+n2]),
                         Proof.Line(np1p2, MP, [n1+n2-1, n1+n2+1])]
                return Proof(InferenceRule(nphi1_proof.statement.assumptions, np1p2),
                             AXIOMATIC_SYSTEM_FULL, lines)
        elif formula.root == '&':
            if value:
                phi1_proof = prove_in_model_full(phi1, model)
                phi2_proof = prove_in_model_full(phi2, model)
                n1, n2 = len(phi1_proof.lines), len(phi2_proof.lines)
                lines = _concat_proofs(phi1_proof, phi2_proof) + \
                        [Proof.Line(Formula('->', phi1, Formula('->', phi2, formula)), A, []),
                         Proof.Line(Formula('->', phi2, formula), MP, [n1 - 1, n1 + n2]),
                         Proof.Line(formula, MP, [n1 + n2 - 1, n1 + n2 + 1])]
                return Proof(InferenceRule(phi1_proof.statement.assumptions, formula),
                             AXIOMATIC_SYSTEM_FULL, lines)
            else:
                if not evaluate(phi1, model):
                    nphi1_proof = prove_in_model_full(phi1, model)
                    np1p2 = Formula('~', formula)
                    np1 = Formula('~', phi1)
                    return Proof(InferenceRule(nphi1_proof.statement.assumptions, np1p2),
                                 AXIOMATIC_SYSTEM_FULL, list(nphi1_proof.lines) +
                                 [Proof.Line(Formula('->', np1, np1p2), NA2, []),
                                  Proof.Line(np1p2, MP, [len(nphi1_proof.lines) - 1, len(nphi1_proof.lines)])])
                else:
                    nphi2_proof = prove_in_model_full(phi2, model)
                    np1p2 = Formula('~', formula)
                    np2 = Formula('~', phi2)
                    return Proof(InferenceRule(nphi2_proof.statement.assumptions, np1p2),
                                 AXIOMATIC_SYSTEM_FULL, list(nphi2_proof.lines) +
                                 [Proof.Line(Formula('->', np2, np1p2), NA1, []),
                                  Proof.Line(np1p2, MP, [len(nphi2_proof.lines) - 1, len(nphi2_proof.lines)])])

