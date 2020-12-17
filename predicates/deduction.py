# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1
    assumptions = set(proof.assumptions)
    assumptions.remove(Schema(assumption))
    # assumptions.union(Prover.AXIOMS)
    phi = assumption
    prover = Prover(assumptions, print_as_proof_forms)
    index_map = [None] * len(proof.lines)
    for i, line in enumerate(proof.lines):
        new_line_index = None
        if type(line) == Proof.AssumptionLine:
            if line.formula == phi:
                new_line_index = prover.add_tautology(Formula("->", phi, phi))
            else:
                alpha = line.formula
                step1 = prover.add_instantiated_assumption(alpha, line.assumption, line.instantiation_map)
                new_line_index = prover.add_tautological_implication(Formula('->', phi, alpha), {step1})
        elif type(line) == Proof.MPLine:
            new_line_index = prover.add_tautological_implication(Formula('->', phi, line.formula),
                                                                 {index_map[line.antecedent_line_number],
                                                                  index_map[line.conditional_line_number]})
        elif type(line) == Proof.TautologyLine:
            new_line_index = prover.add_tautology(Formula("->", phi, line.formula))
        elif type(line) == Proof.UGLine:
            phi_imp_alpha_index = index_map[line.predicate_line_number]
            alpha: Formula = line.formula.predicate
            x: str = line.formula.variable
            ug_formula = Formula("A", x, Formula("->", phi, alpha))
            step1 = prover.add_ug(ug_formula, phi_imp_alpha_index)
            inst_map = {'Q': phi, 'R': alpha.substitute({x: Term('_')}), 'x': x}

            conclusion = Formula("->", phi, Formula("A", x, alpha))

            step2 = prover.add_instantiated_assumption(Formula('->', ug_formula, conclusion), Prover.US,
                                                       inst_map)
            new_line_index = prover.add_mp(conclusion, step1, step2)
        index_map[i] = new_line_index

    return prover.qed()


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    phi = Schema(assumption)
    assert phi in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
    not_assumption = Formula('~', assumption)
    prover = Prover(set(proof.assumptions) - {phi}, print_as_proof_forms)
    proof_contradiction = remove_assumption(proof, assumption, print_as_proof_forms)
    step1 = prover.add_proof(proof_contradiction.conclusion, proof_contradiction)
    prover.add_tautological_implication(not_assumption, {step1})
    return prover.qed()
