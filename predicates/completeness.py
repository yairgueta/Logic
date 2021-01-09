# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""
import itertools
from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *

def _not(f: Formula) -> Formula:
    return Formula('~', f)

def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants

def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)

def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1
    constants = {Term(s) for s in get_constants(sentences)}
    relations = set()
    primitives = set()
    for s in sentences:
        relations.update(s.relations())
        if is_unary(s.root):
            s = s.first
        if is_relation(s.root):
            primitives.add((s.root, s.arguments))

    for r in relations:
        for arity in itertools.product(constants, repeat=r[1]):
            if (r[0], arity) not in primitives:
                return False
    return True



def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    predicates = set()
    constants = {Term(s) for s in get_constants(sentences)}
    for sentence in sentences:
        if is_quantifier(sentence.root):
            if sentence.root == 'A':
                predicates.add((sentence.variable, sentence.predicate))

    for pred in predicates:
        for c in constants:
            if pred[1].substitute({pred[0]: c}) not in sentences:
                return False
    return True

def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3
    predicates = set()
    constants = {Term(s) for s in get_constants(sentences)}
    for sentence in sentences:
        if is_quantifier(sentence.root):
            if sentence.root == 'E':
                predicates.add((sentence.variable, sentence.predicate))

    for pred in predicates:
        for c in constants:
            if pred[1].substitute({pred[0]: c}) in sentences:
                break
        else:
            return False
    return True

def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    if is_quantifier(unsatisfied.root):
        for c in model.universe:
            substituted = unsatisfied.predicate.substitute({unsatisfied.variable: Term(c)})
            if substituted in sentences and not model.evaluate_formula(substituted):
                return find_unsatisfied_quantifier_free_sentence(sentences, model, substituted)
    else:
        return unsatisfied

def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1
    if is_unary(quantifier_free.root):
        return get_primitives(quantifier_free.first)
    if is_binary(quantifier_free.root):
        return get_primitives(quantifier_free.first).union(get_primitives(quantifier_free.second))
    if is_relation(quantifier_free.root):
        return {quantifier_free}


def _is_primitive_or_its_negation(formula: Formula) -> bool:
    if is_unary(formula.root):
        formula = formula.first
    if is_relation(formula.root):
        return True
    return False


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """    
    assert is_closed(sentences)
    # Task 12.3.2
    primitives = {s for s in sentences if _is_primitive_or_its_negation(s)}
    universe = get_constants(sentences)
    relation_meanings = {}
    for primitive in primitives:
        if not is_unary(primitive.root):
            relation_meanings.setdefault(primitive.root, set()).add(tuple(str(t) for t in primitive.arguments))
    model = Model(universe, {c: c for c in universe}, relation_meanings)

    for s in sentences:
        if not model.evaluate_formula(s):
            unsat = find_unsatisfied_quantifier_free_sentence(sentences, model, s)
            unsat_primitives = {f if f in primitives else _not(f) for f in get_primitives(unsat)}

            prover = Prover(Prover.AXIOMS.union(unsat_primitives, {unsat}))
            lines = {prover.add_assumption(unsat)}
            lines.update({prover.add_assumption(f) for f in unsat_primitives})
            prover.add_tautological_implication(Formula('&', unsat, _not(unsat)), lines)
            return prover.qed()
    return model


def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    affirmed_formula = affirmed_assumption.formula
    negated_formula = negated_assumption.formula
    assert negated_formula == \
           Formula('~', affirmed_formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4
    contra1 = proof_by_way_of_contradiction(proof_from_affirmation, affirmed_formula)
    contra2 = proof_by_way_of_contradiction(proof_from_negation, negated_formula)

    prover = Prover(common_assumptions)
    affir_step = prover.add_proof(_not(affirmed_formula), contra1)
    neg_step = prover.add_proof(_not(negated_formula), contra2)
    prover.add_tautological_implication(Formula('&', affirmed_formula, negated_formula), {affir_step, neg_step})
    return prover.qed()


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5
    contra_proof = proof_by_way_of_contradiction(proof, instantiation)
    prover = Prover(contra_proof.assumptions)
    step1 = prover.add_proof(_not(instantiation), contra_proof)
    step2 = prover.add_assumption(universal)
    step3 = prover.add_universal_instantiation(instantiation, step2, constant)
    prover.add_tautological_implication(Formula('&', instantiation, _not(instantiation)), {step1, step3})

    return prover.qed()



def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6
    universe = {Term(c) for c in get_constants(sentences)}
    new_sentences = {x for x in sentences}
    for s in sentences:
        if s.root == 'A':
            for c in universe:
                new_sentences.add(s.predicate.substitute({s.variable: c}))
    return new_sentences


def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in given the proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1
    lines = []
    map = {constant: Term(variable)}
    for l in proof.lines:
        f = l.formula.substitute(map)
        if isinstance(l, Proof.TautologyLine):
            line = Proof.TautologyLine(f)
        if isinstance(l, Proof.AssumptionLine):
            ins_map = {}
            for x,y in l.instantiation_map.items():
                if isinstance(y, str):
                    ins_map[x] = y if y != constant else variable
                else:
                    ins_map[x] = y.substitute(map)
            line = Proof.AssumptionLine(f, l.assumption, ins_map)
        if isinstance(l, Proof.MPLine):
            line = Proof.MPLine(f, l.antecedent_line_number, l.conditional_line_number)
        if isinstance(l, Proof.UGLine):
            line = Proof.UGLine(f, l.predicate_line_number)
        lines.append(line)

    assumptions = {Schema(s.formula.substitute(map), s.templates) for s in proof.assumptions}
    return Proof(assumptions, lines[-1].formula, lines)


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2
    var = 'zz'
    contra_proof = proof_by_way_of_contradiction(proof, witness)
    contra_zz_proof = replace_constant(contra_proof, constant, var)

    contra = Formula('&', witness, _not(witness))
    n_phizz = contra_zz_proof.conclusion

    prover = Prover(contra_zz_proof.assumptions)
    step1 = prover.add_proof(n_phizz, contra_zz_proof)
    step3 = prover.add_assumption(existential)
    step4 = prover.add_ug(Formula('A', var, n_phizz), step1)

    n_phix = n_phizz.substitute({var: Term(existential.variable)})
    step5 = prover.add_universal_instantiation(n_phix, step4, existential.variable)
    step2 = prover.add_tautological_implication(Formula('->', n_phix.first, contra), {step5})
    step4 = prover.add_existential_derivation(contra, step3, step2)
    return prover.qed()



def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by callingמר
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
    universe = {Term(c) for c in get_constants(sentences)}
    new_sentences = {x for x in sentences}
    for s in sentences:
        if s.root == 'E':
            for c in universe:
                if s.predicate.substitute({s.variable: c}) in sentences:
                    break
            else:
                _c = next(fresh_constant_name_generator)
                new_sentences.add(s.predicate.substitute({s.variable: Term(_c)}))
    return new_sentences
