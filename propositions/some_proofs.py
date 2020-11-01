# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/some_proofs.py

"""Some proofs in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE2_RULE`, and
    `AE1_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE2_RULE`, and `AE1_RULE`.
    """
    lemma = InferenceRule([Formula.parse('(p&q)')], Formula.parse('(q&p)'))
    rules = {A_RULE, AE1_RULE, AE2_RULE}
    lines = [Proof.Line(Formula.parse('(p&q)')),
             Proof.Line(Formula.parse('p'), AE2_RULE, [0]),
             Proof.Line(Formula.parse('q'), AE1_RULE, [0]),
             Proof.Line(Formula.parse('(q&p)'), A_RULE, [2,1])
            ]
    return Proof(lemma, rules, lines)


def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    rules = {MP, I1, D}
    lines = [Proof.Line(Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))'), D, []),
             Proof.Line(Formula.parse('(p->((p->p)->p))'), I1, []),
             Proof.Line(Formula.parse('((p->(p->p))->(p->p))'), MP, [1, 0]),
             Proof.Line(Formula.parse('(p->(p->p))'), I1, []),
             Proof.Line(Formula.parse('(p->p)'), MP, [3, 2])]
    return Proof(I0, rules, lines)

#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    p,q,r = Formula.parse('p'), Formula.parse('q'), Formula.parse('r')
    lines = [Proof.Line(p),
             Proof.Line(Formula('->', p, q)),
             Proof.Line(q, MP, [0, 1]),
             Proof.Line(Formula('->', q, r)),
             Proof.Line(r, MP, [2, 3])]
    return remove_assumption(Proof(InferenceRule(list(HS.assumptions)+[p], r), {MP, I0, I1, D}, lines))
    # Task 5.5

def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a
    rules = {I0, I1, D, N, MP}
    lines = [Proof.Line(Formula.parse('~p')),
             Proof.Line(Formula.parse('(~p->(~q->~p))'), I1, []),
             Proof.Line(Formula.parse('(~q->~p)'), MP, [0, 1]),
             Proof.Line(Formula.parse('((~q->~p)->(p->q))'), N, []),
             Proof.Line(Formula.parse('(p->q)'), MP, [2,3])]
    return remove_assumption(Proof(InferenceRule([Formula.parse('~p')], Formula.parse('(p->q)')), rules, lines))

#: Double-negation elimination
_NNE = InferenceRule([], Formula.parse('(~~p->p)'))

def _prove_NNE() -> Proof:
    """Proves `_NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_NNE` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b
    rules = {I0, I1, D, N, MP}
    lines = [Proof.Line(Formula.parse('~~p')),  # 0
             Proof.Line(Formula.parse('(~~p->(~~~~p->~~p))'), I1, []),  # 1
             Proof.Line(Formula.parse('(~~~~p->~~p)'), MP, [0, 1]),  # 2
             Proof.Line(Formula.parse('((~~~~p->~~p)->(~p->~~~p))'), N, []),  # 3
             Proof.Line(Formula.parse('(~p->~~~p)'), MP, [2, 3]),  # 4
             Proof.Line(Formula.parse('((~p->~~~p)->(~~p->p))'), N, []),  # 5
             Proof.Line(Formula.parse('(~~p->p)'), MP, [4, 5]),  # 6
             Proof.Line(Formula.parse('p'), MP, [0, 6])]
    return remove_assumption(Proof(InferenceRule([Formula.parse('~~p')], Formula.parse('p')), rules, lines))

def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c
    rules = {I0, I1, D, N, MP, _NNE}
    lines = [Proof.Line(Formula.parse('(~~~p->~p)'), _NNE, []),  # 0
             Proof.Line(Formula.parse('((~~~p->~p)->(p->~~p))'), N, []),  # 1
             Proof.Line(Formula.parse('(p->~~p)'), MP, [0, 1])]  # 2
    return inline_proof(Proof(NN, rules, lines), _prove_NNE())

#: Contraposition
_CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def _prove_CP() -> Proof:
    """Proves `_CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CP` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d
    rules = {I0, I1, D, N, MP, _NNE, I2}
    assumption = InferenceRule([Formula.parse('(p->q)'), Formula.parse('~q'), Formula.parse('~~p')], Formula.parse('~(p->p)'))
    lines = [Proof.Line(Formula.parse('~~p')),  # 0
             Proof.Line(Formula.parse('(~~p->p)'), _NNE, []),  # 1
             Proof.Line(Formula.parse('p'), MP, [0, 1]),  # 2
             Proof.Line(Formula.parse('(p->q)')),  # 3
             Proof.Line(Formula.parse('q'), MP, [2, 3]),  # 4
             Proof.Line(Formula.parse('~q')),  # 5
             Proof.Line(Formula.parse('(~q->(q->~(p->p)))'), I2, []),  # 6
             Proof.Line(Formula.parse('(q->~(p->p))'), MP, [5, 6]),  # 7
             Proof.Line(Formula.parse('~(p->p)'), MP, [4, 7])]
    proof = Proof(assumption, rules, lines)
    proof = prove_by_way_of_contradiction(proof)  # proved by contradiction at first.
    proof = remove_assumption(proof)  # remove ~q assumption
    proof = remove_assumption(proof)  # remove p->q assumption
    proof = inline_proof(proof, _prove_NNE())
    proof = inline_proof(proof, prove_I2())

    return proof

def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    rules = {I0, I1, D, N, MP, _NNE, I2}
    assumption = InferenceRule([Formula.parse('p'), Formula.parse('~q'), Formula.parse('~~(p->q)')],
                               Formula.parse('~(p->p)'))
    lines = [Proof.Line(Formula.parse('~~(p->q)')),  # 0
             Proof.Line(Formula.parse('(~~(p->q)->(p->q))'), _NNE, []),  # 1
             Proof.Line(Formula.parse('(p->q)'), MP, [0, 1]),  # 2
             Proof.Line(Formula.parse('p')),  # 3
             Proof.Line(Formula.parse('q'), MP, [3, 2]),  # 4
             Proof.Line(Formula.parse('~q')),  # 5
             Proof.Line(Formula.parse('(~q->(q->~(p->p)))'), I2, []),  # 6
             Proof.Line(Formula.parse('(q->~(p->p))'), MP, [5, 6]),  # 7
             Proof.Line(Formula.parse('~(p->p)'), MP, [4, 7])]
    proof = Proof(assumption, rules, lines)
    proof = prove_by_way_of_contradiction(proof)  # proved by contradiction at first.
    proof = remove_assumption(proof)  # remove ~q assumption
    proof = remove_assumption(proof)  # remove p->q assumption
    proof = inline_proof(proof, _prove_NNE())
    proof = inline_proof(proof, prove_I2())

    return proof

#: Consequentia mirabilis
_CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def _prove_CM() -> Proof:
    """Proves `_CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CM` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    rules = {I0, I1, D, N, MP, I2}
    assumption = InferenceRule([Formula.parse('(~p->p)'), Formula.parse('~p')], Formula.parse('~(p->p)'))
    lines = [Proof.Line(Formula.parse('(~p->p)')),  # 0
             Proof.Line(Formula.parse('~p')),  # 1
             Proof.Line(Formula.parse('p'), MP, [1, 0]),  # 2
             Proof.Line(Formula.parse('(~p->(p->~(p->p)))'), I2, []),  # 3
             Proof.Line(Formula.parse('(p->~(p->p))'), MP, [1, 3]),  # 4
             Proof.Line(Formula.parse('~(p->p)'), MP, [2, 4])]
    proof = Proof(assumption, rules, lines)
    proof = prove_by_way_of_contradiction(proof)  # proved by contradiction at first.
    proof = inline_proof(proof, prove_I2())
    return proof

def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    rules = {I0, I1, D, N, MP, _CM, HS, _CP}
    assumption = InferenceRule([Formula.parse('(q->p)'), Formula.parse('(~q->p)')], Formula.parse('p'))
    lines = [Proof.Line(Formula.parse('((q->p)->(~p->~q))'), _CP, []),  # 0
             Proof.Line(Formula.parse('(q->p)')),  # 1
             Proof.Line(Formula.parse('(~p->~q)'), MP, [1, 0]),  # 2
             Proof.Line(Formula.parse('(~q->p)')),  # 3
             Proof.Line(Formula.parse('(~p->p)'), HS, [2, 3]),  # 4
             Proof.Line(Formula.parse('p'), _CM, [4])]
    proof = Proof(assumption, rules, lines)
    proof = inline_proof(proof, _prove_CM())
    proof = inline_proof(proof, prove_hypothetical_syllogism())
    proof = inline_proof(proof, _prove_CP())
    proof = remove_assumption(proof)
    proof = remove_assumption(proof)
    return proof

def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    rules = HILBERT_AXIOMATIC_SYSTEM_ALTERNATIVE.union({HS, I0})
    assumption = InferenceRule([Formula.parse('(~q->~p)')], Formula.parse('(p->q)'))
    lines = [Proof.Line(Formula.parse('(~q->~p)')),  # 0
             Proof.Line(N_ALTERNATIVE.conclusion, N_ALTERNATIVE, []),  # 1
             Proof.Line(Formula.parse('((~q->p)->q)'), MP, [0, 1]),  # 2
             Proof.Line(Formula.parse('(p->(~q->p))'), I1, []),  # 3
             Proof.Line(Formula.parse('(p->q)'), HS, [3, 2])]
    proof = Proof(assumption, rules, lines)
    proof = inline_proof(proof, prove_hypothetical_syllogism())
    proof = inline_proof(proof, prove_I2())
    proof = remove_assumption(proof)
    return proof

def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    rules = {MP, I0, I1, D, N, AE1, _CP}
    assumption = NA1
    lines = [Proof.Line(Formula.parse('((p&q)->q)'), AE1, []),  # 0
             Proof.Line(Formula.parse('(((p&q)->q)->(~q->~(p&q)))'), _CP, []),  # 1
             Proof.Line(Formula.parse('(~q->~(p&q))'), MP, [0, 1])]
    proof = Proof(assumption, rules, lines)
    proof = inline_proof(proof, _prove_CP())
    return proof

def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    rules = {MP, I0, I1, D, N, AE2, _CP}
    assumption = NA2
    lines = [Proof.Line(Formula.parse('((p&q)->p)'), AE2, []),  # 0
             Proof.Line(Formula.parse('(((p&q)->p)->(~p->~(p&q)))'), _CP, []),  # 1
             Proof.Line(Formula.parse('(~p->~(p&q))'), MP, [0, 1])]
    proof = Proof(assumption, rules, lines)
    proof = inline_proof(proof, _prove_CP())
    return proof

def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    rules = {MP, I0, I1, D, N, OE, I2, _NNE}
    assumption = InferenceRule([Formula.parse('~p'), Formula.parse('~q'), Formula.parse('~~(p|q)')], Formula.parse('~(p->p)'))
    lines = [Proof.Line(Formula.parse('(p->p)'), I0, []),  # 0
             Proof.Line(Formula.parse('(~q->(q->p))'), I2, []),  # 1
             Proof.Line(Formula.parse('~q')),  # 2
             Proof.Line(Formula.parse('(q->p)'), MP, [2, 1]),  # 3
             Proof.Line(Formula.parse('~~(p|q)')),  # 4
             Proof.Line(Formula.parse('(~~(p|q)->(p|q))'), _NNE, []),  # 5
             Proof.Line(Formula.parse('(p|q)'), MP, [4, 5]),  # 6
             Proof.Line(Formula.parse('((p->p)->((q->p)->((p|q)->p)))'), OE, []),  # 7
             Proof.Line(Formula.parse('((q->p)->((p|q)->p))'), MP, [0, 7]),  # 8
             Proof.Line(Formula.parse('((p|q)->p)'), MP, [3, 8]),  # 9
             Proof.Line(Formula.parse('p'), MP, [6, 9]),  # 10
             Proof.Line(Formula.parse('(~p->(p->~(p->p)))'), I2, []),  # 11
             Proof.Line(Formula.parse('~p')),  # 12
             Proof.Line(Formula.parse('(p->~(p->p))'), MP, [12, 11]),  # 13
             Proof.Line(Formula.parse('~(p->p)'), MP, [10, 13])]  # 14
    proof = Proof(assumption, rules, lines)
    proof = prove_by_way_of_contradiction(proof)
    proof = remove_assumption(proof)
    proof = remove_assumption(proof)
    proof = inline_proof(proof, prove_I2())
    proof = inline_proof(proof, _prove_NNE())
    return proof
