# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    phi_imp_psi = Formula('->', antecedent_proof.statement.conclusion, consequent)
    assert antecedent_proof.is_valid()
    assert InferenceRule([], phi_imp_psi).is_specialization_of(
        conditional), f"phi->psi: {phi_imp_psi}\ngeneral: {conditional}"

    new_lines = list(antecedent_proof.lines)  # proof of phi
    new_lines.append(Proof.Line(phi_imp_psi, conditional, []))  # phi implies psi
    new_lines.append(Proof.Line(consequent, MP,
                                [len(antecedent_proof.lines) - 1,
                                 len(new_lines) - 1]))  # psi (thanks to MP from previous line)

    new_proof = Proof(InferenceRule([antecedent_proof.statement.assumptions[0]], consequent),
                      antecedent_proof.rules.union({MP, conditional}),
                      new_lines)
    return new_proof


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)

    phi1 = antecedent1_proof.statement.conclusion
    phi2 = antecedent2_proof.statement.conclusion

    phi2_imp_psi = Formula('->', phi2, consequent)
    phi1_imp_phi2 = Formula('->', phi1, phi2_imp_psi)

    lines = list(antecedent1_proof.lines)  # proof of phi1
    lines.append(Proof.Line(phi1_imp_phi2, double_conditional, []))  # phi1 -> (phi2->psi) [assumption]
    lines.append(Proof.Line(phi2_imp_psi, MP, [len(antecedent1_proof.lines) - 1,  # phi2->psi : MP : [0, 1]
                                               len(antecedent1_proof.lines)]))
    for l in antecedent2_proof.lines:  # proof of phi2
        if l.is_assumption():
            lines.append(l)
        else:
            lines.append(Proof.Line(l.formula, l.rule, [i+len(antecedent1_proof.lines)+2 for i in l.assumptions]))
    lines.append(Proof.Line(consequent, MP, [len(lines) - 1,  # psi : MP : [4, 3]
                                             len(antecedent1_proof.lines) + 1]))
    proof = Proof(InferenceRule(antecedent1_proof.statement.assumptions, consequent),
                  antecedent1_proof.rules.union({MP, double_conditional}),
                  lines)
    return proof


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    phi = proof.statement.assumptions[-1]
    new_assumptions = proof.statement.assumptions[:-1]
    new_lines = []
    lines_bias = 0
    lines_map = [-1]*len(proof.lines)
    for i,line in enumerate(proof.lines):
        zi = line.formula
        if zi == phi:
            new_lines.append(Proof.Line(Formula('->', phi, phi), I0, []))
        elif line.rule == MP:
            j,k = line.assumptions
            j,k = lines_map[j], lines_map[k]
            zj = new_lines[j].formula
            zk = new_lines[k].formula
            phi_imp_zi = Formula('->', phi, zi)
            phi_imp_zj = zj
            p_imp_j__imp__p_imp_i = Formula('->', phi_imp_zj, phi_imp_zi)  # (phi->j)->(phi->i)
            p_imp__j_imp_i = zk  # phi->(j->i)
            new_lines.append(Proof.Line(Formula('->', p_imp__j_imp_i, p_imp_j__imp__p_imp_i), D, []))
            new_lines.append(Proof.Line(p_imp_j__imp__p_imp_i, MP, [k, i+lines_bias]))
            new_lines.append(Proof.Line(phi_imp_zi, MP, [j, i+lines_bias+1]))
            lines_bias += 2
        elif line.formula in new_assumptions or line.rule in proof.rules:
            phi_imp_zi = Formula('->', phi, zi)
            new_lines.append(line)
            new_lines.append(Proof.Line(Formula('->', zi, phi_imp_zi), I1, []))
            new_lines.append(Proof.Line(phi_imp_zi, MP, [i + lines_bias, i + lines_bias + 1]))
            lines_bias += 2
        lines_map[i] = i + lines_bias

    return Proof(InferenceRule(new_assumptions, Formula('->', phi, proof.statement.conclusion)),
                 proof.rules.union({MP, I0, I1, D}), new_lines)


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules

    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)
    # Task 5.6


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    nasm_proof = remove_assumption(proof)
    conclusion = proof.statement.assumptions[-1].first
    spec_map = {'p': I0.conclusion, 'q': conclusion}
    new_lines = list(nasm_proof.lines)

    new_lines.append(Proof.Line(N.specialize(spec_map).conclusion, N, []))
    new_lines.append(Proof.Line(Formula('->', spec_map['p'], spec_map['q']), MP, [len(new_lines)-2, len(new_lines)-1]))
    new_lines.append(Proof.Line(I0.conclusion, I0, []))
    new_lines.append(Proof.Line(spec_map['q'], MP, [len(new_lines)-1, len(new_lines)-2]))

    p = Proof(InferenceRule(nasm_proof.statement.assumptions, conclusion),
              nasm_proof.rules.union({MP, I0, I1, D, N}), new_lines)
    print(p)
    return p
