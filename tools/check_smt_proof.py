#!/usr/bin/env python3
"""Independently validate a satrap QF_BOOL eDRAT certificate."""

from __future__ import annotations

import argparse
import itertools
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import TypeAlias

MAX_NESTING = 1_024


class ProofCheckError(Exception):
    """A malformed input, certificate mismatch, or rejected DRAT proof."""


@dataclass(frozen=True)
class StringAtom:
    value: str


class QuotedSymbol(str):
    pass


SExpr: TypeAlias = str | QuotedSymbol | StringAtom | list["SExpr"]
BoolExpr: TypeAlias = tuple[object, ...]
Clause: TypeAlias = tuple[str, tuple[int, ...]]

FALSE: BoolExpr = (0,)
TRUE: BoolExpr = (1,)


class SExprReader:
    def __init__(self, text: str):
        self.text = text
        self.offset = 0

    def read_all(self) -> list[SExpr]:
        expressions = []
        self._skip_trivia()
        while self.offset < len(self.text):
            expressions.append(self._read(0))
            self._skip_trivia()
        return expressions

    def _read(self, depth: int) -> SExpr:
        if depth > MAX_NESTING:
            raise ProofCheckError("maximum S-expression nesting exceeded")
        self._skip_trivia()
        if self.offset >= len(self.text):
            raise ProofCheckError("unexpected end of S-expression")
        char = self.text[self.offset]
        if char == "(":
            self.offset += 1
            values = []
            while True:
                self._skip_trivia()
                if self.offset >= len(self.text):
                    raise ProofCheckError("unterminated S-expression list")
                if self.text[self.offset] == ")":
                    self.offset += 1
                    return values
                values.append(self._read(depth + 1))
        if char == ")":
            raise ProofCheckError("unexpected closing parenthesis")
        if char == '"':
            return self._read_string()
        if char == "|":
            return self._read_quoted_symbol()
        start = self.offset
        while self.offset < len(self.text):
            char = self.text[self.offset]
            if char.isspace() or char in "();":
                break
            self.offset += 1
        if self.offset == start:
            raise ProofCheckError("expected an S-expression atom")
        return self.text[start : self.offset]

    def _read_string(self) -> StringAtom:
        self.offset += 1
        value = []
        while self.offset < len(self.text):
            char = self.text[self.offset]
            self.offset += 1
            if char != '"':
                value.append(char)
                continue
            if self.offset < len(self.text) and self.text[self.offset] == '"':
                self.offset += 1
                value.append('"')
                continue
            return StringAtom("".join(value))
        raise ProofCheckError("unterminated string literal")

    def _read_quoted_symbol(self) -> QuotedSymbol:
        self.offset += 1
        start = self.offset
        while self.offset < len(self.text) and self.text[self.offset] != "|":
            if self.text[self.offset] == "\\":
                raise ProofCheckError("backslash is not allowed in a quoted symbol")
            self.offset += 1
        if self.offset >= len(self.text):
            raise ProofCheckError("unterminated quoted symbol")
        value = self.text[start : self.offset]
        self.offset += 1
        return QuotedSymbol(value)

    def _skip_trivia(self) -> None:
        while True:
            while self.offset < len(self.text) and self.text[self.offset].isspace():
                self.offset += 1
            if self.offset >= len(self.text) or self.text[self.offset] != ";":
                return
            newline = self.text.find("\n", self.offset)
            self.offset = len(self.text) if newline < 0 else newline + 1


def atom(value: SExpr, role: str) -> str:
    if not isinstance(value, str):
        raise ProofCheckError(f"{role} must be an atom")
    return value


def items(value: SExpr, role: str) -> list[SExpr]:
    if not isinstance(value, list):
        raise ProofCheckError(f"{role} must be a list")
    return value


def exact_arity(values: list[object], count: int, role: str) -> None:
    if len(values) != count:
        raise ProofCheckError(f"{role} expects {count} argument(s)")


def minimum_arity(values: list[object], count: int, role: str) -> None:
    if len(values) < count:
        raise ProofCheckError(f"{role} expects at least {count} argument(s)")


def bool_constant(value: bool) -> BoolExpr:
    return TRUE if value else FALSE


def negate(expression: BoolExpr) -> BoolExpr:
    match expression:
        case (0,):
            return TRUE
        case (1,):
            return FALSE
        case (3, inner):
            return inner
        case _:
            return (3, expression)


def complements(left: BoolExpr, right: BoolExpr) -> bool:
    return (left[0] == 3 and left[1] == right) or (right[0] == 3 and right[1] == left)


def junction(expressions: list[BoolExpr], conjunction: bool) -> BoolExpr:
    flattened = []
    for expression in expressions:
        if expression == FALSE and conjunction:
            return FALSE
        if expression == TRUE and not conjunction:
            return TRUE
        if expression in (TRUE, FALSE):
            continue
        expected = 4 if conjunction else 5
        if expression[0] == expected:
            flattened.extend(expression[1])
        else:
            flattened.append(expression)
    flattened = sorted(set(flattened))
    members = set(flattened)
    if any(item[0] == 3 and item[1] in members for item in flattened):
        return bool_constant(not conjunction)
    if not flattened:
        return bool_constant(conjunction)
    if len(flattened) == 1:
        return flattened[0]
    return (4 if conjunction else 5, tuple(flattened))


def xor(left: BoolExpr, right: BoolExpr) -> BoolExpr:
    if left == right:
        return FALSE
    if complements(left, right):
        return TRUE
    if left == FALSE:
        return right
    if right == FALSE:
        return left
    if left == TRUE:
        return negate(right)
    if right == TRUE:
        return negate(left)
    left, right = sorted((left, right))
    return (6, left, right)


def iff(left: BoolExpr, right: BoolExpr) -> BoolExpr:
    if left == right:
        return TRUE
    if complements(left, right):
        return FALSE
    if left == TRUE:
        return right
    if right == TRUE:
        return left
    if left == FALSE:
        return negate(right)
    if right == FALSE:
        return negate(left)
    left, right = sorted((left, right))
    return (7, left, right)


def ite(condition: BoolExpr, then_term: BoolExpr, else_term: BoolExpr) -> BoolExpr:
    if then_term == else_term:
        return then_term
    if condition == TRUE:
        return then_term
    if condition == FALSE:
        return else_term
    if then_term == TRUE and else_term == FALSE:
        return condition
    if then_term == FALSE and else_term == TRUE:
        return negate(condition)
    return (8, condition, then_term, else_term)


def quote_string(value: str) -> str:
    return f'"{value.replace(chr(34), chr(34) * 2)}"'


def quote_symbol(value: str) -> str:
    reserved = {
        "!",
        "_",
        "as",
        "BINARY",
        "DECIMAL",
        "HEXADECIMAL",
        "NUMERAL",
        "exists",
        "forall",
        "let",
        "match",
        "par",
        "lambda",
    }
    allowed = set("~!@$%^&*_-+=<>.?/")
    simple = (
        bool(value)
        and value not in reserved
        and not value[0].isdigit()
        and all(char.isalnum() or char in allowed for char in value)
    )
    return value if simple else f"|{value}|"


def render(expression: SExpr) -> str:
    if isinstance(expression, StringAtom):
        return quote_string(expression.value)
    if isinstance(expression, QuotedSymbol):
        return f"|{expression}|"
    if isinstance(expression, str):
        if (
            expression.startswith(":")
            or expression.isdigit()
            or expression in {"_", "!", "as", "lambda", "let", "exists", "forall", "match", "par"}
        ):
            return expression
        return quote_symbol(expression)
    return f"({' '.join(render(item) for item in expression)})"


@dataclass
class Frame:
    bound_names: list[str] = field(default_factory=list)
    bound_sorts: list[str] = field(default_factory=list)
    assertions: list[tuple[str, BoolExpr]] = field(default_factory=list)


@dataclass(frozen=True)
class Query:
    premises: tuple[str, ...]
    roots: tuple[BoolExpr, ...]
    has_assumptions: bool


class BoolSession:
    def __init__(self) -> None:
        self.bindings: dict[str, BoolExpr] = {}
        self.sorts: set[str] = set()
        self.frames = [Frame()]
        self.global_declarations = False
        self.produce_proofs = False
        self.logic: str | None = None
        self.last_query: Query | None = None
        self.proof_queries: list[Query] = []

    def execute_all(self, commands: list[SExpr]) -> list[Query]:
        for command in commands:
            self.execute(items(command, "top-level command"))
        return self.proof_queries

    def execute(self, command: list[SExpr]) -> None:
        if not command:
            raise ProofCheckError("empty command")
        name = atom(command[0], "command name")
        arguments = command[1:]
        if name == "set-logic":
            exact_arity(arguments, 1, name)
            logic = atom(arguments[0], "logic")
            if logic != "QF_BOOL":
                raise ProofCheckError("QF_BOOL proof contains a non-QF_BOOL script")
            self.logic = logic
            self._invalidate_query()
        elif name == "set-option":
            exact_arity(arguments, 2, name)
            option = atom(arguments[0], "option")
            if option in {":global-declarations", ":produce-proofs"}:
                value = atom(arguments[1], "option value")
                if value not in {"true", "false"}:
                    raise ProofCheckError(f"{option} expects true or false")
                if self.logic is not None:
                    raise ProofCheckError(f"{option} is a start-mode option")
                enabled = value == "true"
                if option == ":global-declarations":
                    self.global_declarations = enabled
                else:
                    self.produce_proofs = enabled
        elif name in {"set-info", "get-info", "get-option", "echo", "exit"}:
            return
        elif name == "declare-const":
            exact_arity(arguments, 2, name)
            self._declare(atom(arguments[0], "constant name"), arguments[1])
        elif name == "define-sort":
            exact_arity(arguments, 3, name)
            parameters = items(arguments[1], "sort parameters")
            if parameters:
                raise ProofCheckError("QF_BOOL proof checker rejects parameterized sorts")
            self._require_bool_sort(arguments[2])
            sort_name = atom(arguments[0], "sort name")
            if sort_name in self.sorts:
                raise ProofCheckError(f"duplicate sort `{sort_name}`")
            self.sorts.add(sort_name)
            self._declaration_frame().bound_sorts.append(sort_name)
            self._invalidate_query()
        elif name == "declare-fun":
            exact_arity(arguments, 3, name)
            domain = items(arguments[1], "function domain")
            if domain:
                raise ProofCheckError("QF_BOOL proof checker rejects nonconstant functions")
            self._declare(atom(arguments[0], "function name"), arguments[2])
        elif name == "define-const":
            exact_arity(arguments, 3, name)
            self._require_bool_sort(arguments[1])
            self._bind(atom(arguments[0], "constant name"), self.parse_term(arguments[2], []))
        elif name == "define-fun":
            exact_arity(arguments, 4, name)
            parameters = items(arguments[1], "function parameters")
            if parameters:
                raise ProofCheckError("QF_BOOL proof checker rejects nonconstant functions")
            self._require_bool_sort(arguments[2])
            self._bind(atom(arguments[0], "function name"), self.parse_term(arguments[3], []))
        elif name == "assert":
            exact_arity(arguments, 1, name)
            source = render(arguments[0])
            term = self.parse_term(peel_annotation(arguments[0]), [])
            self.frames[-1].assertions.append((source, term))
            self._invalidate_query()
        elif name == "push":
            exact_arity(arguments, 1, name)
            for _ in range(parse_numeral(arguments[0], "push count")):
                self.frames.append(Frame())
            self._invalidate_query()
        elif name == "pop":
            exact_arity(arguments, 1, name)
            count = parse_numeral(arguments[0], "pop count")
            if count >= len(self.frames):
                raise ProofCheckError("pop exceeds active proof-checker scopes")
            for _ in range(count):
                frame = self.frames.pop()
                for bound_name in frame.bound_names:
                    self.bindings.pop(bound_name, None)
                for bound_sort in frame.bound_sorts:
                    self.sorts.discard(bound_sort)
            self._invalidate_query()
        elif name == "check-sat":
            exact_arity(arguments, 0, name)
            self._record_query([])
        elif name == "check-sat-assuming":
            exact_arity(arguments, 1, name)
            assumptions = items(arguments[0], "assumptions")
            parsed = [(render(value), self.parse_term(value, [])) for value in assumptions]
            self._record_query(parsed)
        elif name == "reset-assertions":
            exact_arity(arguments, 0, name)
            if self.global_declarations:
                self.frames = [
                    Frame(
                        bound_names=list(self.bindings),
                        bound_sorts=list(self.sorts),
                    )
                ]
            else:
                self.bindings.clear()
                self.sorts.clear()
                self.frames = [Frame()]
            self._invalidate_query()
        elif name == "reset":
            exact_arity(arguments, 0, name)
            prior_queries = self.proof_queries
            self.__init__()
            self.proof_queries = prior_queries
        elif name == "get-value":
            exact_arity(arguments, 1, name)
            for value in items(arguments[0], "get-value terms"):
                self.parse_term(value, [])
        elif name == "get-proof":
            exact_arity(arguments, 0, name)
            if not self.produce_proofs:
                raise ProofCheckError("get-proof used while proof production is disabled")
            if self.last_query is None:
                raise ProofCheckError("get-proof has no preceding check")
            if self.last_query.has_assumptions:
                raise ProofCheckError("get-proof follows a check with a nonempty assumption set")
            self.proof_queries.append(self.last_query)
        elif name in {
            "get-model",
            "get-assignment",
            "get-assertions",
            "get-unsat-core",
            "get-unsat-assumptions",
        }:
            return
        else:
            raise ProofCheckError(f"unsupported QF_BOOL command `{name}`")

    def parse_term(self, expression: SExpr, locals_: list[dict[str, BoolExpr]]) -> BoolExpr:
        if isinstance(expression, str):
            if expression == "true":
                return TRUE
            if expression == "false":
                return FALSE
            for scope in reversed(locals_):
                if expression in scope:
                    return scope[expression]
            if expression not in self.bindings:
                raise ProofCheckError(f"unknown Boolean symbol `{expression}`")
            return self.bindings[expression]
        values = items(expression, "Boolean term")
        if not values:
            raise ProofCheckError("empty Boolean term")
        operator = atom(values[0], "Boolean operator")
        arguments = values[1:]
        if operator == "let":
            exact_arity(arguments, 2, operator)
            scope = {}
            for binding in items(arguments[0], "let bindings"):
                pair = items(binding, "let binding")
                exact_arity(pair, 2, "let binding")
                name = atom(pair[0], "let name")
                if name in scope:
                    raise ProofCheckError(f"duplicate let name `{name}`")
                scope[name] = self.parse_term(pair[1], locals_)
            return self.parse_term(arguments[1], [*locals_, scope])
        if operator == "!":
            if not arguments:
                raise ProofCheckError("annotation requires a term")
            return self.parse_term(arguments[0], locals_)
        terms = [self.parse_term(argument, locals_) for argument in arguments]
        if operator == "not":
            exact_arity(terms, 1, operator)
            return negate(terms[0])
        if operator == "and":
            minimum_arity(terms, 2, operator)
            return junction(terms, True)
        if operator == "or":
            minimum_arity(terms, 2, operator)
            return junction(terms, False)
        if operator == "xor":
            minimum_arity(terms, 2, operator)
            result = terms[0]
            for term in terms[1:]:
                result = xor(result, term)
            return result
        if operator == "=>":
            minimum_arity(terms, 2, operator)
            result = terms[-1]
            for antecedent in reversed(terms[:-1]):
                result = junction([negate(antecedent), result], False)
            return result
        if operator == "=":
            minimum_arity(terms, 2, operator)
            return junction([iff(terms[0], term) for term in terms[1:]], True)
        if operator == "distinct":
            minimum_arity(terms, 2, operator)
            return junction(
                [
                    negate(iff(terms[left], terms[right]))
                    for left in range(len(terms))
                    for right in range(left + 1, len(terms))
                ],
                True,
            )
        if operator == "ite":
            exact_arity(terms, 3, operator)
            return ite(*terms)
        raise ProofCheckError(f"unsupported QF_BOOL operator `{operator}`")

    def _declare(self, name: str, sort: SExpr) -> None:
        self._require_bool_sort(sort)
        self._bind(name, (2, name))

    def _bind(self, name: str, expression: BoolExpr) -> None:
        if name in self.bindings:
            raise ProofCheckError(f"duplicate Boolean symbol `{name}`")
        self.bindings[name] = expression
        self._declaration_frame().bound_names.append(name)
        self._invalidate_query()

    def _require_bool_sort(self, value: SExpr) -> None:
        sort = atom(value, "sort")
        if sort != "Bool" and sort not in self.sorts:
            raise ProofCheckError("QF_BOOL proof contains a non-Boolean declaration")

    def _record_query(self, assumptions: list[tuple[str, BoolExpr]]) -> None:
        assertions = [assertion for frame in self.frames for assertion in frame.assertions]
        assertions.extend(assumptions)
        self.last_query = Query(
            tuple(source for source, _ in assertions),
            tuple(term for _, term in assertions),
            bool(assumptions),
        )

    def _invalidate_query(self) -> None:
        self.last_query = None

    def _declaration_frame(self) -> Frame:
        return self.frames[0] if self.global_declarations else self.frames[-1]


def peel_annotation(expression: SExpr) -> SExpr:
    if (
        isinstance(expression, list)
        and expression
        and expression[0] == "!"
        and len(expression) >= 2
    ):
        return expression[1]
    return expression


def parse_numeral(value: SExpr, role: str) -> int:
    text = atom(value, role)
    if not text.isdigit():
        raise ProofCheckError(f"{role} must be a numeral")
    return int(text)


class CnfEncoder:
    def __init__(self) -> None:
        self.literals: dict[BoolExpr, int] = {}
        self.truth_literal: int | None = None
        self.variable_count = 0
        self.clauses: list[Clause] = []

    def build(self, roots: tuple[BoolExpr, ...]) -> list[Clause]:
        for root in roots:
            self.add_clause("formula", [self.encode(root)])
        return self.clauses

    def encode(self, expression: BoolExpr) -> int:
        if expression in self.literals:
            return self.literals[expression]
        kind = expression[0]
        if kind == 0:
            literal = -self._truth()
        elif kind == 1:
            literal = self._truth()
        elif kind == 2:
            literal = self._new_variable()
        elif kind == 3:
            literal = -self.encode(expression[1])
        elif kind in (4, 5):
            inputs = [self.encode(item) for item in expression[1]]
            output = self._new_variable()
            if kind == 4:
                for input_literal in inputs:
                    self.add_clause("encoding", [-output, input_literal])
                self.add_clause("encoding", [output, *(-value for value in inputs)])
            else:
                for input_literal in inputs:
                    self.add_clause("encoding", [-input_literal, output])
                self.add_clause("encoding", [-output, *inputs])
            literal = output
        elif kind in (6, 7):
            left = self.encode(expression[1])
            right = self.encode(expression[2])
            output = self._new_variable()
            clauses = (
                (
                    [left, right, -output],
                    [-left, -right, -output],
                    [left, -right, output],
                    [-left, right, output],
                )
                if kind == 6
                else (
                    [left, right, output],
                    [-left, -right, output],
                    [left, -right, -output],
                    [-left, right, -output],
                )
            )
            for clause in clauses:
                self.add_clause("encoding", clause)
            literal = output
        elif kind == 8:
            condition = self.encode(expression[1])
            then_term = self.encode(expression[2])
            else_term = self.encode(expression[3])
            output = self._new_variable()
            for clause in (
                [-condition, -then_term, output],
                [-condition, then_term, -output],
                [condition, -else_term, output],
                [condition, else_term, -output],
            ):
                self.add_clause("encoding", clause)
            literal = output
        else:
            raise ProofCheckError(f"unknown canonical Boolean node {kind}")
        self.literals[expression] = literal
        return literal

    def add_clause(self, kind: str, literals: list[int]) -> None:
        normalized = sorted(set(literals), key=literal_index)
        for left, right in itertools.pairwise(normalized):
            if abs(left) == abs(right):
                return
        self.clauses.append((kind, tuple(normalized)))

    def _truth(self) -> int:
        if self.truth_literal is None:
            self.truth_literal = self._new_variable()
            self.add_clause("encoding", [self.truth_literal])
        return self.truth_literal

    def _new_variable(self) -> int:
        self.variable_count += 1
        return self.variable_count


def literal_index(literal: int) -> int:
    return (abs(literal) - 1) * 2 + (0 if literal > 0 else 1)


@dataclass(frozen=True)
class Certificate:
    variable_count: int
    premises: tuple[str, ...]
    clauses: tuple[Clause, ...]
    drat: str


def parse_certificate(text: str) -> Certificate:
    candidates = [
        expression
        for expression in SExprReader(text).read_all()
        if isinstance(expression, list) and expression and expression[0] == "satrap-edrat"
    ]
    if len(candidates) != 1:
        raise ProofCheckError("proof output must contain exactly one satrap-edrat certificate")
    values = candidates[0]
    if len(values) % 2 != 1:
        raise ProofCheckError("satrap-edrat fields must be keyword/value pairs")
    fields = {}
    for index in range(1, len(values), 2):
        name = atom(values[index], "certificate field")
        if name in fields:
            raise ProofCheckError(f"duplicate satrap-edrat field `{name}`")
        fields[name] = values[index + 1]
    expected_fields = {
        ":version",
        ":logic",
        ":variables",
        ":premises",
        ":clauses",
        ":drat",
    }
    if set(fields) != expected_fields:
        missing = sorted(expected_fields - set(fields))
        unknown = sorted(set(fields) - expected_fields)
        detail = []
        if missing:
            detail.append(f"missing {', '.join(missing)}")
        if unknown:
            detail.append(f"unknown {', '.join(unknown)}")
        raise ProofCheckError(f"invalid satrap-edrat fields: {'; '.join(detail)}")
    if atom(fields.get(":version", []), "proof version") != "1":
        raise ProofCheckError("unsupported satrap-edrat proof version")
    if atom(fields.get(":logic", []), "proof logic") != "QF_BOOL":
        raise ProofCheckError("satrap-edrat checker currently accepts only QF_BOOL")
    variable_count = parse_numeral(fields.get(":variables", []), "proof variable count")
    premises = []
    for value in items(fields.get(":premises", ""), "proof premises"):
        if not isinstance(value, StringAtom):
            raise ProofCheckError("proof premises must be strings")
        premises.append(value.value)
    clauses = []
    for raw_clause in items(fields.get(":clauses", ""), "proof clauses"):
        parts = items(raw_clause, "proof clause")
        if not parts:
            raise ProofCheckError("proof clause must name its origin")
        kind = atom(parts[0], "proof clause origin")
        if kind not in {"formula", "encoding"}:
            raise ProofCheckError(f"QF_BOOL proof contains forbidden `{kind}` clause")
        try:
            literals = tuple(int(atom(value, "proof literal")) for value in parts[1:])
        except ValueError as error:
            raise ProofCheckError("proof clause contains a noninteger literal") from error
        if any(literal == 0 for literal in literals):
            raise ProofCheckError("proof input clauses must not contain DIMACS terminators")
        clauses.append((kind, literals))
    drat_value = fields.get(":drat")
    if not isinstance(drat_value, StringAtom):
        raise ProofCheckError("DRAT suffix must be a string")
    return Certificate(variable_count, tuple(premises), tuple(clauses), drat_value.value)


def validate_encoding(script: str, proof: str) -> Certificate:
    certificate = parse_certificate(proof)
    queries = BoolSession().execute_all(SExprReader(script).read_all())
    matches = [query for query in queries if query.premises == certificate.premises]
    if not matches:
        raise ProofCheckError(
            "certificate premises do not match any active query in the original script"
        )
    expected_roots = {query.roots for query in matches}
    if len(expected_roots) != 1:
        raise ProofCheckError("matching source queries have different Boolean meanings")
    encoder = CnfEncoder()
    expected_clauses = tuple(encoder.build(next(iter(expected_roots))))
    if encoder.variable_count != certificate.variable_count:
        raise ProofCheckError(
            "proof variable count does not match the independently reconstructed encoding"
        )
    if expected_clauses != certificate.clauses:
        raise ProofCheckError(
            "proof clauses do not match the independently reconstructed QF_BOOL encoding"
        )
    return certificate


def check_drat(certificate: Certificate, checker: Path, timeout: float) -> None:
    if not checker.is_file():
        raise ProofCheckError(f"DRAT checker does not exist: {checker}")
    with tempfile.TemporaryDirectory(prefix="satrap-smt-proof-") as directory:
        root = Path(directory)
        cnf_path = root / "query.cnf"
        proof_path = root / "query.drat"
        cnf = [f"p cnf {certificate.variable_count} {len(certificate.clauses)}"]
        cnf.extend(
            f"{' '.join(str(value) for value in literals)} 0" for _, literals in certificate.clauses
        )
        cnf_path.write_text("\n".join(cnf) + "\n", encoding="utf-8", newline="\n")
        proof_path.write_text(certificate.drat, encoding="utf-8", newline="\n")
        try:
            result = subprocess.run(
                [str(checker), str(cnf_path), str(proof_path)],
                capture_output=True,
                check=False,
                text=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as error:
            raise ProofCheckError("DRAT checker timed out") from error
    lines = [*result.stdout.splitlines(), *result.stderr.splitlines()]
    if result.returncode != 0 or "s VERIFIED" not in lines:
        tail = "\n".join(lines[-20:])
        raise ProofCheckError(f"DRAT checker rejected the proof\n{tail}".rstrip())


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="original SMT-LIB script")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--proof", type=Path, help="solver output or proof response")
    source.add_argument("--solver", type=Path, help="SMT executable to run on the input")
    parser.add_argument("--checker", type=Path, required=True, help="DRAT-trim executable")
    parser.add_argument("--timeout", type=float, default=60.0)
    return parser.parse_args()


def run_solver(solver: Path, script: str, timeout: float) -> str:
    if not solver.is_file():
        raise ProofCheckError(f"SMT solver does not exist: {solver}")
    try:
        result = subprocess.run(
            [str(solver)],
            capture_output=True,
            check=False,
            input=script,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        raise ProofCheckError("SMT proof-producing query timed out") from error
    if result.returncode != 0:
        tail = "\n".join(result.stderr.splitlines()[-20:])
        raise ProofCheckError(f"SMT solver failed while producing a proof\n{tail}".rstrip())
    responses = SExprReader(result.stdout).read_all()
    for response in responses:
        if response == "unsupported" or (
            isinstance(response, list) and response and response[0] == "error"
        ):
            raise ProofCheckError(f"SMT solver emitted a non-success response: {render(response)}")
    if "unsat" not in responses:
        raise ProofCheckError("SMT solver did not report an exact unsat line")
    return result.stdout


def main() -> int:
    arguments = parse_args()
    try:
        script = arguments.input.read_text(encoding="utf-8")
        if arguments.proof is not None:
            proof = arguments.proof.read_text(encoding="utf-8")
        else:
            proof = run_solver(arguments.solver, script, arguments.timeout)
        certificate = validate_encoding(script, proof)
        check_drat(certificate, arguments.checker, arguments.timeout)
    except (OSError, ProofCheckError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print("SMT proof independently VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
