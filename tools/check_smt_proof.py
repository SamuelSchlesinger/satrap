#!/usr/bin/env python3
"""Independently validate a satrap QF_BOOL or QF_BV eDRAT certificate."""

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
MAX_BITVECTOR_WIDTH = 1_048_576
MAX_QUADRATIC_LOWERING_WORK = 16_000_000


@dataclass(frozen=True)
class BitVecExpr:
    """A bit-vector expression whose bits are stored least-significant first."""

    bits: tuple[BoolExpr, ...]


@dataclass(frozen=True)
class BitVecSort:
    width: int


TermExpr: TypeAlias = BoolExpr | BitVecExpr
SortExpr: TypeAlias = str | BitVecSort
BOOL_SORT = "Bool"


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


def expect_bool_term(value: TermExpr, role: str) -> BoolExpr:
    if isinstance(value, BitVecExpr):
        raise ProofCheckError(f"{role} must have sort Bool")
    return value


def expect_bitvec_term(value: TermExpr, role: str) -> BitVecExpr:
    if not isinstance(value, BitVecExpr):
        raise ProofCheckError(f"{role} must have bit-vector sort")
    return value


def term_sort(value: TermExpr) -> SortExpr:
    return BitVecSort(len(value.bits)) if isinstance(value, BitVecExpr) else BOOL_SORT


def check_bitvector_width(width: int) -> None:
    if width <= 0:
        raise ProofCheckError("bit-vector width must be greater than zero")
    if width > MAX_BITVECTOR_WIDTH:
        raise ProofCheckError(
            f"bit-vector width {width} exceeds the current limit of {MAX_BITVECTOR_WIDTH}"
        )


def check_quadratic_work(width: int, operation: str) -> None:
    if width * width > MAX_QUADRATIC_LOWERING_WORK:
        raise ProofCheckError(
            f"`{operation}` at width {width} exceeds the Boolean-lowering work limit"
        )


def bitvector_constant(value: int, width: int) -> BitVecExpr:
    check_bitvector_width(width)
    if value < 0 or value.bit_length() > width:
        raise ProofCheckError(f"decimal value does not fit in a {width}-bit vector")
    return BitVecExpr(tuple(bool_constant(bool(value & (1 << index))) for index in range(width)))


def same_width(left: BitVecExpr, right: BitVecExpr, operation: str) -> int:
    if len(left.bits) != len(right.bits):
        raise ProofCheckError(
            f"`{operation}` operands have widths {len(left.bits)} and {len(right.bits)}"
        )
    return len(left.bits)


def add_bits(
    left: tuple[BoolExpr, ...], right: tuple[BoolExpr, ...]
) -> tuple[tuple[BoolExpr, ...], BoolExpr]:
    if len(left) != len(right):
        raise ProofCheckError("bit-vector addition operands have different widths")
    carry = FALSE
    result = []
    for left_bit, right_bit in zip(left, right, strict=True):
        pair_sum = xor(left_bit, right_bit)
        result.append(xor(pair_sum, carry))
        pair_carry = junction([left_bit, right_bit], True)
        propagated = junction([pair_sum, carry], True)
        carry = junction([pair_carry, propagated], False)
    return tuple(result), carry


def negate_bits(bits: tuple[BoolExpr, ...]) -> tuple[BoolExpr, ...]:
    inverted = tuple(negate(bit) for bit in bits)
    one = (TRUE, *(FALSE for _ in bits[1:]))
    return add_bits(inverted, one)[0]


def subtract_bits(left: tuple[BoolExpr, ...], right: tuple[BoolExpr, ...]) -> tuple[BoolExpr, ...]:
    return add_bits(left, negate_bits(right))[0]


def multiply_bits(
    left: tuple[BoolExpr, ...],
    right: tuple[BoolExpr, ...],
    output_width: int,
) -> tuple[BoolExpr, ...]:
    result = (FALSE,) * output_width
    for right_index, right_bit in enumerate(right[:output_width]):
        partial = [FALSE] * output_width
        for left_index, left_bit in enumerate(left):
            output = left_index + right_index
            if output >= output_width:
                break
            partial[output] = junction([left_bit, right_bit], True)
        result = add_bits(result, tuple(partial))[0]
    return result


def unsigned_less_than_bits(left: tuple[BoolExpr, ...], right: tuple[BoolExpr, ...]) -> BoolExpr:
    if len(left) != len(right):
        raise ProofCheckError("bit-vector comparison operands have different widths")
    less = FALSE
    equal = TRUE
    for left_bit, right_bit in reversed(tuple(zip(left, right, strict=True))):
        left_less = junction([negate(left_bit), right_bit], True)
        decisive = junction([equal, left_less], True)
        less = junction([less, decisive], False)
        equal = junction([equal, iff(left_bit, right_bit)], True)
    return less


def select_bits(
    condition: BoolExpr,
    then_bits: tuple[BoolExpr, ...],
    else_bits: tuple[BoolExpr, ...],
) -> tuple[BoolExpr, ...]:
    if len(then_bits) != len(else_bits):
        raise ProofCheckError("bit-vector ite branches have different widths")
    return tuple(
        ite(condition, then_bit, else_bit)
        for then_bit, else_bit in zip(then_bits, else_bits, strict=True)
    )


def is_zero_bits(bits: tuple[BoolExpr, ...]) -> BoolExpr:
    return junction([negate(bit) for bit in bits], True)


def unsigned_divide_bits(
    dividend: tuple[BoolExpr, ...], divisor: tuple[BoolExpr, ...]
) -> tuple[tuple[BoolExpr, ...], tuple[BoolExpr, ...]]:
    if len(dividend) != len(divisor):
        raise ProofCheckError("bit-vector division operands have different widths")
    check_quadratic_work(len(dividend), "bit-vector division")
    extended_divisor = (*divisor, FALSE)
    remainder = [FALSE] * (len(dividend) + 1)
    quotient = [FALSE] * len(dividend)
    for index in reversed(range(len(dividend))):
        for bit in reversed(range(1, len(remainder))):
            remainder[bit] = remainder[bit - 1]
        remainder[0] = dividend[index]
        less = unsigned_less_than_bits(tuple(remainder), extended_divisor)
        greater_or_equal = negate(less)
        subtracted = subtract_bits(tuple(remainder), extended_divisor)
        remainder = list(select_bits(greater_or_equal, subtracted, tuple(remainder)))
        quotient[index] = greater_or_equal
    return tuple(quotient), tuple(remainder[:-1])


def bitvector_not(term: BitVecExpr) -> BitVecExpr:
    return BitVecExpr(tuple(negate(bit) for bit in term.bits))


def bitvector_fold(terms: list[BitVecExpr], operation: str) -> BitVecExpr:
    minimum_arity(terms, 2, operation)
    result = terms[0].bits
    for right_term in terms[1:]:
        if len(right_term.bits) != len(result):
            raise ProofCheckError(f"all arguments to `{operation}` must have the same width")
        if operation == "bvand":
            result = tuple(
                junction([left, right], True)
                for left, right in zip(result, right_term.bits, strict=True)
            )
        elif operation == "bvor":
            result = tuple(
                junction([left, right], False)
                for left, right in zip(result, right_term.bits, strict=True)
            )
        elif operation == "bvxor":
            result = tuple(
                xor(left, right) for left, right in zip(result, right_term.bits, strict=True)
            )
        elif operation == "bvadd":
            result = add_bits(result, right_term.bits)[0]
        elif operation == "bvmul":
            check_quadratic_work(len(result), operation)
            result = multiply_bits(result, right_term.bits, len(result))
        else:
            raise ProofCheckError(f"unknown bit-vector fold `{operation}`")
    return BitVecExpr(result)


def bitvector_equal(left: BitVecExpr, right: BitVecExpr) -> BoolExpr:
    same_width(left, right, "=")
    return junction(
        [
            iff(left_bit, right_bit)
            for left_bit, right_bit in zip(left.bits, right.bits, strict=True)
        ],
        True,
    )


def bitvector_concat(left: BitVecExpr, right: BitVecExpr) -> BitVecExpr:
    width = len(left.bits) + len(right.bits)
    check_bitvector_width(width)
    return BitVecExpr((*right.bits, *left.bits))


def bitvector_extract(term: BitVecExpr, high: int, low: int) -> BitVecExpr:
    if low > high or high >= len(term.bits):
        raise ProofCheckError(f"invalid extraction range [{high}:{low}] for width {len(term.bits)}")
    return BitVecExpr(term.bits[low : high + 1])


def bitvector_repeat(term: BitVecExpr, count: int) -> BitVecExpr:
    if count <= 0:
        raise ProofCheckError("bit-vector repeat count must be positive")
    check_bitvector_width(len(term.bits) * count)
    return BitVecExpr(term.bits * count)


def bitvector_extend(term: BitVecExpr, amount: int, signed: bool) -> BitVecExpr:
    check_bitvector_width(len(term.bits) + amount)
    extension = term.bits[-1] if signed else FALSE
    return BitVecExpr((*term.bits, *(extension for _ in range(amount))))


def bitvector_rotate(term: BitVecExpr, amount: int, left: bool) -> BitVecExpr:
    width = len(term.bits)
    amount %= width
    result = [FALSE] * width
    for index, bit in enumerate(term.bits):
        target = (index + amount) % width if left else (index + width - amount) % width
        result[target] = bit
    return BitVecExpr(tuple(result))


def bitvector_negate(term: BitVecExpr) -> BitVecExpr:
    return BitVecExpr(negate_bits(term.bits))


def bitvector_subtract(left: BitVecExpr, right: BitVecExpr) -> BitVecExpr:
    same_width(left, right, "bvsub")
    return BitVecExpr(subtract_bits(left.bits, right.bits))


def bitvector_division(left: BitVecExpr, right: BitVecExpr, operation: str) -> BitVecExpr:
    same_width(left, right, operation)
    if operation in {"bvudiv", "bvurem"}:
        quotient, remainder = unsigned_divide_bits(left.bits, right.bits)
        return BitVecExpr(quotient if operation == "bvudiv" else remainder)

    left_sign = left.bits[-1]
    right_sign = right.bits[-1]
    absolute_left = select_bits(left_sign, negate_bits(left.bits), left.bits)
    absolute_right = select_bits(right_sign, negate_bits(right.bits), right.bits)
    quotient, unsigned_remainder = unsigned_divide_bits(absolute_left, absolute_right)
    if operation == "bvsdiv":
        negative = xor(left_sign, right_sign)
        return BitVecExpr(select_bits(negative, negate_bits(quotient), quotient))
    if operation == "bvsrem":
        return BitVecExpr(
            select_bits(left_sign, negate_bits(unsigned_remainder), unsigned_remainder)
        )
    if operation != "bvsmod":
        raise ProofCheckError(f"unknown bit-vector division `{operation}`")

    remainder_is_zero = is_zero_bits(unsigned_remainder)
    negated_remainder = negate_bits(unsigned_remainder)
    negative_positive = add_bits(negated_remainder, right.bits)[0]
    positive_negative = add_bits(unsigned_remainder, right.bits)[0]
    not_left_sign = negate(left_sign)
    not_right_sign = negate(right_sign)
    both_positive = junction([not_left_sign, not_right_sign], True)
    left_negative = junction([left_sign, not_right_sign], True)
    left_positive = junction([not_left_sign, right_sign], True)
    result = negated_remainder
    result = select_bits(left_positive, positive_negative, result)
    result = select_bits(left_negative, negative_positive, result)
    result = select_bits(both_positive, unsigned_remainder, result)
    return BitVecExpr(select_bits(remainder_is_zero, unsigned_remainder, result))


def bitvector_shift(value: BitVecExpr, amount: BitVecExpr, operation: str) -> BitVecExpr:
    width = same_width(value, amount, operation)
    result = value.bits
    sign = result[-1]
    for index, selector in enumerate(amount.bits):
        shift = 1 << index
        fill = sign if operation == "bvashr" else FALSE
        if shift < width:
            if operation == "bvshl":
                candidate = tuple(
                    result[output - shift] if output >= shift else FALSE for output in range(width)
                )
            else:
                candidate = tuple(
                    result[output + shift] if output + shift < width else fill
                    for output in range(width)
                )
        else:
            candidate = (fill,) * width
        result = select_bits(selector, candidate, result)
    return BitVecExpr(result)


def bitvector_compare(left: BitVecExpr, right: BitVecExpr, operation: str) -> BoolExpr:
    same_width(left, right, operation)
    if operation == "bvult":
        return unsigned_less_than_bits(left.bits, right.bits)
    if operation == "bvule":
        return negate(unsigned_less_than_bits(right.bits, left.bits))
    if operation == "bvugt":
        return unsigned_less_than_bits(right.bits, left.bits)
    if operation == "bvuge":
        return negate(unsigned_less_than_bits(left.bits, right.bits))

    def signed_less(first: BitVecExpr, second: BitVecExpr) -> BoolExpr:
        signs_differ = xor(first.bits[-1], second.bits[-1])
        unsigned = unsigned_less_than_bits(first.bits, second.bits)
        return ite(signs_differ, first.bits[-1], unsigned)

    if operation == "bvslt":
        return signed_less(left, right)
    if operation == "bvsle":
        return negate(signed_less(right, left))
    if operation == "bvsgt":
        return signed_less(right, left)
    if operation == "bvsge":
        return negate(signed_less(left, right))
    raise ProofCheckError(f"unknown bit-vector comparison `{operation}`")


def bitvector_overflow(left: BitVecExpr, right: BitVecExpr | None, operation: str) -> BoolExpr:
    if operation == "bvnego":
        return junction([left.bits[-1], is_zero_bits(left.bits[:-1])], True)
    if right is None:
        raise ProofCheckError(f"`{operation}` expects two bit-vector arguments")
    width = same_width(left, right, operation)
    if operation == "bvuaddo":
        return add_bits(left.bits, right.bits)[1]
    if operation == "bvsaddo":
        result = add_bits(left.bits, right.bits)[0]
        same_inputs = iff(left.bits[-1], right.bits[-1])
        changed_sign = xor(left.bits[-1], result[-1])
        return junction([same_inputs, changed_sign], True)
    if operation == "bvusubo":
        return unsigned_less_than_bits(left.bits, right.bits)
    if operation == "bvssubo":
        result = subtract_bits(left.bits, right.bits)
        different_inputs = xor(left.bits[-1], right.bits[-1])
        changed_sign = xor(left.bits[-1], result[-1])
        return junction([different_inputs, changed_sign], True)
    if operation == "bvumulo":
        check_quadratic_work(width, operation)
        full_width = width * 2
        check_bitvector_width(full_width)
        extended_left = (*left.bits, *(FALSE for _ in range(width)))
        extended_right = (*right.bits, *(FALSE for _ in range(width)))
        product = multiply_bits(extended_left, extended_right, full_width)
        return negate(is_zero_bits(product[width:]))
    if operation == "bvsmulo":
        check_quadratic_work(width, operation)
        full_width = width * 2
        check_bitvector_width(full_width)
        extended_left = (*left.bits, *(left.bits[-1] for _ in range(width)))
        extended_right = (*right.bits, *(right.bits[-1] for _ in range(width)))
        product = multiply_bits(extended_left, extended_right, full_width)
        result_sign = product[width - 1]
        fits = junction([iff(bit, result_sign) for bit in product[width:]], True)
        return negate(fits)
    if operation == "bvsdivo":
        minimum = bitvector_overflow(left, None, "bvnego")
        negative_one = junction([iff(bit, TRUE) for bit in right.bits], True)
        return junction([minimum, negative_one], True)
    raise ProofCheckError(f"unknown bit-vector overflow operator `{operation}`")


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
            or expression.startswith(("#b", "#x"))
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
    logic: str
    premises: tuple[str, ...]
    roots: tuple[BoolExpr, ...]
    has_assumptions: bool


class ProofSession:
    def __init__(self) -> None:
        self.bindings: dict[str, TermExpr] = {}
        self.sorts: dict[str, SortExpr] = {}
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
            if self.logic is not None:
                raise ProofCheckError("logic has already been set")
            if logic not in {"QF_BOOL", "QF_BV"}:
                raise ProofCheckError("proof script uses an unsupported logic")
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
                raise ProofCheckError("proof checker rejects parameterized sorts")
            sort = self.parse_sort(arguments[2])
            sort_name = atom(arguments[0], "sort name")
            if sort_name in self.sorts:
                raise ProofCheckError(f"duplicate sort `{sort_name}`")
            self.sorts[sort_name] = sort
            self._declaration_frame().bound_sorts.append(sort_name)
            self._invalidate_query()
        elif name == "declare-fun":
            exact_arity(arguments, 3, name)
            domain = items(arguments[1], "function domain")
            if domain:
                raise ProofCheckError("proof checker rejects nonconstant functions")
            self._declare(atom(arguments[0], "function name"), arguments[2])
        elif name == "define-const":
            exact_arity(arguments, 3, name)
            sort = self.parse_sort(arguments[1])
            term = self.parse_term(arguments[2], [])
            self._require_declared_sort(term, sort, "constant definition")
            self._bind(atom(arguments[0], "constant name"), term)
        elif name == "define-fun":
            exact_arity(arguments, 4, name)
            parameters = items(arguments[1], "function parameters")
            if parameters:
                raise ProofCheckError("proof checker rejects nonconstant functions")
            sort = self.parse_sort(arguments[2])
            term = self.parse_term(arguments[3], [])
            self._require_declared_sort(term, sort, "function definition")
            self._bind(atom(arguments[0], "function name"), term)
        elif name == "assert":
            exact_arity(arguments, 1, name)
            source = render(arguments[0])
            term = expect_bool_term(self.parse_term(peel_annotation(arguments[0]), []), "assertion")
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
                    self.sorts.pop(bound_sort, None)
            self._invalidate_query()
        elif name == "check-sat":
            exact_arity(arguments, 0, name)
            self._record_query([])
        elif name == "check-sat-assuming":
            exact_arity(arguments, 1, name)
            assumptions = items(arguments[0], "assumptions")
            parsed = [
                (
                    render(value),
                    expect_bool_term(self.parse_term(value, []), "check assumption"),
                )
                for value in assumptions
            ]
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
            raise ProofCheckError(f"unsupported proof-script command `{name}`")

    def parse_term(self, expression: SExpr, locals_: list[dict[str, TermExpr]]) -> TermExpr:
        if isinstance(expression, str):
            if expression == "true":
                return TRUE
            if expression == "false":
                return FALSE
            if expression.startswith("#b"):
                digits = expression[2:]
                if not digits or any(digit not in "01" for digit in digits):
                    raise ProofCheckError("invalid binary bit-vector literal")
                return BitVecExpr(tuple(bool_constant(digit == "1") for digit in reversed(digits)))
            if expression.startswith("#x"):
                digits = expression[2:]
                if not digits:
                    raise ProofCheckError("invalid hexadecimal bit-vector literal")
                try:
                    value = int(digits, 16)
                except ValueError as error:
                    raise ProofCheckError("invalid hexadecimal bit-vector literal") from error
                return bitvector_constant(value, len(digits) * 4)
            for scope in reversed(locals_):
                if expression in scope:
                    return scope[expression]
            if expression not in self.bindings:
                raise ProofCheckError(f"unknown term symbol `{expression}`")
            return self.bindings[expression]
        values = items(expression, "term")
        if not values:
            raise ProofCheckError("empty term")
        if isinstance(values[0], list):
            identifier = items(values[0], "indexed identifier")
            terms = [self.parse_term(argument, locals_) for argument in values[1:]]
            return self._apply_indexed(identifier, terms)
        operator = atom(values[0], "term operator")
        arguments = values[1:]
        if operator == "_":
            exact_arity(arguments, 2, "indexed bit-vector literal")
            value = atom(arguments[0], "bit-vector value")
            if not value.startswith("bv") or not value[2:].isdigit():
                raise ProofCheckError("invalid indexed bit-vector literal")
            width = parse_numeral(arguments[1], "bit-vector width")
            return bitvector_constant(int(value[2:]), width)
        if operator == "let":
            exact_arity(arguments, 2, operator)
            scope: dict[str, TermExpr] = {}
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
            return negate(expect_bool_term(terms[0], operator))
        if operator == "and":
            minimum_arity(terms, 2, operator)
            return junction([expect_bool_term(term, operator) for term in terms], True)
        if operator == "or":
            minimum_arity(terms, 2, operator)
            return junction([expect_bool_term(term, operator) for term in terms], False)
        if operator == "xor":
            minimum_arity(terms, 2, operator)
            boolean_terms = [expect_bool_term(term, operator) for term in terms]
            result = boolean_terms[0]
            for term in boolean_terms[1:]:
                result = xor(result, term)
            return result
        if operator == "=>":
            minimum_arity(terms, 2, operator)
            boolean_terms = [expect_bool_term(term, operator) for term in terms]
            result = boolean_terms[-1]
            for antecedent in reversed(boolean_terms[:-1]):
                result = junction([negate(antecedent), result], False)
            return result
        if operator == "=":
            minimum_arity(terms, 2, operator)
            return junction([self._equivalent(terms[0], term) for term in terms[1:]], True)
        if operator == "distinct":
            minimum_arity(terms, 2, operator)
            return junction(
                [
                    negate(self._equivalent(terms[left], terms[right]))
                    for left in range(len(terms))
                    for right in range(left + 1, len(terms))
                ],
                True,
            )
        if operator == "ite":
            exact_arity(terms, 3, operator)
            condition = expect_bool_term(terms[0], "ite condition")
            if term_sort(terms[1]) != term_sort(terms[2]):
                raise ProofCheckError("ite branches have different sorts")
            if isinstance(terms[1], BitVecExpr):
                else_term = expect_bitvec_term(terms[2], "ite branch")
                return BitVecExpr(select_bits(condition, terms[1].bits, else_term.bits))
            return ite(condition, terms[1], expect_bool_term(terms[2], "ite branch"))
        if operator == "concat":
            exact_arity(terms, 2, operator)
            return bitvector_concat(
                expect_bitvec_term(terms[0], operator),
                expect_bitvec_term(terms[1], operator),
            )
        if operator == "bvnot":
            exact_arity(terms, 1, operator)
            return bitvector_not(expect_bitvec_term(terms[0], operator))
        if operator == "bvneg":
            exact_arity(terms, 1, operator)
            return bitvector_negate(expect_bitvec_term(terms[0], operator))
        if operator in {"bvand", "bvor", "bvxor", "bvadd", "bvmul"}:
            return bitvector_fold([expect_bitvec_term(term, operator) for term in terms], operator)
        if operator in {"bvnand", "bvnor", "bvxnor", "bvcomp"}:
            exact_arity(terms, 2, operator)
            left = expect_bitvec_term(terms[0], operator)
            right = expect_bitvec_term(terms[1], operator)
            same_width(left, right, operator)
            if operator == "bvcomp":
                return BitVecExpr((bitvector_equal(left, right),))
            base = {
                "bvnand": "bvand",
                "bvnor": "bvor",
                "bvxnor": "bvxor",
            }[operator]
            return bitvector_not(bitvector_fold([left, right], base))
        if operator == "bvsub":
            exact_arity(terms, 2, operator)
            return bitvector_subtract(
                expect_bitvec_term(terms[0], operator),
                expect_bitvec_term(terms[1], operator),
            )
        if operator in {"bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"}:
            exact_arity(terms, 2, operator)
            return bitvector_division(
                expect_bitvec_term(terms[0], operator),
                expect_bitvec_term(terms[1], operator),
                operator,
            )
        if operator in {"bvshl", "bvlshr", "bvashr"}:
            exact_arity(terms, 2, operator)
            return bitvector_shift(
                expect_bitvec_term(terms[0], operator),
                expect_bitvec_term(terms[1], operator),
                operator,
            )
        if operator in {
            "bvult",
            "bvule",
            "bvugt",
            "bvuge",
            "bvslt",
            "bvsle",
            "bvsgt",
            "bvsge",
        }:
            exact_arity(terms, 2, operator)
            return bitvector_compare(
                expect_bitvec_term(terms[0], operator),
                expect_bitvec_term(terms[1], operator),
                operator,
            )
        if operator == "bvnego":
            exact_arity(terms, 1, operator)
            return bitvector_overflow(expect_bitvec_term(terms[0], operator), None, operator)
        if operator in {
            "bvuaddo",
            "bvsaddo",
            "bvumulo",
            "bvsmulo",
            "bvusubo",
            "bvssubo",
            "bvsdivo",
        }:
            exact_arity(terms, 2, operator)
            return bitvector_overflow(
                expect_bitvec_term(terms[0], operator),
                expect_bitvec_term(terms[1], operator),
                operator,
            )
        raise ProofCheckError(f"unsupported proof term operator `{operator}`")

    def _declare(self, name: str, sort: SExpr) -> None:
        parsed_sort = self.parse_sort(sort)
        if self.logic == "QF_BOOL" and parsed_sort != BOOL_SORT:
            raise ProofCheckError("QF_BOOL proof contains a bit-vector declaration")
        if parsed_sort == BOOL_SORT:
            term: TermExpr = (2, 0, name)
        else:
            term = BitVecExpr(tuple((2, 1, name, index) for index in range(parsed_sort.width)))
        self._bind(name, term)

    def _bind(self, name: str, expression: TermExpr) -> None:
        if name in self.bindings:
            raise ProofCheckError(f"duplicate term symbol `{name}`")
        self.bindings[name] = expression
        self._declaration_frame().bound_names.append(name)
        self._invalidate_query()

    def parse_sort(self, value: SExpr) -> SortExpr:
        if isinstance(value, str):
            if value == "Bool":
                return BOOL_SORT
            if value in self.sorts:
                return self.sorts[value]
            raise ProofCheckError(f"unsupported proof sort `{value}`")
        values = items(value, "sort")
        if len(values) == 3 and values[0] == "_" and values[1] == "BitVec":
            width = parse_numeral(values[2], "bit-vector width")
            check_bitvector_width(width)
            if self.logic == "QF_BOOL":
                raise ProofCheckError("QF_BOOL proof contains a bit-vector sort")
            return BitVecSort(width)
        raise ProofCheckError("proof checker accepts only Bool and BitVec sorts")

    def _apply_indexed(self, identifier: list[SExpr], terms: list[TermExpr]) -> TermExpr:
        if len(identifier) < 3 or identifier[0] != "_":
            raise ProofCheckError("invalid indexed bit-vector operator")
        operator = atom(identifier[1], "indexed operator")
        exact_arity(terms, 1, operator)
        term = expect_bitvec_term(terms[0], operator)
        if operator == "extract":
            exact_arity(identifier, 4, "extract identifier")
            high = parse_numeral(identifier[2], "extract high index")
            low = parse_numeral(identifier[3], "extract low index")
            return bitvector_extract(term, high, low)
        exact_arity(identifier, 3, f"{operator} identifier")
        index = parse_numeral(identifier[2], f"{operator} index")
        if operator == "repeat":
            return bitvector_repeat(term, index)
        if operator == "zero_extend":
            return bitvector_extend(term, index, False)
        if operator == "sign_extend":
            return bitvector_extend(term, index, True)
        if operator == "rotate_left":
            return bitvector_rotate(term, index, True)
        if operator == "rotate_right":
            return bitvector_rotate(term, index, False)
        raise ProofCheckError(f"unsupported indexed bit-vector operator `{operator}`")

    def _equivalent(self, left: TermExpr, right: TermExpr) -> BoolExpr:
        if term_sort(left) != term_sort(right):
            raise ProofCheckError("equality operands have different sorts")
        if isinstance(left, BitVecExpr):
            return bitvector_equal(left, expect_bitvec_term(right, "equality operand"))
        return iff(left, expect_bool_term(right, "equality operand"))

    def _require_declared_sort(self, term: TermExpr, declared: SortExpr, role: str) -> None:
        if term_sort(term) != declared:
            raise ProofCheckError(f"{role} does not have its declared sort")

    def _record_query(self, assumptions: list[tuple[str, BoolExpr]]) -> None:
        if self.logic is None:
            raise ProofCheckError("check command used before set-logic")
        assertions = [assertion for frame in self.frames for assertion in frame.assertions]
        assertions.extend(assumptions)
        self.last_query = Query(
            self.logic,
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
    logic: str
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
    logic = atom(fields.get(":logic", []), "proof logic")
    if logic not in {"QF_BOOL", "QF_BV"}:
        raise ProofCheckError(f"satrap-edrat checker does not accept logic `{logic}`")
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
            raise ProofCheckError(f"{logic} proof contains forbidden `{kind}` clause")
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
    return Certificate(logic, variable_count, tuple(premises), tuple(clauses), drat_value.value)


def validate_encoding(script: str, proof: str) -> Certificate:
    certificate = parse_certificate(proof)
    queries = ProofSession().execute_all(SExprReader(script).read_all())
    matches = [
        query
        for query in queries
        if query.logic == certificate.logic and query.premises == certificate.premises
    ]
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
            f"proof clauses do not match the independently reconstructed {certificate.logic} "
            "encoding"
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
