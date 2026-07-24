#!/usr/bin/env python3
"""Independently validate a satrap ground SMT eDRAT certificate."""

from __future__ import annotations

import argparse
import itertools
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from fractions import Fraction
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
MAX_INTEGER_PROOF_VARIABLES = 512
MAX_INTEGER_PROOF_WORK = 1_000_000


@dataclass(frozen=True, order=True)
class BitVecExpr:
    """A bit-vector expression whose bits are stored least-significant first."""

    bits: tuple[BoolExpr, ...]


class OrderedSort:
    def __lt__(self, other: object) -> bool:
        if not isinstance(other, OrderedSort):
            return NotImplemented
        return sort_order_key(self) < sort_order_key(other)

    def __le__(self, other: object) -> bool:
        if not isinstance(other, OrderedSort):
            return NotImplemented
        return sort_order_key(self) <= sort_order_key(other)

    def __gt__(self, other: object) -> bool:
        if not isinstance(other, OrderedSort):
            return NotImplemented
        return sort_order_key(self) > sort_order_key(other)

    def __ge__(self, other: object) -> bool:
        if not isinstance(other, OrderedSort):
            return NotImplemented
        return sort_order_key(self) >= sort_order_key(other)


@dataclass(frozen=True)
class BoolSort(OrderedSort):
    pass


@dataclass(frozen=True)
class BitVecSort(OrderedSort):
    width: int


@dataclass(frozen=True)
class UninterpretedSort(OrderedSort):
    name: str


@dataclass(frozen=True)
class ArraySort(OrderedSort):
    index: SortExpr
    element: SortExpr


@dataclass(frozen=True)
class IntSort(OrderedSort):
    pass


@dataclass(frozen=True)
class RealSort(OrderedSort):
    pass


SortExpr: TypeAlias = BoolSort | BitVecSort | UninterpretedSort | ArraySort | IntSort | RealSort
BOOL_SORT = BoolSort()
INT_SORT = IntSort()
REAL_SORT = RealSort()


def sort_order_key(sort: OrderedSort) -> tuple[object, ...]:
    if isinstance(sort, BoolSort):
        return (0,)
    if isinstance(sort, BitVecSort):
        return (1, sort.width)
    if isinstance(sort, UninterpretedSort):
        return (2, sort.name)
    if isinstance(sort, ArraySort):
        return (3, sort_order_key(sort.index), sort_order_key(sort.element))
    if isinstance(sort, IntSort):
        return (4,)
    if isinstance(sort, RealSort):
        return (5,)
    raise ProofCheckError("unknown proof sort")


class OrderedFunction:
    def __lt__(self, other: object) -> bool:
        if not isinstance(other, OrderedFunction):
            return NotImplemented
        return function_order_key(self) < function_order_key(other)

    def __le__(self, other: object) -> bool:
        if not isinstance(other, OrderedFunction):
            return NotImplemented
        return function_order_key(self) <= function_order_key(other)

    def __gt__(self, other: object) -> bool:
        if not isinstance(other, OrderedFunction):
            return NotImplemented
        return function_order_key(self) > function_order_key(other)

    def __ge__(self, other: object) -> bool:
        if not isinstance(other, OrderedFunction):
            return NotImplemented
        return function_order_key(self) >= function_order_key(other)


@dataclass(frozen=True)
class DeclaredFunctionName(OrderedFunction):
    name: str


@dataclass(frozen=True)
class ArraySelectFunction(OrderedFunction):
    array_sort: ArraySort


ProofFunction: TypeAlias = DeclaredFunctionName | ArraySelectFunction


def function_order_key(function: OrderedFunction) -> tuple[object, ...]:
    if isinstance(function, DeclaredFunctionName):
        return (0, function.name)
    if isinstance(function, ArraySelectFunction):
        return (1, sort_order_key(function.array_sort))
    raise ProofCheckError("unknown proof function")


@dataclass(frozen=True, order=True)
class ApplicationExpr:
    function: ProofFunction
    domain: tuple[SortExpr, ...]
    range: SortExpr
    arguments: tuple[object, ...]


@dataclass(frozen=True, order=True)
class UfExpr:
    node: tuple[object, ...]


ArithmeticVariable: TypeAlias = tuple[object, ...]


@dataclass(frozen=True, order=True)
class LinearExpr:
    constant: Fraction
    coefficients: tuple[tuple[ArithmeticVariable, Fraction], ...]


@dataclass(frozen=True, order=True)
class ArithmeticExpr:
    sort: SortExpr
    linear: LinearExpr


TermExpr: TypeAlias = BoolExpr | BitVecExpr | UfExpr | ArithmeticExpr


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
    if isinstance(value, (BitVecExpr, UfExpr, ArithmeticExpr)):
        raise ProofCheckError(f"{role} must have sort Bool")
    return value


def expect_bitvec_term(value: TermExpr, role: str) -> BitVecExpr:
    if not isinstance(value, BitVecExpr):
        raise ProofCheckError(f"{role} must have bit-vector sort")
    return value


def expect_uf_term(value: TermExpr, role: str) -> UfExpr:
    if not isinstance(value, UfExpr):
        raise ProofCheckError(f"{role} must have an abstract sort")
    return value


def expect_arithmetic_term(value: TermExpr, role: str) -> ArithmeticExpr:
    if not isinstance(value, ArithmeticExpr):
        raise ProofCheckError(f"{role} must have sort Int or Real")
    return value


def term_sort(value: TermExpr) -> SortExpr:
    if isinstance(value, BitVecExpr):
        return BitVecSort(len(value.bits))
    if isinstance(value, UfExpr):
        return uf_sort(value)
    if isinstance(value, ArithmeticExpr):
        return value.sort
    return BOOL_SORT


def uf_sort(value: UfExpr) -> SortExpr:
    node = value.node
    if node[0] in {0, 2, 3, 4, 5}:
        sort = node[1]
    elif node[0] == 1:
        application = node[1]
        if not isinstance(application, ApplicationExpr):
            raise ProofCheckError("malformed abstract application")
        sort = application.range
    else:
        raise ProofCheckError("unknown abstract proof term")
    if not isinstance(sort, (UninterpretedSort, ArraySort)):
        raise ProofCheckError("abstract proof term has a lowered result sort")
    return sort


def linear_expression(
    constant: Fraction = Fraction(0),
    coefficients: dict[ArithmeticVariable, Fraction] | None = None,
) -> LinearExpr:
    normalized = tuple(
        sorted(
            (
                (variable, coefficient)
                for variable, coefficient in (coefficients or {}).items()
                if coefficient
            ),
            key=lambda item: item[0],
        )
    )
    return LinearExpr(constant, normalized)


def linear_variable(variable: ArithmeticVariable) -> LinearExpr:
    return linear_expression(coefficients={variable: Fraction(1)})


def linear_scaled(expression: LinearExpr, scale: Fraction) -> LinearExpr:
    return linear_expression(
        expression.constant * scale,
        {variable: coefficient * scale for variable, coefficient in expression.coefficients},
    )


def linear_add_scaled(
    left: LinearExpr,
    right: LinearExpr,
    scale: Fraction,
) -> LinearExpr:
    coefficients = dict(left.coefficients)
    for variable, coefficient in right.coefficients:
        coefficients[variable] = coefficients.get(variable, Fraction(0)) + coefficient * scale
    return linear_expression(left.constant + right.constant * scale, coefficients)


def arithmetic_constant(sort: SortExpr, value: Fraction) -> ArithmeticExpr:
    if not isinstance(sort, (IntSort, RealSort)):
        raise ProofCheckError("arithmetic constant has a non-arithmetic sort")
    return ArithmeticExpr(sort, linear_expression(value))


def arithmetic_variable(sort: SortExpr, variable: ArithmeticVariable) -> ArithmeticExpr:
    if not isinstance(sort, (IntSort, RealSort)):
        raise ProofCheckError("arithmetic variable has a non-arithmetic sort")
    return ArithmeticExpr(sort, linear_variable(variable))


def common_arithmetic_sort(terms: list[ArithmeticExpr]) -> SortExpr:
    if not terms:
        raise ProofCheckError("arithmetic operation has no operands")
    if any(isinstance(term.sort, RealSort) for term in terms):
        return REAL_SORT
    if all(isinstance(term.sort, IntSort) for term in terms):
        return INT_SORT
    raise ProofCheckError("arithmetic operation has a non-arithmetic operand")


def coerce_arithmetic(term: ArithmeticExpr, sort: SortExpr) -> ArithmeticExpr:
    if term.sort == sort:
        return term
    if isinstance(term.sort, IntSort) and isinstance(sort, RealSort):
        return ArithmeticExpr(REAL_SORT, term.linear)
    raise ProofCheckError("cannot implicitly coerce Real to Int")


def arithmetic_add(terms: list[ArithmeticExpr]) -> ArithmeticExpr:
    minimum_arity(terms, 2, "+")
    sort = common_arithmetic_sort(terms)
    result = linear_expression()
    for term in terms:
        result = linear_add_scaled(result, coerce_arithmetic(term, sort).linear, Fraction(1))
    return ArithmeticExpr(sort, result)


def arithmetic_subtract(terms: list[ArithmeticExpr]) -> ArithmeticExpr:
    minimum_arity(terms, 1, "-")
    if len(terms) == 1:
        return ArithmeticExpr(terms[0].sort, linear_scaled(terms[0].linear, Fraction(-1)))
    sort = common_arithmetic_sort(terms)
    result = coerce_arithmetic(terms[0], sort).linear
    for term in terms[1:]:
        result = linear_add_scaled(
            result,
            coerce_arithmetic(term, sort).linear,
            Fraction(-1),
        )
    return ArithmeticExpr(sort, result)


def arithmetic_multiply(terms: list[ArithmeticExpr]) -> ArithmeticExpr:
    minimum_arity(terms, 2, "*")
    sort = common_arithmetic_sort(terms)
    scale = Fraction(1)
    nonconstant: LinearExpr | None = None
    for term in terms:
        expression = coerce_arithmetic(term, sort).linear
        if not expression.coefficients:
            scale *= expression.constant
        elif nonconstant is None:
            nonconstant = expression
        else:
            raise ProofCheckError("nonlinear multiplication is outside the proof boundary")
    result = linear_expression(scale) if nonconstant is None else linear_scaled(nonconstant, scale)
    return ArithmeticExpr(sort, result)


def arithmetic_divide(
    numerator: ArithmeticExpr,
    denominator: ArithmeticExpr,
) -> ArithmeticExpr:
    if denominator.linear.coefficients:
        raise ProofCheckError("division by a nonconstant is outside the proof boundary")
    if denominator.linear.constant == 0:
        raise ProofCheckError("division by zero is outside the proof boundary")
    numerator = coerce_arithmetic(numerator, REAL_SORT)
    return ArithmeticExpr(
        REAL_SORT,
        linear_scaled(numerator.linear, Fraction(1, 1) / denominator.linear.constant),
    )


def arithmetic_comparison(
    left: ArithmeticExpr,
    right: ArithmeticExpr,
    strict: bool,
) -> BoolExpr:
    sort = common_arithmetic_sort([left, right])
    expression = linear_add_scaled(
        coerce_arithmetic(left, sort).linear,
        coerce_arithmetic(right, sort).linear,
        Fraction(-1),
    )
    if not expression.coefficients:
        return bool_constant(expression.constant < 0 if strict else expression.constant <= 0)
    return (2, 5, sort, expression, strict)


def arithmetic_equal(left: ArithmeticExpr, right: ArithmeticExpr) -> BoolExpr:
    return junction(
        [
            arithmetic_comparison(left, right, False),
            arithmetic_comparison(right, left, False),
        ],
        True,
    )


def arithmetic_ite(
    condition: BoolExpr,
    then_term: ArithmeticExpr,
    else_term: ArithmeticExpr,
) -> ArithmeticExpr:
    sort = common_arithmetic_sort([then_term, else_term])
    then_term = coerce_arithmetic(then_term, sort)
    else_term = coerce_arithmetic(else_term, sort)
    if condition == TRUE:
        return then_term
    if condition == FALSE:
        return else_term
    variable: ArithmeticVariable = (
        1,
        sort,
        condition,
        then_term.linear,
        else_term.linear,
    )
    return arithmetic_variable(sort, variable)


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
            or is_numeral_text(expression)
            or parse_decimal_text(expression) is not None
            or expression in {"_", "!", "as", "lambda", "let", "exists", "forall", "match", "par"}
        ):
            return expression
        return quote_symbol(expression)
    return f"({' '.join(render(item) for item in expression)})"


@dataclass
class Frame:
    bound_names: list[str] = field(default_factory=list)
    bound_functions: list[str] = field(default_factory=list)
    bound_sorts: list[str] = field(default_factory=list)
    assertions: list[tuple[str, BoolExpr]] = field(default_factory=list)


@dataclass(frozen=True)
class DeclaredFunction:
    name: str
    domain: tuple[SortExpr, ...]
    range: SortExpr


@dataclass(frozen=True)
class DefinedFunction:
    parameters: tuple[str, ...]
    domain: tuple[SortExpr, ...]
    range: SortExpr
    body: SExpr


FunctionBinding: TypeAlias = DeclaredFunction | DefinedFunction


@dataclass(frozen=True)
class Query:
    logic: str
    premises: tuple[str, ...]
    roots: tuple[BoolExpr, ...]
    has_assumptions: bool


class ProofSession:
    def __init__(self) -> None:
        self.bindings: dict[str, TermExpr] = {}
        self.functions: dict[str, FunctionBinding] = {}
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
            if logic not in {
                "QF_BOOL",
                "QF_BV",
                "QF_UF",
                "QF_UFBV",
                "QF_ABV",
                "QF_AUFBV",
                "QF_IDL",
                "QF_LIA",
                "QF_RDL",
                "QF_LRA",
            }:
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
        elif name == "declare-sort":
            exact_arity(arguments, 2, name)
            sort_name = atom(arguments[0], "sort name")
            if parse_numeral(arguments[1], "sort arity") != 0:
                raise ProofCheckError("proof checker accepts only nullary sorts")
            if self.logic not in {"QF_UF", "QF_UFBV", "QF_AUFBV"}:
                raise ProofCheckError("uninterpreted sort used outside a UF proof logic")
            if sort_name in self.sorts:
                raise ProofCheckError(f"duplicate sort `{sort_name}`")
            self.sorts[sort_name] = UninterpretedSort(sort_name)
            self._declaration_frame().bound_sorts.append(sort_name)
            self._invalidate_query()
        elif name == "define-sort":
            exact_arity(arguments, 3, name)
            self._require_logic()
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
            function_name = atom(arguments[0], "function name")
            domain = tuple(
                self.parse_sort(value) for value in items(arguments[1], "function domain")
            )
            if not domain:
                self._declare(function_name, arguments[2])
            else:
                self._declare_function(
                    function_name,
                    DeclaredFunction(
                        function_name,
                        domain,
                        self.parse_sort(arguments[2]),
                    ),
                )
        elif name == "define-const":
            exact_arity(arguments, 3, name)
            sort = self.parse_sort(arguments[1])
            term = self.parse_term(arguments[2], [])
            self._require_declared_sort(term, sort, "constant definition")
            self._bind(atom(arguments[0], "constant name"), term)
        elif name == "define-fun":
            exact_arity(arguments, 4, name)
            parameters = items(arguments[1], "function parameters")
            function_name = atom(arguments[0], "function name")
            parameter_names = []
            domain = []
            for parameter in parameters:
                fields = items(parameter, "function parameter")
                exact_arity(fields, 2, "function parameter")
                parameter_name = atom(fields[0], "function parameter name")
                if parameter_name in parameter_names:
                    raise ProofCheckError(f"duplicate function parameter `{parameter_name}`")
                parameter_names.append(parameter_name)
                domain.append(self.parse_sort(fields[1]))
            range_sort = self.parse_sort(arguments[2])
            if not domain:
                term = self.parse_term(arguments[3], [])
                self._require_declared_sort(term, range_sort, "function definition")
                self._bind(function_name, term)
            else:
                scope = {
                    parameter: self._placeholder_term(sort, function_name, index)
                    for index, (parameter, sort) in enumerate(
                        zip(parameter_names, domain, strict=True)
                    )
                }
                result = self.parse_term(arguments[3], [scope])
                self._require_declared_sort(
                    result,
                    range_sort,
                    f"definition of `{function_name}`",
                )
                self._declare_function(
                    function_name,
                    DefinedFunction(
                        tuple(parameter_names),
                        tuple(domain),
                        range_sort,
                        arguments[3],
                    ),
                )
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
                for bound_function in frame.bound_functions:
                    self.functions.pop(bound_function, None)
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
                        bound_functions=list(self.functions),
                        bound_sorts=list(self.sorts),
                    )
                ]
            else:
                self.bindings.clear()
                self.functions.clear()
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
                self._require_bitvectors()
                digits = expression[2:]
                if not digits or any(digit not in "01" for digit in digits):
                    raise ProofCheckError("invalid binary bit-vector literal")
                return BitVecExpr(tuple(bool_constant(digit == "1") for digit in reversed(digits)))
            if expression.startswith("#x"):
                self._require_bitvectors()
                digits = expression[2:]
                if not digits:
                    raise ProofCheckError("invalid hexadecimal bit-vector literal")
                try:
                    value = int(digits, 16)
                except ValueError as error:
                    raise ProofCheckError("invalid hexadecimal bit-vector literal") from error
                return bitvector_constant(value, len(digits) * 4)
            if not isinstance(expression, QuotedSymbol) and is_numeral_text(expression):
                self._require_arithmetic()
                return arithmetic_constant(INT_SORT, Fraction(int(expression)))
            decimal = (
                parse_decimal_text(expression) if not isinstance(expression, QuotedSymbol) else None
            )
            if decimal is not None:
                self._require_reals()
                return arithmetic_constant(REAL_SORT, decimal)
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
            if identifier and identifier[0] == "as":
                return self._apply_qualified(identifier, terms)
            return self._apply_indexed(identifier, terms)
        operator = atom(values[0], "term operator")
        arguments = values[1:]
        if operator == "_":
            self._require_bitvectors()
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
            if isinstance(terms[1], ArithmeticExpr) and isinstance(terms[2], ArithmeticExpr):
                return arithmetic_ite(condition, terms[1], terms[2])
            if term_sort(terms[1]) != term_sort(terms[2]):
                raise ProofCheckError("ite branches have different sorts")
            if isinstance(terms[1], BitVecExpr):
                else_term = expect_bitvec_term(terms[2], "ite branch")
                return BitVecExpr(select_bits(condition, terms[1].bits, else_term.bits))
            if isinstance(terms[1], UfExpr):
                else_term = expect_uf_term(terms[2], "ite branch")
                return UfExpr(
                    (
                        2,
                        uf_sort(terms[1]),
                        condition,
                        terms[1],
                        else_term,
                    )
                )
            return ite(condition, terms[1], expect_bool_term(terms[2], "ite branch"))
        if operator in {"+", "-", "*"}:
            self._require_arithmetic()
            arithmetic_terms = [expect_arithmetic_term(term, operator) for term in terms]
            if operator == "+":
                return arithmetic_add(arithmetic_terms)
            if operator == "-":
                return arithmetic_subtract(arithmetic_terms)
            return arithmetic_multiply(arithmetic_terms)
        if operator == "/":
            self._require_reals()
            exact_arity(terms, 2, operator)
            return arithmetic_divide(
                expect_arithmetic_term(terms[0], operator),
                expect_arithmetic_term(terms[1], operator),
            )
        if operator in {"<", "<=", ">", ">="}:
            self._require_arithmetic()
            minimum_arity(terms, 2, operator)
            arithmetic_terms = [expect_arithmetic_term(term, operator) for term in terms]
            comparisons = []
            for left, right in itertools.pairwise(arithmetic_terms):
                if operator in {"<", "<="}:
                    comparisons.append(arithmetic_comparison(left, right, operator == "<"))
                else:
                    comparisons.append(arithmetic_comparison(right, left, operator == ">"))
            return junction(comparisons, True)
        if operator == "select":
            exact_arity(terms, 2, operator)
            array = expect_uf_term(terms[0], "select source")
            array_sort = uf_sort(array)
            if not isinstance(array_sort, ArraySort):
                raise ProofCheckError("select source must have array sort")
            self._require_declared_sort(terms[1], array_sort.index, "select index")
            return self._array_select(array, terms[1])
        if operator == "store":
            exact_arity(terms, 3, operator)
            array = expect_uf_term(terms[0], "store source")
            array_sort = uf_sort(array)
            if not isinstance(array_sort, ArraySort):
                raise ProofCheckError("store source must have array sort")
            self._require_declared_sort(terms[1], array_sort.index, "store index")
            self._require_declared_sort(terms[2], array_sort.element, "store value")
            return UfExpr((4, array_sort, array, terms[1], terms[2]))
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
        if operator in self.functions:
            return self._apply_function(operator, terms, locals_)
        raise ProofCheckError(f"unsupported proof term operator `{operator}`")

    def _declare(self, name: str, sort: SExpr) -> None:
        self._require_logic()
        parsed_sort = self.parse_sort(sort)
        if self.logic == "QF_BOOL" and parsed_sort != BOOL_SORT:
            raise ProofCheckError("QF_BOOL proof contains a non-Boolean declaration")
        if self.logic in {"QF_BV", "QF_ABV"} and isinstance(parsed_sort, UninterpretedSort):
            raise ProofCheckError(f"{self.logic} proof contains an uninterpreted declaration")
        if self.logic == "QF_UF" and isinstance(parsed_sort, (BitVecSort, ArraySort)):
            raise ProofCheckError("QF_UF proof contains a non-UF declaration")
        if self.logic in {"QF_IDL", "QF_LIA"} and not isinstance(parsed_sort, (BoolSort, IntSort)):
            raise ProofCheckError(f"{self.logic} proof contains a declaration outside Bool or Int")
        if self.logic in {"QF_RDL", "QF_LRA"} and not isinstance(parsed_sort, (BoolSort, RealSort)):
            raise ProofCheckError(f"{self.logic} proof contains a declaration outside Bool or Real")
        if parsed_sort == BOOL_SORT:
            term: TermExpr = (2, 0, name)
        elif isinstance(parsed_sort, BitVecSort):
            term = BitVecExpr(tuple((2, 1, name, index) for index in range(parsed_sort.width)))
        elif isinstance(parsed_sort, (IntSort, RealSort)):
            term = arithmetic_variable(parsed_sort, (0, parsed_sort, name))
        else:
            term = UfExpr((0, parsed_sort, name))
        self._bind(name, term)

    def _bind(self, name: str, expression: TermExpr) -> None:
        self._require_logic()
        if name in self.bindings or name in self.functions:
            raise ProofCheckError(f"duplicate term symbol `{name}`")
        self.bindings[name] = expression
        self._declaration_frame().bound_names.append(name)
        self._invalidate_query()

    def _declare_function(self, name: str, function: FunctionBinding) -> None:
        self._require_logic()
        if isinstance(function, DeclaredFunction) and self.logic not in {
            "QF_UF",
            "QF_UFBV",
            "QF_AUFBV",
        }:
            raise ProofCheckError("uninterpreted function used outside a UF proof logic")
        if name in self.bindings or name in self.functions:
            raise ProofCheckError(f"duplicate term symbol `{name}`")
        self.functions[name] = function
        self._declaration_frame().bound_functions.append(name)
        self._invalidate_query()

    def _require_logic(self) -> None:
        if self.logic is None:
            raise ProofCheckError("declaration used before set-logic")

    def _require_bitvectors(self) -> None:
        if self.logic not in {"QF_BV", "QF_UFBV", "QF_ABV", "QF_AUFBV"}:
            raise ProofCheckError("bit-vector term used outside a bit-vector proof logic")

    def _require_arithmetic(self) -> None:
        if self.logic not in {"QF_IDL", "QF_LIA", "QF_RDL", "QF_LRA"}:
            raise ProofCheckError("arithmetic term used outside an arithmetic proof logic")

    def _require_reals(self) -> None:
        if self.logic not in {"QF_RDL", "QF_LRA"}:
            raise ProofCheckError("real term used outside a real proof logic")

    @staticmethod
    def _placeholder_term(
        sort: SortExpr,
        function: str,
        index: int,
    ) -> TermExpr:
        name = f"@proof-parameter:{function}:{index}"
        if sort == BOOL_SORT:
            return (2, 0, name)
        if isinstance(sort, BitVecSort):
            return BitVecExpr(tuple((2, 1, name, bit) for bit in range(sort.width)))
        if isinstance(sort, (UninterpretedSort, ArraySort)):
            return UfExpr((0, sort, name))
        if isinstance(sort, (IntSort, RealSort)):
            return arithmetic_variable(sort, (0, sort, name))
        raise ProofCheckError("defined function parameter has an unsupported sort")

    def parse_sort(self, value: SExpr) -> SortExpr:
        if isinstance(value, str):
            if value == "Bool":
                return BOOL_SORT
            if value == "Int":
                if self.logic not in {"QF_IDL", "QF_LIA"}:
                    raise ProofCheckError("Int sort used outside an integer proof logic")
                return INT_SORT
            if value == "Real":
                if self.logic not in {"QF_RDL", "QF_LRA"}:
                    raise ProofCheckError("Real sort used outside a real proof logic")
                return REAL_SORT
            if value in self.sorts:
                return self.sorts[value]
            raise ProofCheckError(f"unsupported proof sort `{value}`")
        values = items(value, "sort")
        if len(values) == 3 and values[0] == "_" and values[1] == "BitVec":
            width = parse_numeral(values[2], "bit-vector width")
            check_bitvector_width(width)
            if self.logic not in {"QF_BV", "QF_UFBV", "QF_ABV", "QF_AUFBV"}:
                raise ProofCheckError("bit-vector sort used outside a bit-vector proof logic")
            return BitVecSort(width)
        if len(values) == 3 and values[0] == "Array":
            if self.logic not in {"QF_ABV", "QF_AUFBV"}:
                raise ProofCheckError("array sort used outside an array proof logic")
            index = self.parse_sort(values[1])
            element = self.parse_sort(values[2])
            if isinstance(index, ArraySort) or isinstance(element, ArraySort):
                raise ProofCheckError("nested arrays are outside the proof boundary")
            return ArraySort(index, element)
        raise ProofCheckError("proof checker encountered an unsupported sort")

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

    def _apply_qualified(
        self,
        identifier: list[SExpr],
        terms: list[TermExpr],
    ) -> TermExpr:
        exact_arity(identifier, 3, "qualified identifier")
        if atom(identifier[0], "qualified identifier") != "as":
            raise ProofCheckError("unsupported qualified identifier")
        if atom(identifier[1], "qualified operator") != "const":
            raise ProofCheckError("unsupported qualified operator")
        exact_arity(terms, 1, "constant array")
        sort = self.parse_sort(identifier[2])
        if not isinstance(sort, ArraySort):
            raise ProofCheckError("qualified const must name an array sort")
        self._require_declared_sort(terms[0], sort.element, "constant-array value")
        return UfExpr((3, sort, terms[0]))

    @staticmethod
    def _array_select(array: UfExpr, index: TermExpr) -> TermExpr:
        sort = uf_sort(array)
        if not isinstance(sort, ArraySort):
            raise ProofCheckError("array select has a non-array source")
        application = ApplicationExpr(
            ArraySelectFunction(sort),
            (sort, sort.index),
            sort.element,
            (array, index),
        )
        if sort.element == BOOL_SORT:
            return (2, 2, application, 0)
        if isinstance(sort.element, BitVecSort):
            return BitVecExpr(tuple((2, 2, application, bit) for bit in range(sort.element.width)))
        if isinstance(sort.element, UninterpretedSort):
            return UfExpr((1, application))
        raise ProofCheckError("nested array elements are outside the proof boundary")

    def _equivalent(self, left: TermExpr, right: TermExpr) -> BoolExpr:
        if isinstance(left, ArithmeticExpr) and isinstance(right, ArithmeticExpr):
            return arithmetic_equal(left, right)
        if term_sort(left) != term_sort(right):
            raise ProofCheckError("equality operands have different sorts")
        if isinstance(left, BitVecExpr):
            return bitvector_equal(left, expect_bitvec_term(right, "equality operand"))
        if isinstance(left, UfExpr):
            right = expect_uf_term(right, "equality operand")
            return (9, *sorted((left, right)))
        return iff(left, expect_bool_term(right, "equality operand"))

    def _apply_function(
        self,
        name: str,
        terms: list[TermExpr],
        locals_: list[dict[str, TermExpr]],
    ) -> TermExpr:
        function = self.functions[name]
        if len(terms) != len(function.domain):
            raise ProofCheckError(f"function `{name}` expects {len(function.domain)} argument(s)")
        for term, expected in zip(terms, function.domain, strict=True):
            self._require_declared_sort(term, expected, f"argument to `{name}`")
        if isinstance(function, DefinedFunction):
            scope = dict(zip(function.parameters, terms, strict=True))
            result = self.parse_term(function.body, [*locals_, scope])
            self._require_declared_sort(
                result,
                function.range,
                f"result of defined function `{name}`",
            )
            return result
        application = ApplicationExpr(
            DeclaredFunctionName(function.name),
            tuple(function.domain),
            function.range,
            tuple(terms),
        )
        if function.range == BOOL_SORT:
            return (2, 2, application, 0)
        if isinstance(function.range, BitVecSort):
            return BitVecExpr(
                tuple((2, 2, application, index) for index in range(function.range.width))
            )
        if isinstance(function.range, (UninterpretedSort, ArraySort)):
            return UfExpr((1, application))
        raise ProofCheckError(f"function `{name}` has an unsupported result sort")

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
    if not is_numeral_text(text):
        raise ProofCheckError(f"{role} must be a numeral")
    return int(text)


def is_numeral_text(text: str) -> bool:
    return text == "0" or (
        bool(text)
        and text[0] in "123456789"
        and all(character.isascii() and character.isdigit() for character in text)
    )


def parse_decimal_text(text: str) -> Fraction | None:
    if text.count(".") != 1:
        return None
    whole, fractional = text.split(".", 1)
    if not is_numeral_text(whole) or not fractional:
        return None
    if not all(character.isascii() and character.isdigit() for character in fractional):
        return None
    denominator = 10 ** len(fractional)
    return Fraction(int(whole) * denominator + int(fractional), denominator)


class UfLowering:
    def __init__(self, roots: tuple[BoolExpr, ...]):
        self.applications: set[ApplicationExpr] = set()
        self.abstract_terms: dict[SortExpr, set[UfExpr]] = {}
        self.processed_array_selects: set[ApplicationExpr] = set()
        self.lowered: dict[BoolExpr, BoolExpr] = {}
        self.lowered_abstract: dict[UfExpr, tuple[BoolExpr, ...]] = {}
        for root in roots:
            self._collect_bool(root)

    def lower_roots(
        self, roots: tuple[BoolExpr, ...]
    ) -> tuple[tuple[BoolExpr, ...], tuple[BoolExpr, ...]]:
        self.prepare_theory()
        lowered = tuple(self.lower_bool(root) for root in roots)
        return lowered, self.theory_axioms()

    def _collect_bool(self, expression: BoolExpr) -> None:
        kind = expression[0]
        if kind == 2:
            if len(expression) >= 4 and expression[1] == 2:
                application = expression[2]
                if not isinstance(application, ApplicationExpr):
                    raise ProofCheckError("malformed proof application atom")
                self._collect_application(application)
            return
        if kind == 3:
            self._collect_bool(expression[1])
        elif kind in {4, 5}:
            for item in expression[1]:
                self._collect_bool(item)
        elif kind in {6, 7}:
            self._collect_bool(expression[1])
            self._collect_bool(expression[2])
        elif kind == 8:
            self._collect_bool(expression[1])
            self._collect_bool(expression[2])
            self._collect_bool(expression[3])
        elif kind == 9:
            self._collect_abstract(expression[1])
            self._collect_abstract(expression[2])
        elif kind not in {0, 1}:
            raise ProofCheckError(f"unknown raw Boolean proof node {kind}")

    def _collect_term(self, term: TermExpr) -> None:
        if isinstance(term, BitVecExpr):
            for bit in term.bits:
                self._collect_bool(bit)
        elif isinstance(term, UfExpr):
            self._collect_abstract(term)
        else:
            self._collect_bool(term)

    def _collect_application(self, application: ApplicationExpr) -> None:
        if application in self.applications:
            return
        self.applications.add(application)
        for argument in application.arguments:
            if not isinstance(argument, (tuple, BitVecExpr, UfExpr)):
                raise ProofCheckError("malformed proof application argument")
            self._collect_term(argument)
        if isinstance(application.range, (UninterpretedSort, ArraySort)):
            result = UfExpr((1, application))
            self._register_abstract(result)

    def _collect_abstract(self, expression: UfExpr) -> None:
        node = expression.node
        if node[0] == 0:
            self._register_abstract(expression)
        elif node[0] == 1:
            application = node[1]
            if not isinstance(application, ApplicationExpr):
                raise ProofCheckError("malformed abstract application")
            self._collect_application(application)
            self._register_abstract(expression)
        elif node[0] == 2:
            self._collect_bool(node[2])
            self._collect_abstract(node[3])
            self._collect_abstract(node[4])
        elif node[0] == 3:
            self._collect_term(node[2])
            self._register_abstract(expression)
        elif node[0] == 4:
            self._collect_abstract(node[2])
            self._collect_term(node[3])
            self._collect_term(node[4])
            self._register_abstract(expression)
        elif node[0] == 5:
            self._collect_abstract(node[3])
            self._collect_abstract(node[4])
            self._register_abstract(expression)
        else:
            raise ProofCheckError("unknown abstract proof term")

    def _register_abstract(self, expression: UfExpr) -> None:
        if expression.node[0] != 2:
            self.abstract_terms.setdefault(uf_sort(expression), set()).add(expression)

    def lower_bool(self, expression: BoolExpr) -> BoolExpr:
        if expression in self.lowered:
            return self.lowered[expression]
        kind = expression[0]
        if kind in {0, 1, 2}:
            result = expression
        elif kind == 3:
            result = negate(self.lower_bool(expression[1]))
        elif kind in {4, 5}:
            result = junction(
                [self.lower_bool(item) for item in expression[1]],
                kind == 4,
            )
        elif kind == 6:
            result = xor(
                self.lower_bool(expression[1]),
                self.lower_bool(expression[2]),
            )
        elif kind == 7:
            result = iff(
                self.lower_bool(expression[1]),
                self.lower_bool(expression[2]),
            )
        elif kind == 8:
            result = ite(
                self.lower_bool(expression[1]),
                self.lower_bool(expression[2]),
                self.lower_bool(expression[3]),
            )
        elif kind == 9:
            result = self.abstract_equal(expression[1], expression[2])
        else:
            raise ProofCheckError(f"unknown raw Boolean proof node {kind}")
        self.lowered[expression] = result
        return result

    def abstract_bits(self, expression: UfExpr) -> tuple[BoolExpr, ...]:
        if expression in self.lowered_abstract:
            return self.lowered_abstract[expression]
        node = expression.node
        sort = uf_sort(expression)
        if node[0] in {0, 1, 3, 4, 5}:
            count = len(self.abstract_terms.get(sort, set()))
            if count == 0:
                raise ProofCheckError("abstract proof sort has no canonical ground terms")
            width = max(1, (count - 1).bit_length())
            bits = tuple((2, 3, sort, expression, index) for index in range(width))
        elif node[0] == 2:
            condition = self.lower_bool(node[2])
            then_bits = self.abstract_bits(node[3])
            else_bits = self.abstract_bits(node[4])
            if len(then_bits) != len(else_bits):
                raise ProofCheckError("abstract ite branches have inconsistent class encodings")
            bits = tuple(
                ite(condition, then_bit, else_bit)
                for then_bit, else_bit in zip(
                    then_bits,
                    else_bits,
                    strict=True,
                )
            )
        else:
            raise ProofCheckError("unknown abstract proof term")
        self.lowered_abstract[expression] = bits
        return bits

    def abstract_equal(self, left: UfExpr, right: UfExpr) -> BoolExpr:
        if uf_sort(left) != uf_sort(right):
            raise ProofCheckError("abstract equality operands have different sorts")
        return junction(
            [
                iff(left_bit, right_bit)
                for left_bit, right_bit in zip(
                    self.abstract_bits(left),
                    self.abstract_bits(right),
                    strict=True,
                )
            ],
            True,
        )

    def value_equal(self, left: object, right: object) -> BoolExpr:
        if isinstance(left, BitVecExpr) and isinstance(right, BitVecExpr):
            if len(left.bits) != len(right.bits):
                raise ProofCheckError("proof bit-vector values have different widths")
            return junction(
                [
                    iff(self.lower_bool(left_bit), self.lower_bool(right_bit))
                    for left_bit, right_bit in zip(
                        left.bits,
                        right.bits,
                        strict=True,
                    )
                ],
                True,
            )
        if isinstance(left, UfExpr) and isinstance(right, UfExpr):
            return self.abstract_equal(left, right)
        if (
            isinstance(left, tuple)
            and isinstance(right, tuple)
            and not isinstance(left, (BitVecExpr, UfExpr))
            and not isinstance(right, (BitVecExpr, UfExpr))
        ):
            return iff(self.lower_bool(left), self.lower_bool(right))
        raise ProofCheckError("proof values with different sorts were compared")

    def application_result(self, application: ApplicationExpr) -> TermExpr:
        if application.range == BOOL_SORT:
            return (2, 2, application, 0)
        if isinstance(application.range, BitVecSort):
            return BitVecExpr(
                tuple((2, 2, application, index) for index in range(application.range.width))
            )
        if isinstance(application.range, (UninterpretedSort, ArraySort)):
            return UfExpr((1, application))
        raise ProofCheckError("proof application has an unsupported result sort")

    def prepare_theory(self) -> None:
        for array_sort, left, right in self.array_pairs():
            witness = self.array_witness(array_sort, left, right)
            self.array_select_application(left, witness)
            self.array_select_application(right, witness)

        while True:
            pending = sorted(
                application
                for application in self.applications
                if isinstance(application.function, ArraySelectFunction)
                and application not in self.processed_array_selects
            )
            if not pending:
                return
            for application in pending:
                self.processed_array_selects.add(application)
                self.expand_array_select(application)

    def theory_axioms(self) -> tuple[BoolExpr, ...]:
        application_count = len(self.applications)
        abstract_term_count = sum(map(len, self.abstract_terms.values()))
        axioms = {
            *self.array_semantics_axioms(),
            *self.array_extensionality_axioms(),
            *self.congruence_axioms(),
        }
        if (
            len(self.applications) != application_count
            or sum(map(len, self.abstract_terms.values())) != abstract_term_count
        ):
            raise ProofCheckError("array proof theory closure changed after Boolean lowering")
        return tuple(sorted(axioms))

    def array_pairs(self) -> list[tuple[ArraySort, UfExpr, UfExpr]]:
        pairs = []
        for sort in sorted(self.abstract_terms):
            if not isinstance(sort, ArraySort):
                continue
            terms = sorted(self.abstract_terms[sort])
            for left_index, left in enumerate(terms):
                for right in terms[left_index + 1 :]:
                    pairs.append((sort, left, right))
        return pairs

    def array_witness(
        self,
        array_sort: ArraySort,
        left: UfExpr,
        right: UfExpr,
    ) -> TermExpr:
        index_sort = array_sort.index
        if index_sort == BOOL_SORT:
            return (2, 4, array_sort, left, right, 0)
        if isinstance(index_sort, BitVecSort):
            return BitVecExpr(
                tuple((2, 4, array_sort, left, right, index) for index in range(index_sort.width))
            )
        if isinstance(index_sort, UninterpretedSort):
            witness = UfExpr((5, index_sort, array_sort, left, right))
            self._register_abstract(witness)
            return witness
        raise ProofCheckError("nested array indices are outside the proof boundary")

    @staticmethod
    def value_sort(value: TermExpr) -> SortExpr:
        return term_sort(value)

    def array_select_application(
        self,
        array: UfExpr,
        index: TermExpr,
    ) -> ApplicationExpr:
        array_sort = uf_sort(array)
        if not isinstance(array_sort, ArraySort):
            raise ProofCheckError("array select has a non-array source")
        if self.value_sort(index) != array_sort.index:
            raise ProofCheckError("array select index has an inconsistent proof sort")
        if isinstance(array_sort.element, ArraySort):
            raise ProofCheckError("nested array elements are outside the proof boundary")
        application = ApplicationExpr(
            ArraySelectFunction(array_sort),
            (array_sort, array_sort.index),
            array_sort.element,
            (array, index),
        )
        self._collect_application(application)
        return application

    def expand_array_select(self, application: ApplicationExpr) -> None:
        if not isinstance(application.function, ArraySelectFunction):
            return
        if len(application.arguments) != 2 or not isinstance(application.arguments[0], UfExpr):
            raise ProofCheckError("canonical array select has malformed arguments")
        array = application.arguments[0]
        index = application.arguments[1]
        if not isinstance(index, (tuple, BitVecExpr, UfExpr)):
            raise ProofCheckError("canonical array select has a malformed index")
        node = array.node
        if node[0] == 4:
            self.array_select_application(node[2], index)
        elif node[0] == 2:
            self.array_select_application(node[3], index)
            self.array_select_application(node[4], index)

    def value_ite(
        self,
        condition: BoolExpr,
        then_value: TermExpr,
        else_value: TermExpr,
    ) -> TermExpr:
        if self.value_sort(then_value) != self.value_sort(else_value):
            raise ProofCheckError("proof ite values have inconsistent sorts")
        condition = self.lower_bool(condition)
        if isinstance(then_value, BitVecExpr) and isinstance(else_value, BitVecExpr):
            return BitVecExpr(
                tuple(
                    ite(
                        condition,
                        self.lower_bool(then_bit),
                        self.lower_bool(else_bit),
                    )
                    for then_bit, else_bit in zip(
                        then_value.bits,
                        else_value.bits,
                        strict=True,
                    )
                )
            )
        if isinstance(then_value, UfExpr) and isinstance(else_value, UfExpr):
            return UfExpr(
                (
                    2,
                    uf_sort(then_value),
                    condition,
                    then_value,
                    else_value,
                )
            )
        if isinstance(then_value, tuple) and isinstance(else_value, tuple):
            return ite(
                condition,
                self.lower_bool(then_value),
                self.lower_bool(else_value),
            )
        raise ProofCheckError("proof ite values have inconsistent representations")

    def array_semantics_axioms(self) -> set[BoolExpr]:
        axioms = set()
        applications = sorted(
            application
            for application in self.applications
            if isinstance(application.function, ArraySelectFunction)
        )
        for application in applications:
            if len(application.arguments) != 2 or not isinstance(application.arguments[0], UfExpr):
                raise ProofCheckError("canonical array select has malformed arguments")
            array = application.arguments[0]
            index = application.arguments[1]
            if not isinstance(index, (tuple, BitVecExpr, UfExpr)):
                raise ProofCheckError("canonical array select has a malformed index")
            node = array.node
            semantic_value: TermExpr | None = None
            if node[0] == 3:
                semantic_value = node[2]
            elif node[0] == 4:
                fallback = self.application_result(self.array_select_application(node[2], index))
                same_index = self.value_equal(node[3], index)
                semantic_value = self.value_ite(same_index, node[4], fallback)
            elif node[0] == 2:
                then_value = self.application_result(self.array_select_application(node[3], index))
                else_value = self.application_result(self.array_select_application(node[4], index))
                semantic_value = self.value_ite(node[2], then_value, else_value)
            if semantic_value is not None:
                axioms.add(
                    self.value_equal(
                        self.application_result(application),
                        semantic_value,
                    )
                )
        return axioms

    def array_extensionality_axioms(self) -> set[BoolExpr]:
        axioms = set()
        for array_sort, left, right in self.array_pairs():
            witness = self.array_witness(array_sort, left, right)
            left_value = self.application_result(self.array_select_application(left, witness))
            right_value = self.application_result(self.array_select_application(right, witness))
            arrays_equal = self.abstract_equal(left, right)
            values_differ = negate(self.value_equal(left_value, right_value))
            axioms.add(junction([arrays_equal, values_differ], False))
        return axioms

    def congruence_axioms(self) -> tuple[BoolExpr, ...]:
        applications = sorted(self.applications)
        axioms: set[BoolExpr] = set()
        for left_index, left in enumerate(applications):
            for right in applications[left_index + 1 :]:
                if left.function != right.function:
                    continue
                if left.domain != right.domain or left.range != right.range:
                    raise ProofCheckError("proof function name has inconsistent signatures")
                arguments_equal = junction(
                    [
                        self.value_equal(left_argument, right_argument)
                        for left_argument, right_argument in zip(
                            left.arguments,
                            right.arguments,
                            strict=True,
                        )
                    ],
                    True,
                )
                results_equal = self.value_equal(
                    self.application_result(left),
                    self.application_result(right),
                )
                axioms.add(junction([negate(arguments_equal), results_equal], False))
        return tuple(sorted(axioms))


class CnfEncoder:
    def __init__(self) -> None:
        self.literals: dict[BoolExpr, int] = {}
        self.truth_literal: int | None = None
        self.variable_count = 0
        self.clauses: list[Clause] = []

    def build(
        self,
        roots: tuple[BoolExpr, ...],
        theory_axioms: tuple[BoolExpr, ...] = (),
    ) -> list[Clause]:
        for root in roots:
            self.add_clause("formula", [self.encode(root)])
        for axiom in theory_axioms:
            self.add_clause("theory", [self.encode(axiom)])
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
class LinearConstraint:
    sort: SortExpr
    expression: LinearExpr
    strict: bool


class ArithmeticProblem:
    def __init__(self, sort: SortExpr, roots: tuple[BoolExpr, ...]):
        if not isinstance(sort, (IntSort, RealSort)):
            raise ProofCheckError("arithmetic problem has a non-arithmetic sort")
        self.sort = sort
        self.predicates: dict[BoolExpr, LinearConstraint] = {}
        self.ites: set[ArithmeticVariable] = set()
        self.required: set[BoolExpr] = set()
        visited_boolean: set[BoolExpr] = set()
        visited_variables: set[ArithmeticVariable] = set()
        for root in roots:
            self._collect_bool(root, visited_boolean, visited_variables)
        self.required.update(self.predicates)

    def _collect_bool(
        self,
        expression: BoolExpr,
        visited_boolean: set[BoolExpr],
        visited_variables: set[ArithmeticVariable],
    ) -> None:
        if expression in visited_boolean:
            return
        visited_boolean.add(expression)
        kind = expression[0]
        if kind in {0, 1}:
            return
        if kind == 2:
            if len(expression) >= 2 and expression[1] == 5:
                if len(expression) != 5:
                    raise ProofCheckError("malformed arithmetic proof atom")
                _, _, sort, linear, strict = expression
                if sort != self.sort or not isinstance(linear, LinearExpr):
                    raise ProofCheckError("arithmetic proof contains a predicate of the wrong sort")
                if not isinstance(strict, bool):
                    raise ProofCheckError("arithmetic proof predicate has a malformed strictness")
                self.predicates[expression] = LinearConstraint(sort, linear, strict)
                self._collect_linear(linear, visited_boolean, visited_variables)
            return
        if kind == 3:
            self._collect_bool(expression[1], visited_boolean, visited_variables)
            return
        if kind in {4, 5}:
            for item in expression[1]:
                self._collect_bool(item, visited_boolean, visited_variables)
            return
        if kind in {6, 7}:
            self._collect_bool(expression[1], visited_boolean, visited_variables)
            self._collect_bool(expression[2], visited_boolean, visited_variables)
            return
        if kind == 8:
            self._collect_bool(expression[1], visited_boolean, visited_variables)
            self._collect_bool(expression[2], visited_boolean, visited_variables)
            self._collect_bool(expression[3], visited_boolean, visited_variables)
            return
        if kind == 9:
            raise ProofCheckError("arithmetic proof contains an unlowered theory equality")
        raise ProofCheckError(f"unknown canonical Boolean node {kind}")

    def _collect_linear(
        self,
        expression: LinearExpr,
        visited_boolean: set[BoolExpr],
        visited_variables: set[ArithmeticVariable],
    ) -> None:
        for variable, _ in expression.coefficients:
            if variable in visited_variables:
                continue
            visited_variables.add(variable)
            if not variable:
                raise ProofCheckError("malformed arithmetic proof variable")
            kind = variable[0]
            if kind == 0:
                if len(variable) != 3 or variable[1] != self.sort:
                    raise ProofCheckError("arithmetic proof contains a variable of the wrong sort")
                continue
            if kind != 1 or len(variable) != 5:
                raise ProofCheckError("malformed arithmetic proof variable")
            _, sort, condition, then_expression, else_expression = variable
            if (
                sort != self.sort
                or not isinstance(then_expression, LinearExpr)
                or not isinstance(else_expression, LinearExpr)
            ):
                raise ProofCheckError("arithmetic proof contains an ite of the wrong sort")
            self.ites.add(variable)
            self.required.add(condition)
            self._collect_bool(condition, visited_boolean, visited_variables)
            self._collect_linear(then_expression, visited_boolean, visited_variables)
            self._collect_linear(else_expression, visited_boolean, visited_variables)

    def constraints(
        self,
        assignment: dict[BoolExpr, bool],
    ) -> list[LinearConstraint]:
        constraints = []
        for term, predicate in sorted(self.predicates.items()):
            if term not in assignment:
                raise ProofCheckError("arithmetic predicate has no Boolean assignment")
            positive = assignment[term]
            expression = (
                predicate.expression
                if positive
                else linear_scaled(predicate.expression, Fraction(-1))
            )
            constraints.append(
                LinearConstraint(self.sort, expression, predicate.strict == positive)
            )
        for variable in sorted(self.ites):
            _, _, condition, then_expression, else_expression = variable
            if condition not in assignment:
                raise ProofCheckError("arithmetic ite condition has no Boolean assignment")
            selected = then_expression if assignment[condition] else else_expression
            forward = linear_add_scaled(
                linear_variable(variable),
                selected,
                Fraction(-1),
            )
            constraints.append(LinearConstraint(self.sort, forward, False))
            constraints.append(
                LinearConstraint(
                    self.sort,
                    linear_scaled(forward, Fraction(-1)),
                    False,
                )
            )
        return constraints


@dataclass(frozen=True, order=True)
class IntegerExpr:
    constant: int
    coefficients: tuple[tuple[ArithmeticVariable, int], ...]


def integer_expression(
    constant: int = 0,
    coefficients: dict[ArithmeticVariable, int] | None = None,
) -> IntegerExpr:
    return IntegerExpr(
        constant,
        tuple(
            sorted(
                (
                    (variable, coefficient)
                    for variable, coefficient in (coefficients or {}).items()
                    if coefficient
                ),
                key=lambda item: item[0],
            )
        ),
    )


def integer_from_linear(expression: LinearExpr) -> IntegerExpr | None:
    if expression.constant.denominator != 1 or any(
        coefficient.denominator != 1 for _, coefficient in expression.coefficients
    ):
        return None
    return integer_expression(
        expression.constant.numerator,
        {variable: coefficient.numerator for variable, coefficient in expression.coefficients},
    )


def integer_coefficient(expression: IntegerExpr, variable: ArithmeticVariable) -> int:
    return dict(expression.coefficients).get(variable, 0)


def integer_without(expression: IntegerExpr, variable: ArithmeticVariable) -> IntegerExpr:
    return integer_expression(
        expression.constant,
        {
            candidate: coefficient
            for candidate, coefficient in expression.coefficients
            if candidate != variable
        },
    )


def integer_scaled(expression: IntegerExpr, scale: int) -> IntegerExpr:
    return integer_expression(
        expression.constant * scale,
        {variable: coefficient * scale for variable, coefficient in expression.coefficients},
    )


def integer_add_scaled(left: IntegerExpr, right: IntegerExpr, scale: int) -> IntegerExpr:
    coefficients = dict(left.coefficients)
    for variable, coefficient in right.coefficients:
        coefficients[variable] = coefficients.get(variable, 0) + coefficient * scale
    return integer_expression(left.constant + right.constant * scale, coefficients)


def integer_substitute(
    expression: IntegerExpr,
    variable: ArithmeticVariable,
    value: IntegerExpr,
) -> IntegerExpr:
    coefficient = integer_coefficient(expression, variable)
    return integer_add_scaled(integer_without(expression, variable), value, coefficient)


@dataclass(frozen=True, order=True)
class IntegerInequality:
    expression: IntegerExpr


@dataclass(frozen=True, order=True)
class DivisibilityConstraint:
    modulus: int
    expression: IntegerExpr


@dataclass(frozen=True)
class IntegerProblem:
    inequalities: tuple[IntegerInequality, ...] = ()
    divisibilities: tuple[DivisibilityConstraint, ...] = ()


def substitute_integer_problem(
    problem: IntegerProblem,
    variable: ArithmeticVariable,
    value: IntegerExpr,
) -> IntegerProblem:
    return IntegerProblem(
        tuple(
            IntegerInequality(integer_substitute(constraint.expression, variable, value))
            for constraint in problem.inequalities
        ),
        tuple(
            DivisibilityConstraint(
                constraint.modulus,
                integer_substitute(constraint.expression, variable, value),
            )
            for constraint in problem.divisibilities
        ),
    )


def integer_problem_mentions(problem: IntegerProblem, variable: ArithmeticVariable) -> bool:
    return any(
        integer_coefficient(constraint.expression, variable) for constraint in problem.inequalities
    ) or any(
        integer_coefficient(constraint.expression, variable)
        for constraint in problem.divisibilities
    )


@dataclass(frozen=True)
class CooperElimination:
    normalized: IntegerProblem
    period: int
    lower_bases: tuple[IntegerExpr, ...]
    upper_bases: tuple[IntegerExpr, ...]


@dataclass
class IntegerProofBudget:
    remaining: int = MAX_INTEGER_PROOF_WORK

    def spend(self, amount: int) -> None:
        if amount < 0 or amount > self.remaining:
            raise ProofCheckError(
                "linear-integer proof exceeded its deterministic work limit of "
                f"{MAX_INTEGER_PROOF_WORK} steps"
            )
        self.remaining -= amount


def integer_linear_constraints_unsat(constraints: list[LinearConstraint]) -> bool:
    inequalities = []
    for constraint in constraints:
        if constraint.sort != INT_SORT:
            raise ProofCheckError("linear-integer proof contains a constraint of the wrong sort")
        expression = integer_from_linear(constraint.expression)
        if expression is None:
            raise ProofCheckError("linear-integer proof contains a non-integral affine expression")
        if not constraint.strict:
            expression = integer_expression(
                expression.constant - 1,
                dict(expression.coefficients),
            )
        inequalities.append(IntegerInequality(expression))
    problem = IntegerProblem(tuple(inequalities))
    variables = tuple(
        sorted(
            {
                variable
                for constraint in problem.inequalities
                for variable, _ in constraint.expression.coefficients
            }
        )
    )
    if len(variables) > MAX_INTEGER_PROOF_VARIABLES:
        raise ProofCheckError(
            f"linear-integer proof has {len(variables)} variables; "
            f"the deterministic proof limit is {MAX_INTEGER_PROOF_VARIABLES}"
        )
    return not integer_problem_satisfiable(problem, variables, IntegerProofBudget())


def integer_problem_satisfiable(
    problem: IntegerProblem,
    variables: tuple[ArithmeticVariable, ...],
    budget: IntegerProofBudget,
) -> bool:
    budget.spend(1)
    problem = simplify_integer_problem(problem, budget)
    if problem is None:
        return False
    if not variables:
        return True
    variable = min(
        variables,
        key=lambda candidate: (cooper_elimination_cost(problem, candidate), candidate),
    )
    remaining = tuple(candidate for candidate in variables if candidate != variable)
    if not integer_problem_mentions(problem, variable):
        return integer_problem_satisfiable(problem, remaining, budget)

    elimination = normalize_cooper_variable(problem, variable, budget)
    if elimination.lower_bases:
        candidates = (
            integer_expression(base.constant + offset, dict(base.coefficients))
            for base in elimination.lower_bases
            for offset in range(1, elimination.period + 1)
        )
    elif elimination.upper_bases:
        candidates = (
            integer_expression(base.constant - offset, dict(base.coefficients))
            for base in elimination.upper_bases
            for offset in range(1, elimination.period + 1)
        )
    else:
        candidates = (integer_expression(value) for value in range(elimination.period))
    for candidate in candidates:
        budget.spend(1)
        reduced = substitute_integer_problem(elimination.normalized, variable, candidate)
        if integer_problem_satisfiable(reduced, remaining, budget):
            return True
    return False


def cooper_elimination_cost(problem: IntegerProblem, variable: ArithmeticVariable) -> int:
    scale = 1
    lower_count = 0
    upper_count = 0
    mentioned = False
    for constraint in problem.inequalities:
        coefficient = integer_coefficient(constraint.expression, variable)
        if coefficient == 0:
            continue
        mentioned = True
        scale = integer_lcm(scale, abs(coefficient))
        if coefficient < 0:
            lower_count += 1
        else:
            upper_count += 1
    for constraint in problem.divisibilities:
        coefficient = integer_coefficient(constraint.expression, variable)
        if coefficient == 0:
            continue
        mentioned = True
        scale = integer_lcm(scale, abs(coefficient))
    if not mentioned:
        return 0

    period = scale
    for constraint in problem.divisibilities:
        coefficient = integer_coefficient(constraint.expression, variable)
        if coefficient:
            transformed_modulus = (scale // abs(coefficient)) * abs(constraint.modulus)
            period = integer_lcm(period, transformed_modulus)
    candidate_count = lower_count or upper_count or 1
    return period * candidate_count


def normalize_cooper_variable(
    problem: IntegerProblem,
    variable: ArithmeticVariable,
    budget: IntegerProofBudget,
) -> CooperElimination:
    budget.spend(len(problem.inequalities) + len(problem.divisibilities))
    coefficients = [
        coefficient
        for constraint in (*problem.inequalities, *problem.divisibilities)
        if (coefficient := integer_coefficient(constraint.expression, variable))
    ]
    if not coefficients:
        raise ProofCheckError("linear-integer proof tried to eliminate an absent variable")
    scale = 1
    for coefficient in coefficients:
        scale = integer_lcm(scale, abs(coefficient))

    inequalities = []
    divisibilities = []
    lower_bases = []
    upper_bases = []
    for constraint in problem.inequalities:
        coefficient = integer_coefficient(constraint.expression, variable)
        if coefficient == 0:
            inequalities.append(constraint)
            continue
        factor = scale // abs(coefficient)
        expression = integer_scaled(integer_without(constraint.expression, variable), factor)
        coefficients_by_variable = dict(expression.coefficients)
        coefficients_by_variable[variable] = 1 if coefficient > 0 else -1
        expression = integer_expression(expression.constant, coefficients_by_variable)
        if coefficient > 0:
            upper_bases.append(integer_scaled(integer_without(expression, variable), -1))
        else:
            lower_bases.append(integer_without(expression, variable))
        inequalities.append(IntegerInequality(expression))
    for constraint in problem.divisibilities:
        coefficient = integer_coefficient(constraint.expression, variable)
        if coefficient == 0:
            divisibilities.append(constraint)
            continue
        factor = scale // abs(coefficient)
        expression = integer_scaled(integer_without(constraint.expression, variable), factor)
        coefficients_by_variable = dict(expression.coefficients)
        coefficients_by_variable[variable] = 1 if coefficient > 0 else -1
        divisibilities.append(
            DivisibilityConstraint(
                constraint.modulus * factor,
                integer_expression(expression.constant, coefficients_by_variable),
            )
        )
    divisibilities.append(
        DivisibilityConstraint(
            scale,
            integer_expression(coefficients={variable: 1}),
        )
    )
    period = 1
    for constraint in divisibilities:
        period = integer_lcm(period, constraint.modulus)
    return CooperElimination(
        IntegerProblem(tuple(inequalities), tuple(divisibilities)),
        period,
        tuple(lower_bases),
        tuple(upper_bases),
    )


def simplify_integer_problem(
    problem: IntegerProblem,
    budget: IntegerProofBudget,
) -> IntegerProblem | None:
    budget.spend(len(problem.inequalities) + len(problem.divisibilities))
    inequalities = set()
    for constraint in problem.inequalities:
        expression = constraint.expression
        coefficient_gcd = 0
        for _, coefficient in expression.coefficients:
            coefficient_gcd = integer_gcd(coefficient_gcd, coefficient)
        if coefficient_gcd > 1:
            expression = integer_expression(
                expression.constant // coefficient_gcd,
                {
                    variable: coefficient // coefficient_gcd
                    for variable, coefficient in expression.coefficients
                },
            )
            constraint = IntegerInequality(expression)
        if not expression.coefficients:
            if expression.constant >= 0:
                return None
        else:
            inequalities.add(constraint)

    divisibilities = set()
    for constraint in problem.divisibilities:
        modulus = abs(constraint.modulus)
        if modulus == 0:
            raise ProofCheckError("linear-integer proof produced a zero divisibility modulus")
        expression = constraint.expression
        common_gcd = modulus
        for _, coefficient in expression.coefficients:
            common_gcd = integer_gcd(common_gcd, coefficient)
        if expression.constant % common_gcd:
            return None
        if common_gcd > 1:
            modulus //= common_gcd
            expression = integer_expression(
                expression.constant // common_gcd,
                {
                    variable: coefficient // common_gcd
                    for variable, coefficient in expression.coefficients
                },
            )
        if modulus == 1:
            continue
        normalized = DivisibilityConstraint(modulus, expression)
        if not expression.coefficients:
            if expression.constant % modulus:
                return None
        else:
            divisibilities.add(normalized)
    return IntegerProblem(tuple(sorted(inequalities)), tuple(sorted(divisibilities)))


def integer_gcd(left: int, right: int) -> int:
    left = abs(left)
    right = abs(right)
    while right:
        left, right = right, left % right
    return left


def integer_lcm(left: int, right: int) -> int:
    if left == 0 or right == 0:
        return 0
    return abs((left // integer_gcd(left, right)) * right)


def real_linear_constraints_unsat(constraints: list[LinearConstraint]) -> bool:
    simplified = simplify_real_constraints(constraints)
    if simplified is None:
        return True
    constraints = simplified
    variables = sorted(
        {
            variable
            for constraint in constraints
            for variable, _ in constraint.expression.coefficients
        }
    )

    for variable in variables:
        independent = []
        upper = []
        lower = []
        for constraint in constraints:
            if constraint.sort != REAL_SORT:
                raise ProofCheckError("linear-real proof contains a constraint of the wrong sort")
            coefficient = dict(constraint.expression.coefficients).get(variable, Fraction(0))
            if coefficient == 0:
                independent.append(constraint)
            elif coefficient > 0:
                upper.append((constraint, coefficient))
            else:
                lower.append((constraint, coefficient))
        for upper_constraint, upper_coefficient in upper:
            for lower_constraint, lower_coefficient in lower:
                expression = linear_add_scaled(
                    linear_scaled(upper_constraint.expression, -lower_coefficient),
                    lower_constraint.expression,
                    upper_coefficient,
                )
                independent.append(
                    LinearConstraint(
                        REAL_SORT,
                        expression,
                        upper_constraint.strict or lower_constraint.strict,
                    )
                )
        simplified = simplify_real_constraints(independent)
        if simplified is None:
            return True
        constraints = simplified
    return False


def simplify_real_constraints(
    constraints: list[LinearConstraint],
) -> list[LinearConstraint] | None:
    seen = set()
    result = []
    for constraint in constraints:
        if constraint.sort != REAL_SORT:
            raise ProofCheckError("linear-real proof contains a constraint of the wrong sort")
        if not constraint.expression.coefficients:
            satisfied = (
                constraint.expression.constant < 0
                if constraint.strict
                else constraint.expression.constant <= 0
            )
            if not satisfied:
                return None
        elif constraint not in seen:
            seen.add(constraint)
            result.append(constraint)
    return result


@dataclass(frozen=True)
class DifferenceEdge:
    source: int
    target: int
    weight: Fraction
    epsilon: int


def difference_constraints_unsat(
    constraints: list[LinearConstraint],
    expected_sort: SortExpr,
) -> bool:
    variables = sorted(
        {
            variable
            for constraint in constraints
            for variable, _ in constraint.expression.coefficients
        }
    )
    variable_indices = {variable: index for index, variable in enumerate(variables)}
    zero = len(variable_indices)
    edges = []
    for constraint in constraints:
        if constraint.sort != expected_sort:
            raise ProofCheckError("difference-logic constraint has an inconsistent sort")
        if not constraint.expression.coefficients:
            satisfied = (
                constraint.expression.constant < 0
                if constraint.strict
                else constraint.expression.constant <= 0
            )
            if not satisfied:
                return True
            continue
        edges.append(difference_edge(constraint, expected_sort, variable_indices, zero))

    vertex_count = len(variable_indices) + 1
    distances = [(Fraction(0), 0) for _ in range(vertex_count)]
    for iteration in range(vertex_count):
        changed = False
        for edge in edges:
            candidate = (
                distances[edge.source][0] + edge.weight,
                distances[edge.source][1] + edge.epsilon,
            )
            if candidate < distances[edge.target]:
                distances[edge.target] = candidate
                changed = True
        if not changed:
            return False
        if iteration + 1 == vertex_count:
            return True
    return False


def difference_edge(
    constraint: LinearConstraint,
    expected_sort: SortExpr,
    variable_indices: dict[ArithmeticVariable, int],
    zero: int,
) -> DifferenceEdge:
    coefficients = list(constraint.expression.coefficients)
    if len(coefficients) == 1 and coefficients[0][1] > 0:
        positive = variable_indices[coefficients[0][0]]
        negative = zero
        scale = coefficients[0][1]
    elif len(coefficients) == 1 and coefficients[0][1] < 0:
        positive = zero
        negative = variable_indices[coefficients[0][0]]
        scale = -coefficients[0][1]
    elif (
        len(coefficients) == 2
        and coefficients[0][1] > 0
        and coefficients[0][1] == -coefficients[1][1]
    ):
        positive = variable_indices[coefficients[0][0]]
        negative = variable_indices[coefficients[1][0]]
        scale = coefficients[0][1]
    elif (
        len(coefficients) == 2
        and coefficients[1][1] > 0
        and coefficients[1][1] == -coefficients[0][1]
    ):
        positive = variable_indices[coefficients[1][0]]
        negative = variable_indices[coefficients[0][0]]
        scale = coefficients[1][1]
    else:
        raise ProofCheckError("proof predicate is outside the declared difference-logic fragment")

    bound = -constraint.expression.constant / scale
    if isinstance(expected_sort, IntSort):
        integer_bound = fraction_ceil(bound) - 1 if constraint.strict else fraction_floor(bound)
        weight = Fraction(integer_bound)
        epsilon = 0
    elif isinstance(expected_sort, RealSort):
        weight = bound
        epsilon = -1 if constraint.strict else 0
    else:
        raise ProofCheckError("difference-logic proof selected a non-arithmetic sort")
    return DifferenceEdge(negative, positive, weight, epsilon)


def fraction_floor(value: Fraction) -> int:
    return value.numerator // value.denominator


def fraction_ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def normalized_clause(literals: tuple[int, ...]) -> tuple[int, ...] | None:
    normalized = tuple(sorted(set(literals), key=literal_index))
    for left, right in itertools.pairwise(normalized):
        if abs(left) == abs(right):
            return None
    return normalized


def validate_arithmetic_encoding(
    certificate: Certificate,
    roots: tuple[BoolExpr, ...],
) -> None:
    sort = INT_SORT if certificate.logic in {"QF_IDL", "QF_LIA"} else REAL_SORT
    problem = ArithmeticProblem(sort, roots)
    encoder = CnfEncoder()
    encoder.build(roots)
    for expression in sorted(problem.required):
        encoder.encode(expression)
    expected_prefix = tuple(encoder.clauses)
    if encoder.variable_count != certificate.variable_count:
        raise ProofCheckError(
            "proof variable count does not match the independently reconstructed encoding"
        )
    if certificate.clauses[: len(expected_prefix)] != expected_prefix:
        raise ProofCheckError(
            f"proof clauses do not match the independently reconstructed {certificate.logic} "
            "encoding prefix"
        )

    theory_clauses = certificate.clauses[len(expected_prefix) :]
    required_literals = {
        expression: encoder.encode(expression) for expression in sorted(problem.required)
    }
    required_variables = {abs(literal) for literal in required_literals.values()}
    for kind, literals in theory_clauses:
        if kind != "theory":
            raise ProofCheckError(
                "arithmetic proof has a non-theory clause after its encoding prefix"
            )
        if normalized_clause(literals) != literals:
            raise ProofCheckError("arithmetic theory clause is not canonically normalized")
        if any(abs(literal) > certificate.variable_count for literal in literals):
            raise ProofCheckError("arithmetic theory clause uses an out-of-range variable")
        if {abs(literal) for literal in literals} != required_variables:
            raise ProofCheckError(
                "arithmetic theory clause does not block a complete required assignment"
            )
        blocked_variables = {abs(literal): literal < 0 for literal in literals}
        assignment = {
            expression: (
                blocked_variables[abs(literal)]
                if literal > 0
                else not blocked_variables[abs(literal)]
            )
            for expression, literal in required_literals.items()
        }
        constraints = problem.constraints(assignment)
        if certificate.logic == "QF_LIA":
            unsatisfiable = integer_linear_constraints_unsat(constraints)
        elif certificate.logic == "QF_LRA":
            unsatisfiable = real_linear_constraints_unsat(constraints)
        else:
            unsatisfiable = difference_constraints_unsat(constraints, sort)
        if not unsatisfiable:
            raise ProofCheckError("arithmetic theory clause blocks a satisfiable theory assignment")


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
    if logic not in {
        "QF_BOOL",
        "QF_BV",
        "QF_UF",
        "QF_UFBV",
        "QF_ABV",
        "QF_AUFBV",
        "QF_IDL",
        "QF_LIA",
        "QF_RDL",
        "QF_LRA",
    }:
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
        allowed_kinds = (
            {"formula", "encoding", "theory"}
            if logic
            in {
                "QF_UF",
                "QF_UFBV",
                "QF_ABV",
                "QF_AUFBV",
                "QF_IDL",
                "QF_LIA",
                "QF_RDL",
                "QF_LRA",
            }
            else {"formula", "encoding"}
        )
        if kind not in allowed_kinds:
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
    raw_roots = next(iter(expected_roots))
    if certificate.logic in {"QF_UF", "QF_UFBV", "QF_ABV", "QF_AUFBV"}:
        roots, theory_axioms = UfLowering(raw_roots).lower_roots(raw_roots)
    else:
        roots = raw_roots
        theory_axioms = ()
    if certificate.logic in {"QF_IDL", "QF_LIA", "QF_RDL", "QF_LRA"}:
        validate_arithmetic_encoding(certificate, roots)
        return certificate
    encoder = CnfEncoder()
    expected_clauses = tuple(encoder.build(roots, theory_axioms))
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
