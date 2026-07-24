import unittest

from check_smt_proof import (
    FALSE,
    TRUE,
    BitVecExpr,
    bitvector_compare,
    bitvector_constant,
    bitvector_division,
    bitvector_fold,
    bitvector_negate,
    bitvector_overflow,
    bitvector_shift,
    bitvector_subtract,
)


def unsigned_value(term: BitVecExpr) -> int:
    value = 0
    for index, bit in enumerate(term.bits):
        if bit == TRUE:
            value |= 1 << index
        elif bit != FALSE:
            raise AssertionError(f"expected a constant bit, received {bit!r}")
    return value


def truth_value(expression: tuple[object, ...]) -> bool:
    if expression == TRUE:
        return True
    if expression == FALSE:
        return False
    raise AssertionError(f"expected a Boolean constant, received {expression!r}")


def signed_value(value: int, width: int) -> int:
    sign = 1 << (width - 1)
    return value if value < sign else value - (1 << width)


def signed_division(left: int, right: int) -> int:
    quotient = abs(left) // abs(right)
    return -quotient if (left < 0) != (right < 0) else quotient


class BitBlastSemanticsTests(unittest.TestCase):
    def test_exhaustive_small_arithmetic_comparisons_shifts_and_overflow(self):
        for width in range(1, 5):
            modulus = 1 << width
            mask = modulus - 1
            minimum = -(1 << (width - 1))
            maximum = (1 << (width - 1)) - 1
            for left_value in range(modulus):
                for right_value in range(modulus):
                    left = bitvector_constant(left_value, width)
                    right = bitvector_constant(right_value, width)
                    signed_left = signed_value(left_value, width)
                    signed_right = signed_value(right_value, width)

                    self.assertEqual(
                        unsigned_value(bitvector_fold([left, right], "bvadd")),
                        (left_value + right_value) & mask,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_subtract(left, right)),
                        (left_value - right_value) & mask,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_fold([left, right], "bvmul")),
                        (left_value * right_value) & mask,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_division(left, right, "bvudiv")),
                        mask if right_value == 0 else left_value // right_value,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_division(left, right, "bvurem")),
                        left_value if right_value == 0 else left_value % right_value,
                    )

                    if right_value == 0:
                        signed_quotient = 1 if signed_left < 0 else mask
                        signed_remainder = left_value
                        signed_modulus = left_value
                    else:
                        quotient = signed_division(signed_left, signed_right)
                        remainder = signed_left - quotient * signed_right
                        signed_quotient = quotient & mask
                        signed_remainder = remainder & mask
                        signed_modulus = (signed_left % signed_right) & mask
                    self.assertEqual(
                        unsigned_value(bitvector_division(left, right, "bvsdiv")),
                        signed_quotient,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_division(left, right, "bvsrem")),
                        signed_remainder,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_division(left, right, "bvsmod")),
                        signed_modulus,
                    )

                    for operation, expected in [
                        ("bvult", left_value < right_value),
                        ("bvule", left_value <= right_value),
                        ("bvugt", left_value > right_value),
                        ("bvuge", left_value >= right_value),
                        ("bvslt", signed_left < signed_right),
                        ("bvsle", signed_left <= signed_right),
                        ("bvsgt", signed_left > signed_right),
                        ("bvsge", signed_left >= signed_right),
                    ]:
                        self.assertEqual(
                            truth_value(bitvector_compare(left, right, operation)),
                            expected,
                        )

                    for operation, expected in [
                        ("bvuaddo", left_value + right_value > mask),
                        (
                            "bvsaddo",
                            not minimum <= signed_left + signed_right <= maximum,
                        ),
                        ("bvumulo", left_value * right_value > mask),
                        (
                            "bvsmulo",
                            not minimum <= signed_left * signed_right <= maximum,
                        ),
                        ("bvusubo", left_value < right_value),
                        (
                            "bvssubo",
                            not minimum <= signed_left - signed_right <= maximum,
                        ),
                        (
                            "bvsdivo",
                            signed_left == minimum and signed_right == -1,
                        ),
                    ]:
                        self.assertEqual(
                            truth_value(bitvector_overflow(left, right, operation)),
                            expected,
                        )

                    self.assertEqual(
                        unsigned_value(bitvector_shift(left, right, "bvshl")),
                        (left_value << right_value) & mask,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_shift(left, right, "bvlshr")),
                        left_value >> right_value,
                    )
                    self.assertEqual(
                        unsigned_value(bitvector_shift(left, right, "bvashr")),
                        (signed_left >> right_value) & mask,
                    )

                left = bitvector_constant(left_value, width)
                self.assertEqual(
                    unsigned_value(bitvector_negate(left)),
                    (-left_value) & mask,
                )
                self.assertEqual(
                    truth_value(bitvector_overflow(left, None, "bvnego")),
                    signed_value(left_value, width) == minimum,
                )


if __name__ == "__main__":
    unittest.main()
