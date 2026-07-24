use super::term::{Sort, TermError, TermId, TermStore};

const MAX_BITVECTOR_WIDTH: u32 = 1_048_576;
const MAX_QUADRATIC_LOWERING_WORK: u64 = 16_000_000;

impl TermStore {
    pub(crate) fn fresh_bitvec(&mut self, width: u32) -> Result<TermId, TermError> {
        check_width(width)?;
        let bits = (0..width)
            .map(|_| self.fresh_bool_atom().1)
            .collect::<Vec<_>>();
        self.make_bitvec(bits)
    }

    pub(crate) fn bitvec_from_binary(&mut self, literal: &str) -> Result<TermId, TermError> {
        let digits = literal
            .strip_prefix("#b")
            .ok_or_else(|| TermError::new("binary bit-vector literal must start with `#b`"))?;
        if digits.is_empty() || !digits.bytes().all(|byte| matches!(byte, b'0' | b'1')) {
            return Err(TermError::new("invalid binary bit-vector literal"));
        }
        check_width(
            u32::try_from(digits.len())
                .map_err(|_| TermError::new("bit-vector literal is too wide"))?,
        )?;
        let bits = digits
            .bytes()
            .rev()
            .map(|byte| self.bool_constant(byte == b'1'))
            .collect();
        self.make_bitvec(bits)
    }

    pub(crate) fn bitvec_from_hexadecimal(&mut self, literal: &str) -> Result<TermId, TermError> {
        let digits = literal
            .strip_prefix("#x")
            .ok_or_else(|| TermError::new("hexadecimal bit-vector literal must start with `#x`"))?;
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(TermError::new("invalid hexadecimal bit-vector literal"));
        }
        let width = digits
            .len()
            .checked_mul(4)
            .and_then(|width| u32::try_from(width).ok())
            .ok_or_else(|| TermError::new("bit-vector literal is too wide"))?;
        check_width(width)?;
        let mut bits = Vec::with_capacity(width as usize);
        for digit in digits.bytes().rev() {
            let value = match digit {
                b'0'..=b'9' => digit - b'0',
                b'a'..=b'f' => digit - b'a' + 10,
                b'A'..=b'F' => digit - b'A' + 10,
                _ => unreachable!("hexadecimal digits checked above"),
            };
            for index in 0..4 {
                bits.push(self.bool_constant(value & (1 << index) != 0));
            }
        }
        self.make_bitvec(bits)
    }

    pub(crate) fn bitvec_from_decimal(
        &mut self,
        decimal: &str,
        width: u32,
    ) -> Result<TermId, TermError> {
        check_width(width)?;
        if decimal.is_empty() || !decimal.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(TermError::new("invalid decimal bit-vector value"));
        }
        if decimal.len() > 1 && decimal.starts_with('0') {
            return Err(TermError::new(
                "decimal bit-vector value is not a valid numeral",
            ));
        }
        let mut digits = decimal.bytes().map(|byte| byte - b'0').collect::<Vec<_>>();
        let mut value_bits = Vec::new();
        while digits.iter().any(|&digit| digit != 0) {
            let mut carry = 0_u8;
            for digit in &mut digits {
                let current = carry * 10 + *digit;
                *digit = current / 2;
                carry = current % 2;
            }
            value_bits.push(carry != 0);
            let first_nonzero = digits.iter().position(|&digit| digit != 0);
            if let Some(first_nonzero) = first_nonzero {
                digits.drain(..first_nonzero);
            } else {
                digits.clear();
            }
        }
        if value_bits.len() > width as usize {
            return Err(TermError::new(format!(
                "decimal value does not fit in a {width}-bit vector"
            )));
        }
        value_bits.resize(width as usize, false);
        let bits = value_bits
            .into_iter()
            .map(|value| self.bool_constant(value))
            .collect();
        self.make_bitvec(bits)
    }

    pub(crate) fn bitvec_width(&self, term: TermId) -> Result<u32, TermError> {
        match self.sort(term)? {
            Sort::BitVec(width) => Ok(width),
            Sort::Bool | Sort::Int | Sort::Real | Sort::Uninterpreted(_) | Sort::Array(_) => {
                Err(TermError::new("expected a bit-vector term"))
            }
        }
    }

    pub(crate) fn bvnot(&mut self, term: TermId) -> Result<TermId, TermError> {
        let bits = self.bitvec_bits(term)?.to_vec();
        let result = bits
            .into_iter()
            .map(|bit| self.not(bit))
            .collect::<Result<Vec<_>, _>>()?;
        self.make_bitvec(result)
    }

    pub(crate) fn bvand(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        self.fold_bitwise(terms, Bitwise::And)
    }

    pub(crate) fn bvor(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        self.fold_bitwise(terms, Bitwise::Or)
    }

    pub(crate) fn bvxor(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        self.fold_bitwise(terms, Bitwise::Xor)
    }

    pub(crate) fn bvnand(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let conjunction = self.bvand(&[left, right])?;
        self.bvnot(conjunction)
    }

    pub(crate) fn bvnor(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let disjunction = self.bvor(&[left, right])?;
        self.bvnot(disjunction)
    }

    pub(crate) fn bvxnor(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let exclusive = self.bvxor(&[left, right])?;
        self.bvnot(exclusive)
    }

    pub(crate) fn bvcomp(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let equality = self.equal(&[left, right])?;
        self.make_bitvec(vec![equality])
    }

    fn fold_bitwise(&mut self, terms: &[TermId], operation: Bitwise) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new(format!(
                "`{}` expects at least two arguments",
                operation.name()
            )));
        }
        let width = self.bitvec_width(terms[0])?;
        let mut result = self.bitvec_bits(terms[0])?.to_vec();
        for &term in &terms[1..] {
            if self.bitvec_width(term)? != width {
                return Err(TermError::new(format!(
                    "all arguments to `{}` must have the same bit-vector width",
                    operation.name()
                )));
            }
            let right = self.bitvec_bits(term)?.to_vec();
            for (left, right) in result.iter_mut().zip(right) {
                *left = match operation {
                    Bitwise::And => self.and(&[*left, right])?,
                    Bitwise::Or => self.or(&[*left, right])?,
                    Bitwise::Xor => self.xor(*left, right)?,
                };
            }
        }
        self.make_bitvec(result)
    }

    pub(crate) fn concat(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let left_width = self.bitvec_width(left)?;
        let right_width = self.bitvec_width(right)?;
        let width = left_width
            .checked_add(right_width)
            .ok_or_else(|| TermError::new("concatenated bit-vector width overflow"))?;
        check_width(width)?;
        let mut bits = self.bitvec_bits(right)?.to_vec();
        bits.extend_from_slice(self.bitvec_bits(left)?);
        self.make_bitvec(bits)
    }

    pub(crate) fn extract(
        &mut self,
        term: TermId,
        high: u32,
        low: u32,
    ) -> Result<TermId, TermError> {
        let width = self.bitvec_width(term)?;
        if low > high || high >= width {
            return Err(TermError::new(format!(
                "invalid extraction range [{high}:{low}] for width {width}"
            )));
        }
        let bits = self.bitvec_bits(term)?[low as usize..=high as usize].to_vec();
        self.make_bitvec(bits)
    }

    pub(crate) fn repeat(&mut self, term: TermId, count: u32) -> Result<TermId, TermError> {
        if count == 0 {
            return Err(TermError::new("bit-vector repeat count must be positive"));
        }
        let width = self
            .bitvec_width(term)?
            .checked_mul(count)
            .ok_or_else(|| TermError::new("repeated bit-vector width overflow"))?;
        check_width(width)?;
        let input = self.bitvec_bits(term)?.to_vec();
        let mut bits = Vec::with_capacity(width as usize);
        for _ in 0..count {
            bits.extend_from_slice(&input);
        }
        self.make_bitvec(bits)
    }

    pub(crate) fn zero_extend(&mut self, term: TermId, amount: u32) -> Result<TermId, TermError> {
        let width = self
            .bitvec_width(term)?
            .checked_add(amount)
            .ok_or_else(|| TermError::new("zero-extended bit-vector width overflow"))?;
        check_width(width)?;
        let mut bits = self.bitvec_bits(term)?.to_vec();
        bits.resize(width as usize, self.bool_constant(false));
        self.make_bitvec(bits)
    }

    pub(crate) fn sign_extend(&mut self, term: TermId, amount: u32) -> Result<TermId, TermError> {
        let original_width = self.bitvec_width(term)?;
        let width = original_width
            .checked_add(amount)
            .ok_or_else(|| TermError::new("sign-extended bit-vector width overflow"))?;
        check_width(width)?;
        let mut bits = self.bitvec_bits(term)?.to_vec();
        let sign = bits[original_width as usize - 1];
        bits.resize(width as usize, sign);
        self.make_bitvec(bits)
    }

    pub(crate) fn rotate_left(&mut self, term: TermId, amount: u32) -> Result<TermId, TermError> {
        let width = self.bitvec_width(term)?;
        let amount = amount % width;
        let input = self.bitvec_bits(term)?.to_vec();
        let mut bits = vec![self.bool_constant(false); width as usize];
        for (index, bit) in input.into_iter().enumerate() {
            bits[(index + amount as usize) % width as usize] = bit;
        }
        self.make_bitvec(bits)
    }

    pub(crate) fn rotate_right(&mut self, term: TermId, amount: u32) -> Result<TermId, TermError> {
        let width = self.bitvec_width(term)?;
        let amount = amount % width;
        let input = self.bitvec_bits(term)?.to_vec();
        let mut bits = vec![self.bool_constant(false); width as usize];
        for (index, bit) in input.into_iter().enumerate() {
            bits[(index + width as usize - amount as usize) % width as usize] = bit;
        }
        self.make_bitvec(bits)
    }

    pub(crate) fn bvneg(&mut self, term: TermId) -> Result<TermId, TermError> {
        let bits = self.bitvec_bits(term)?.to_vec();
        let result = self.negate_bits(&bits)?;
        self.make_bitvec(result)
    }

    pub(crate) fn bvadd(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`bvadd` expects at least two arguments"));
        }
        let width = self.bitvec_width(terms[0])?;
        let mut result = self.bitvec_bits(terms[0])?.to_vec();
        for &term in &terms[1..] {
            if self.bitvec_width(term)? != width {
                return Err(TermError::new(
                    "all arguments to `bvadd` must have the same width",
                ));
            }
            let right = self.bitvec_bits(term)?.to_vec();
            result = self.add_bits(&result, &right)?.0;
        }
        self.make_bitvec(result)
    }

    pub(crate) fn bvsub(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvsub")?;
        let left = self.bitvec_bits(left)?.to_vec();
        let right = self.bitvec_bits(right)?.to_vec();
        let result = self.subtract_bits(&left, &right)?;
        self.make_bitvec(result)
    }

    pub(crate) fn bvmul(&mut self, terms: &[TermId]) -> Result<TermId, TermError> {
        if terms.len() < 2 {
            return Err(TermError::new("`bvmul` expects at least two arguments"));
        }
        let width = self.bitvec_width(terms[0])?;
        check_quadratic(width, "bvmul")?;
        let mut result = self.bitvec_bits(terms[0])?.to_vec();
        for &term in &terms[1..] {
            if self.bitvec_width(term)? != width {
                return Err(TermError::new(
                    "all arguments to `bvmul` must have the same width",
                ));
            }
            let right = self.bitvec_bits(term)?.to_vec();
            result = self.multiply_bits(&result, &right, width as usize)?;
        }
        self.make_bitvec(result)
    }

    pub(crate) fn bvudiv(
        &mut self,
        dividend: TermId,
        divisor: TermId,
    ) -> Result<TermId, TermError> {
        self.require_same_bv_width(dividend, divisor, "bvudiv")?;
        let dividend = self.bitvec_bits(dividend)?.to_vec();
        let divisor = self.bitvec_bits(divisor)?.to_vec();
        let (quotient, _) = self.unsigned_divide_bits(&dividend, &divisor)?;
        self.make_bitvec(quotient)
    }

    pub(crate) fn bvurem(
        &mut self,
        dividend: TermId,
        divisor: TermId,
    ) -> Result<TermId, TermError> {
        self.require_same_bv_width(dividend, divisor, "bvurem")?;
        let dividend = self.bitvec_bits(dividend)?.to_vec();
        let divisor = self.bitvec_bits(divisor)?.to_vec();
        let (_, remainder) = self.unsigned_divide_bits(&dividend, &divisor)?;
        self.make_bitvec(remainder)
    }

    pub(crate) fn bvsdiv(
        &mut self,
        dividend: TermId,
        divisor: TermId,
    ) -> Result<TermId, TermError> {
        self.require_same_bv_width(dividend, divisor, "bvsdiv")?;
        let dividend = self.bitvec_bits(dividend)?.to_vec();
        let divisor = self.bitvec_bits(divisor)?.to_vec();
        let dividend_sign = *dividend.last().expect("bit-vectors are nonempty");
        let divisor_sign = *divisor.last().expect("bit-vectors are nonempty");
        let abs_dividend = self.absolute_bits(&dividend, dividend_sign)?;
        let abs_divisor = self.absolute_bits(&divisor, divisor_sign)?;
        let (quotient, _) = self.unsigned_divide_bits(&abs_dividend, &abs_divisor)?;
        let negative = self.xor(dividend_sign, divisor_sign)?;
        let negated = self.negate_bits(&quotient)?;
        let result = self.select_bits(negative, &negated, &quotient)?;
        self.make_bitvec(result)
    }

    pub(crate) fn bvsrem(
        &mut self,
        dividend: TermId,
        divisor: TermId,
    ) -> Result<TermId, TermError> {
        self.require_same_bv_width(dividend, divisor, "bvsrem")?;
        let dividend = self.bitvec_bits(dividend)?.to_vec();
        let divisor = self.bitvec_bits(divisor)?.to_vec();
        let dividend_sign = *dividend.last().expect("bit-vectors are nonempty");
        let divisor_sign = *divisor.last().expect("bit-vectors are nonempty");
        let abs_dividend = self.absolute_bits(&dividend, dividend_sign)?;
        let abs_divisor = self.absolute_bits(&divisor, divisor_sign)?;
        let (_, remainder) = self.unsigned_divide_bits(&abs_dividend, &abs_divisor)?;
        let negated = self.negate_bits(&remainder)?;
        let result = self.select_bits(dividend_sign, &negated, &remainder)?;
        self.make_bitvec(result)
    }

    pub(crate) fn bvsmod(
        &mut self,
        dividend: TermId,
        divisor: TermId,
    ) -> Result<TermId, TermError> {
        self.require_same_bv_width(dividend, divisor, "bvsmod")?;
        let dividend_bits = self.bitvec_bits(dividend)?.to_vec();
        let divisor_bits = self.bitvec_bits(divisor)?.to_vec();
        let dividend_sign = *dividend_bits.last().expect("bit-vectors are nonempty");
        let divisor_sign = *divisor_bits.last().expect("bit-vectors are nonempty");
        let abs_dividend = self.absolute_bits(&dividend_bits, dividend_sign)?;
        let abs_divisor = self.absolute_bits(&divisor_bits, divisor_sign)?;
        let (_, unsigned_remainder) = self.unsigned_divide_bits(&abs_dividend, &abs_divisor)?;
        let remainder_is_zero = self.is_zero_bits(&unsigned_remainder)?;
        let negated_remainder = self.negate_bits(&unsigned_remainder)?;
        let negative_positive = self.add_bits(&negated_remainder, &divisor_bits)?.0;
        let positive_negative = self.add_bits(&unsigned_remainder, &divisor_bits)?.0;

        let not_dividend_sign = self.not(dividend_sign)?;
        let not_divisor_sign = self.not(divisor_sign)?;
        let both_positive = self.and(&[not_dividend_sign, not_divisor_sign])?;
        let dividend_negative = self.and(&[dividend_sign, not_divisor_sign])?;
        let dividend_positive = self.and(&[not_dividend_sign, divisor_sign])?;

        let mut result = negated_remainder;
        result = self.select_bits(dividend_positive, &positive_negative, &result)?;
        result = self.select_bits(dividend_negative, &negative_positive, &result)?;
        result = self.select_bits(both_positive, &unsigned_remainder, &result)?;
        result = self.select_bits(remainder_is_zero, &unsigned_remainder, &result)?;
        self.make_bitvec(result)
    }

    pub(crate) fn bvshl(&mut self, value: TermId, amount: TermId) -> Result<TermId, TermError> {
        self.variable_shift(value, amount, Shift::Left)
    }

    pub(crate) fn bvlshr(&mut self, value: TermId, amount: TermId) -> Result<TermId, TermError> {
        self.variable_shift(value, amount, Shift::LogicalRight)
    }

    pub(crate) fn bvashr(&mut self, value: TermId, amount: TermId) -> Result<TermId, TermError> {
        self.variable_shift(value, amount, Shift::ArithmeticRight)
    }

    fn variable_shift(
        &mut self,
        value: TermId,
        amount: TermId,
        direction: Shift,
    ) -> Result<TermId, TermError> {
        let width = self.require_same_bv_width(value, amount, direction.name())?;
        let selectors = self.bitvec_bits(amount)?.to_vec();
        let mut result = self.bitvec_bits(value)?.to_vec();
        let sign = *result.last().expect("bit-vectors are nonempty");
        let false_term = self.bool_constant(false);
        for (index, selector) in selectors.into_iter().enumerate() {
            let shift = 1_usize.checked_shl(index as u32);
            let fill = if direction == Shift::ArithmeticRight {
                sign
            } else {
                false_term
            };
            let candidate = if let Some(shift) = shift.filter(|&shift| shift < width as usize) {
                (0..width as usize)
                    .map(|output| match direction {
                        Shift::Left => output
                            .checked_sub(shift)
                            .map_or(false_term, |input| result[input]),
                        Shift::LogicalRight | Shift::ArithmeticRight => {
                            let input = output + shift;
                            if input < width as usize {
                                result[input]
                            } else {
                                fill
                            }
                        }
                    })
                    .collect::<Vec<_>>()
            } else {
                vec![fill; width as usize]
            };
            result = self.select_bits(selector, &candidate, &result)?;
        }
        self.make_bitvec(result)
    }

    pub(crate) fn bvult(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvult")?;
        let left = self.bitvec_bits(left)?.to_vec();
        let right = self.bitvec_bits(right)?.to_vec();
        self.unsigned_less_than_bits(&left, &right)
    }

    pub(crate) fn bvule(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let greater = self.bvult(right, left)?;
        self.not(greater)
    }

    pub(crate) fn bvugt(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.bvult(right, left)
    }

    pub(crate) fn bvuge(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.bvule(right, left)
    }

    pub(crate) fn bvslt(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvslt")?;
        let left_bits = self.bitvec_bits(left)?.to_vec();
        let right_bits = self.bitvec_bits(right)?.to_vec();
        let left_sign = *left_bits.last().expect("bit-vectors are nonempty");
        let right_sign = *right_bits.last().expect("bit-vectors are nonempty");
        let signs_differ = self.xor(left_sign, right_sign)?;
        let unsigned = self.unsigned_less_than_bits(&left_bits, &right_bits)?;
        self.ite(signs_differ, left_sign, unsigned)
    }

    pub(crate) fn bvsle(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let greater = self.bvslt(right, left)?;
        self.not(greater)
    }

    pub(crate) fn bvsgt(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.bvslt(right, left)
    }

    pub(crate) fn bvsge(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.bvsle(right, left)
    }

    pub(crate) fn bvnego(&mut self, term: TermId) -> Result<TermId, TermError> {
        let bits = self.bitvec_bits(term)?.to_vec();
        let sign = *bits.last().expect("bit-vectors are nonempty");
        let low_zero = self.is_zero_bits(&bits[..bits.len() - 1])?;
        self.and(&[sign, low_zero])
    }

    pub(crate) fn bvuaddo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvuaddo")?;
        let left = self.bitvec_bits(left)?.to_vec();
        let right = self.bitvec_bits(right)?.to_vec();
        Ok(self.add_bits(&left, &right)?.1)
    }

    pub(crate) fn bvsaddo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvsaddo")?;
        let left = self.bitvec_bits(left)?.to_vec();
        let right = self.bitvec_bits(right)?.to_vec();
        let result = self.add_bits(&left, &right)?.0;
        let left_sign = *left.last().expect("bit-vectors are nonempty");
        let right_sign = *right.last().expect("bit-vectors are nonempty");
        let result_sign = *result.last().expect("bit-vectors are nonempty");
        let same_inputs = self.iff(left_sign, right_sign)?;
        let changed_sign = self.xor(left_sign, result_sign)?;
        self.and(&[same_inputs, changed_sign])
    }

    pub(crate) fn bvumulo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let width = self.require_same_bv_width(left, right, "bvumulo")?;
        check_quadratic(width, "bvumulo")?;
        let full_width = width
            .checked_mul(2)
            .ok_or_else(|| TermError::new("full multiplication width overflow"))?;
        check_width(full_width)?;
        let mut left = self.bitvec_bits(left)?.to_vec();
        let mut right = self.bitvec_bits(right)?.to_vec();
        left.resize(full_width as usize, self.bool_constant(false));
        right.resize(full_width as usize, self.bool_constant(false));
        let product = self.multiply_bits(&left, &right, full_width as usize)?;
        let high_nonzero = self.is_zero_bits(&product[width as usize..])?;
        self.not(high_nonzero)
    }

    pub(crate) fn bvsmulo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let width = self.require_same_bv_width(left, right, "bvsmulo")?;
        check_quadratic(width, "bvsmulo")?;
        let full_width = width
            .checked_mul(2)
            .ok_or_else(|| TermError::new("full multiplication width overflow"))?;
        check_width(full_width)?;
        let mut left = self.bitvec_bits(left)?.to_vec();
        let mut right = self.bitvec_bits(right)?.to_vec();
        let left_sign = *left.last().expect("bit-vectors are nonempty");
        let right_sign = *right.last().expect("bit-vectors are nonempty");
        left.resize(full_width as usize, left_sign);
        right.resize(full_width as usize, right_sign);
        let product = self.multiply_bits(&left, &right, full_width as usize)?;
        let result_sign = product[width as usize - 1];
        let high_matches = product[width as usize..]
            .iter()
            .map(|&bit| self.iff(bit, result_sign))
            .collect::<Result<Vec<_>, _>>()?;
        let fits = self.and(&high_matches)?;
        self.not(fits)
    }

    pub(crate) fn bvusubo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.bvult(left, right)
    }

    pub(crate) fn bvssubo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvssubo")?;
        let left = self.bitvec_bits(left)?.to_vec();
        let right = self.bitvec_bits(right)?.to_vec();
        let result = self.subtract_bits(&left, &right)?;
        let left_sign = *left.last().expect("bit-vectors are nonempty");
        let right_sign = *right.last().expect("bit-vectors are nonempty");
        let result_sign = *result.last().expect("bit-vectors are nonempty");
        let different_inputs = self.xor(left_sign, right_sign)?;
        let changed_sign = self.xor(left_sign, result_sign)?;
        self.and(&[different_inputs, changed_sign])
    }

    pub(crate) fn bvsdivo(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        self.require_same_bv_width(left, right, "bvsdivo")?;
        let minimum = self.bvnego(left)?;
        let right = self.bitvec_bits(right)?.to_vec();
        let all_ones = right
            .iter()
            .map(|&bit| self.iff(bit, self.bool_constant(true)))
            .collect::<Result<Vec<_>, _>>()?;
        let negative_one = self.and(&all_ones)?;
        self.and(&[minimum, negative_one])
    }

    fn require_same_bv_width(
        &self,
        left: TermId,
        right: TermId,
        operation: &str,
    ) -> Result<u32, TermError> {
        let left_width = self.bitvec_width(left)?;
        let right_width = self.bitvec_width(right)?;
        if left_width == right_width {
            Ok(left_width)
        } else {
            Err(TermError::new(format!(
                "`{operation}` operands have widths {left_width} and {right_width}"
            )))
        }
    }

    fn add_bits(
        &mut self,
        left: &[TermId],
        right: &[TermId],
    ) -> Result<(Vec<TermId>, TermId), TermError> {
        debug_assert_eq!(left.len(), right.len());
        let mut carry = self.bool_constant(false);
        let mut result = Vec::with_capacity(left.len());
        for (&left, &right) in left.iter().zip(right) {
            let pair_sum = self.xor(left, right)?;
            result.push(self.xor(pair_sum, carry)?);
            let pair_carry = self.and(&[left, right])?;
            let propagated = self.and(&[pair_sum, carry])?;
            carry = self.or(&[pair_carry, propagated])?;
        }
        Ok((result, carry))
    }

    fn negate_bits(&mut self, bits: &[TermId]) -> Result<Vec<TermId>, TermError> {
        let inverted = bits
            .iter()
            .map(|&bit| self.not(bit))
            .collect::<Result<Vec<_>, _>>()?;
        let mut one = vec![self.bool_constant(false); bits.len()];
        one[0] = self.bool_constant(true);
        Ok(self.add_bits(&inverted, &one)?.0)
    }

    fn subtract_bits(
        &mut self,
        left: &[TermId],
        right: &[TermId],
    ) -> Result<Vec<TermId>, TermError> {
        let negated = self.negate_bits(right)?;
        Ok(self.add_bits(left, &negated)?.0)
    }

    fn multiply_bits(
        &mut self,
        left: &[TermId],
        right: &[TermId],
        output_width: usize,
    ) -> Result<Vec<TermId>, TermError> {
        let false_term = self.bool_constant(false);
        let mut result = vec![false_term; output_width];
        for (right_index, &right_bit) in right.iter().enumerate().take(output_width) {
            let mut partial = vec![false_term; output_width];
            for (left_index, &left_bit) in left.iter().enumerate() {
                let output = left_index + right_index;
                if output >= output_width {
                    break;
                }
                partial[output] = self.and(&[left_bit, right_bit])?;
            }
            result = self.add_bits(&result, &partial)?.0;
        }
        Ok(result)
    }

    fn unsigned_divide_bits(
        &mut self,
        dividend: &[TermId],
        divisor: &[TermId],
    ) -> Result<(Vec<TermId>, Vec<TermId>), TermError> {
        debug_assert_eq!(dividend.len(), divisor.len());
        let width = u32::try_from(dividend.len())
            .map_err(|_| TermError::new("bit-vector width exceeds u32"))?;
        check_quadratic(width, "bit-vector division")?;
        let false_term = self.bool_constant(false);
        let mut extended_divisor = divisor.to_vec();
        extended_divisor.push(false_term);
        let mut remainder = vec![false_term; dividend.len() + 1];
        let mut quotient = vec![false_term; dividend.len()];
        for index in (0..dividend.len()).rev() {
            for bit in (1..remainder.len()).rev() {
                remainder[bit] = remainder[bit - 1];
            }
            remainder[0] = dividend[index];
            let less = self.unsigned_less_than_bits(&remainder, &extended_divisor)?;
            let greater_or_equal = self.not(less)?;
            let subtracted = self.subtract_bits(&remainder, &extended_divisor)?;
            remainder = self.select_bits(greater_or_equal, &subtracted, &remainder)?;
            quotient[index] = greater_or_equal;
        }
        remainder.pop();
        Ok((quotient, remainder))
    }

    fn unsigned_less_than_bits(
        &mut self,
        left: &[TermId],
        right: &[TermId],
    ) -> Result<TermId, TermError> {
        debug_assert_eq!(left.len(), right.len());
        let mut less = self.bool_constant(false);
        let mut equal = self.bool_constant(true);
        for (&left, &right) in left.iter().zip(right).rev() {
            let not_left = self.not(left)?;
            let left_less = self.and(&[not_left, right])?;
            let decisive = self.and(&[equal, left_less])?;
            less = self.or(&[less, decisive])?;
            let bit_equal = self.iff(left, right)?;
            equal = self.and(&[equal, bit_equal])?;
        }
        Ok(less)
    }

    fn absolute_bits(&mut self, bits: &[TermId], sign: TermId) -> Result<Vec<TermId>, TermError> {
        let negated = self.negate_bits(bits)?;
        self.select_bits(sign, &negated, bits)
    }

    fn select_bits(
        &mut self,
        condition: TermId,
        then_bits: &[TermId],
        else_bits: &[TermId],
    ) -> Result<Vec<TermId>, TermError> {
        debug_assert_eq!(then_bits.len(), else_bits.len());
        then_bits
            .iter()
            .zip(else_bits)
            .map(|(&then_bit, &else_bit)| self.ite(condition, then_bit, else_bit))
            .collect()
    }

    fn is_zero_bits(&mut self, bits: &[TermId]) -> Result<TermId, TermError> {
        let zero_bits = bits
            .iter()
            .map(|&bit| self.not(bit))
            .collect::<Result<Vec<_>, _>>()?;
        self.and(&zero_bits)
    }
}

#[derive(Clone, Copy)]
enum Bitwise {
    And,
    Or,
    Xor,
}

impl Bitwise {
    fn name(self) -> &'static str {
        match self {
            Self::And => "bvand",
            Self::Or => "bvor",
            Self::Xor => "bvxor",
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Shift {
    Left,
    LogicalRight,
    ArithmeticRight,
}

impl Shift {
    fn name(self) -> &'static str {
        match self {
            Self::Left => "bvshl",
            Self::LogicalRight => "bvlshr",
            Self::ArithmeticRight => "bvashr",
        }
    }
}

fn check_width(width: u32) -> Result<(), TermError> {
    if width == 0 {
        Err(TermError::new("bit-vector width must be greater than zero"))
    } else if width > MAX_BITVECTOR_WIDTH {
        Err(TermError::new(format!(
            "bit-vector width {width} exceeds the current limit of {MAX_BITVECTOR_WIDTH}"
        )))
    } else {
        Ok(())
    }
}

fn check_quadratic(width: u32, operation: &str) -> Result<(), TermError> {
    if u64::from(width) * u64::from(width) > MAX_QUADRATIC_LOWERING_WORK {
        Err(TermError::new(format!(
            "`{operation}` at width {width} exceeds the current Boolean-lowering work limit"
        )))
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::TermStore;
    use crate::smt::term::{SymbolId, TermKind};

    #[test]
    fn constants_concat_extract_extend_and_rotate_use_smt_bit_order() {
        let mut terms = TermStore::new();
        let a = terms.bitvec_from_binary("#b101").unwrap();
        let b = terms.bitvec_from_binary("#b01").unwrap();
        let concatenated = terms.concat(a, b).unwrap();
        assert_eq!(value(&terms, concatenated), 0b10101);
        assert_eq!(
            built_value(&mut terms, |terms| terms.extract(concatenated, 3, 1)),
            0b010
        );
        assert_eq!(
            built_value(&mut terms, |terms| terms.zero_extend(a, 2)),
            0b00101
        );
        assert_eq!(
            built_value(&mut terms, |terms| terms.sign_extend(a, 2)),
            0b11101
        );
        assert_eq!(
            built_value(&mut terms, |terms| terms.rotate_left(a, 1)),
            0b011
        );
        assert_eq!(
            built_value(&mut terms, |terms| terms.rotate_right(a, 1)),
            0b110
        );
    }

    #[test]
    fn exhaustive_small_arithmetic_matches_integer_semantics() {
        for width in 1..=4 {
            let modulus = 1_u64 << width;
            let mask = modulus - 1;
            for left in 0..modulus {
                for right in 0..modulus {
                    let mut terms = TermStore::new();
                    let a = constant(&mut terms, left, width);
                    let b = constant(&mut terms, right, width);
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvadd(&[a, b])),
                        (left + right) & mask
                    );
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvsub(a, b)),
                        left.wrapping_sub(right) & mask
                    );
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvmul(&[a, b])),
                        (left * right) & mask
                    );
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvudiv(a, b)),
                        left.checked_div(right).unwrap_or(mask)
                    );
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvurem(a, b)),
                        if right == 0 { left } else { left % right }
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvult(a, b)),
                        left < right
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvslt(a, b)),
                        signed(left, width) < signed(right, width)
                    );
                }
            }
        }
    }

    #[test]
    fn exhaustive_small_signed_division_and_remainders_match_smt_definitions() {
        for width in 1..=4 {
            let modulus = 1_u64 << width;
            let mask = modulus - 1;
            let minimum = -(1_i64 << (width - 1));
            for left in 0..modulus {
                for right in 0..modulus {
                    let mut terms = TermStore::new();
                    let a = constant(&mut terms, left, width);
                    let b = constant(&mut terms, right, width);
                    let x = signed(left, width);
                    let y = signed(right, width);
                    let quotient = if y == 0 {
                        if x < 0 { 1 } else { mask as i64 }
                    } else if x == minimum && y == -1 {
                        minimum
                    } else {
                        x / y
                    };
                    let remainder = if y == 0 { x } else { x % y };
                    let modulo = signed_modulo(x, y);
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvsdiv(a, b)),
                        unsigned(quotient, width)
                    );
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvsrem(a, b)),
                        unsigned(remainder, width)
                    );
                    assert_eq!(
                        built_value(&mut terms, |terms| terms.bvsmod(a, b)),
                        unsigned(modulo, width)
                    );
                }
            }
        }
    }

    #[test]
    fn exhaustive_small_overflow_predicates_match_widened_arithmetic() {
        for width in 1..=4 {
            let modulus = 1_u64 << width;
            let signed_min = -(1_i64 << (width - 1));
            let signed_max = (1_i64 << (width - 1)) - 1;
            for left in 0..modulus {
                for right in 0..modulus {
                    let mut terms = TermStore::new();
                    let a = constant(&mut terms, left, width);
                    let b = constant(&mut terms, right, width);
                    let x = signed(left, width);
                    let y = signed(right, width);
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvuaddo(a, b)),
                        left + right >= modulus
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvsaddo(a, b)),
                        !(signed_min..=signed_max).contains(&(x + y))
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvumulo(a, b)),
                        left * right >= modulus
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvsmulo(a, b)),
                        !(signed_min..=signed_max).contains(&(x * y))
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvusubo(a, b)),
                        left < right
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvssubo(a, b)),
                        !(signed_min..=signed_max).contains(&(x - y))
                    );
                    assert_eq!(
                        built_boolean(&mut terms, |terms| terms.bvsdivo(a, b)),
                        x == signed_min && y == -1
                    );
                }
            }
        }
    }

    #[test]
    fn exhaustive_symbolic_four_bit_circuits_match_integer_semantics() {
        const WIDTH: u32 = 4;
        const MASK: u64 = (1 << WIDTH) - 1;

        let mut terms = TermStore::new();
        let a = terms.fresh_bitvec(WIDTH).unwrap();
        let b = terms.fresh_bitvec(WIDTH).unwrap();
        let a_symbols = symbols(&terms, a);
        let b_symbols = symbols(&terms, b);

        let not = terms.bvnot(a).unwrap();
        let neg = terms.bvneg(a).unwrap();
        let and = terms.bvand(&[a, b]).unwrap();
        let or = terms.bvor(&[a, b]).unwrap();
        let xor = terms.bvxor(&[a, b]).unwrap();
        let nand = terms.bvnand(a, b).unwrap();
        let nor = terms.bvnor(a, b).unwrap();
        let xnor = terms.bvxnor(a, b).unwrap();
        let comp = terms.bvcomp(a, b).unwrap();
        let add = terms.bvadd(&[a, b]).unwrap();
        let sub = terms.bvsub(a, b).unwrap();
        let mul = terms.bvmul(&[a, b]).unwrap();
        let udiv = terms.bvudiv(a, b).unwrap();
        let urem = terms.bvurem(a, b).unwrap();
        let sdiv = terms.bvsdiv(a, b).unwrap();
        let srem = terms.bvsrem(a, b).unwrap();
        let smod = terms.bvsmod(a, b).unwrap();
        let shl = terms.bvshl(a, b).unwrap();
        let lshr = terms.bvlshr(a, b).unwrap();
        let ashr = terms.bvashr(a, b).unwrap();
        let ult = terms.bvult(a, b).unwrap();
        let ule = terms.bvule(a, b).unwrap();
        let ugt = terms.bvugt(a, b).unwrap();
        let uge = terms.bvuge(a, b).unwrap();
        let slt = terms.bvslt(a, b).unwrap();
        let sle = terms.bvsle(a, b).unwrap();
        let sgt = terms.bvsgt(a, b).unwrap();
        let sge = terms.bvsge(a, b).unwrap();
        let nego = terms.bvnego(a).unwrap();
        let uaddo = terms.bvuaddo(a, b).unwrap();
        let saddo = terms.bvsaddo(a, b).unwrap();
        let umulo = terms.bvumulo(a, b).unwrap();
        let smulo = terms.bvsmulo(a, b).unwrap();
        let usubo = terms.bvusubo(a, b).unwrap();
        let ssubo = terms.bvssubo(a, b).unwrap();
        let sdivo = terms.bvsdivo(a, b).unwrap();
        let concat = terms.concat(a, b).unwrap();
        let extracted = terms.extract(concat, 5, 2).unwrap();
        let zero_extended = terms.zero_extend(a, 3).unwrap();
        let sign_extended = terms.sign_extend(a, 3).unwrap();
        let rotated_left = terms.rotate_left(a, 3).unwrap();
        let rotated_right = terms.rotate_right(a, 3).unwrap();

        for left in 0..=MASK {
            for right in 0..=MASK {
                let x = signed(left, WIDTH);
                let y = signed(right, WIDTH);
                let signed_min = -(1_i64 << (WIDTH - 1));
                let signed_max = (1_i64 << (WIDTH - 1)) - 1;
                let signed_quotient = if y == 0 {
                    if x < 0 { 1 } else { MASK as i64 }
                } else if x == signed_min && y == -1 {
                    signed_min
                } else {
                    x / y
                };
                let signed_remainder = if y == 0 { x } else { x % y };

                let word = |term| symbolic_value(&terms, term, &a_symbols, &b_symbols, left, right);
                let predicate =
                    |term| symbolic_boolean(&terms, term, &a_symbols, &b_symbols, left, right);

                assert_eq!(word(not), (!left) & MASK, "bvnot {left} {right}");
                assert_eq!(
                    word(neg),
                    left.wrapping_neg() & MASK,
                    "bvneg {left} {right}"
                );
                assert_eq!(word(and), left & right, "bvand {left} {right}");
                assert_eq!(word(or), left | right, "bvor {left} {right}");
                assert_eq!(word(xor), left ^ right, "bvxor {left} {right}");
                assert_eq!(word(nand), (!(left & right)) & MASK, "bvnand");
                assert_eq!(word(nor), (!(left | right)) & MASK, "bvnor");
                assert_eq!(word(xnor), (!(left ^ right)) & MASK, "bvxnor");
                assert_eq!(word(comp), u64::from(left == right), "bvcomp");
                assert_eq!(word(add), (left + right) & MASK, "bvadd");
                assert_eq!(word(sub), left.wrapping_sub(right) & MASK, "bvsub");
                assert_eq!(word(mul), (left * right) & MASK, "bvmul");
                assert_eq!(
                    word(udiv),
                    left.checked_div(right).unwrap_or(MASK),
                    "bvudiv"
                );
                assert_eq!(
                    word(urem),
                    if right == 0 { left } else { left % right },
                    "bvurem"
                );
                assert_eq!(word(sdiv), unsigned(signed_quotient, WIDTH), "bvsdiv");
                assert_eq!(word(srem), unsigned(signed_remainder, WIDTH), "bvsrem");
                assert_eq!(word(smod), unsigned(signed_modulo(x, y), WIDTH), "bvsmod");
                assert_eq!(
                    word(shl),
                    if right >= u64::from(WIDTH) {
                        0
                    } else {
                        (left << right) & MASK
                    },
                    "bvshl"
                );
                assert_eq!(
                    word(lshr),
                    if right >= u64::from(WIDTH) {
                        0
                    } else {
                        left >> right
                    },
                    "bvlshr"
                );
                assert_eq!(
                    word(ashr),
                    unsigned(x >> right.min(u64::from(WIDTH)) as u32, WIDTH),
                    "bvashr"
                );
                assert_eq!(predicate(ult), left < right, "bvult");
                assert_eq!(predicate(ule), left <= right, "bvule");
                assert_eq!(predicate(ugt), left > right, "bvugt");
                assert_eq!(predicate(uge), left >= right, "bvuge");
                assert_eq!(predicate(slt), x < y, "bvslt");
                assert_eq!(predicate(sle), x <= y, "bvsle");
                assert_eq!(predicate(sgt), x > y, "bvsgt");
                assert_eq!(predicate(sge), x >= y, "bvsge");
                assert_eq!(predicate(nego), x == signed_min, "bvnego");
                assert_eq!(predicate(uaddo), left + right > MASK, "bvuaddo");
                assert_eq!(
                    predicate(saddo),
                    !(signed_min..=signed_max).contains(&(x + y)),
                    "bvsaddo"
                );
                assert_eq!(predicate(umulo), left * right > MASK, "bvumulo");
                assert_eq!(
                    predicate(smulo),
                    !(signed_min..=signed_max).contains(&(x * y)),
                    "bvsmulo"
                );
                assert_eq!(predicate(usubo), left < right, "bvusubo");
                assert_eq!(
                    predicate(ssubo),
                    !(signed_min..=signed_max).contains(&(x - y)),
                    "bvssubo"
                );
                assert_eq!(predicate(sdivo), x == signed_min && y == -1, "bvsdivo");
                assert_eq!(word(concat), (left << WIDTH) | right, "concat");
                assert_eq!(
                    word(extracted),
                    (((left << WIDTH) | right) >> 2) & MASK,
                    "extract"
                );
                assert_eq!(word(zero_extended), left, "zero_extend");
                assert_eq!(word(sign_extended), unsigned(x, WIDTH + 3), "sign_extend");
                assert_eq!(
                    word(rotated_left),
                    ((left << 3) | (left >> 1)) & MASK,
                    "rotate_left"
                );
                assert_eq!(
                    word(rotated_right),
                    ((left >> 3) | (left << 1)) & MASK,
                    "rotate_right"
                );
            }
        }
    }

    fn constant(terms: &mut TermStore, value: u64, width: u32) -> super::TermId {
        terms
            .bitvec_from_decimal(&value.to_string(), width)
            .unwrap()
    }

    fn value(terms: &TermStore, term: super::TermId) -> u64 {
        terms
            .evaluate_bitvec(term, |_| false)
            .unwrap()
            .into_iter()
            .enumerate()
            .fold(0, |value, (index, bit)| value | (u64::from(bit) << index))
    }

    fn boolean(terms: &TermStore, term: super::TermId) -> bool {
        terms.evaluate_bool(term, |_| false).unwrap()
    }

    fn symbols(terms: &TermStore, term: super::TermId) -> Vec<SymbolId> {
        terms
            .bitvec_bits(term)
            .unwrap()
            .iter()
            .map(|&bit| match terms.node(bit).kind {
                TermKind::Atom(symbol) => symbol,
                _ => panic!("fresh bit-vector bit must be an atom"),
            })
            .collect()
    }

    fn symbolic_value(
        terms: &TermStore,
        term: super::TermId,
        left_symbols: &[SymbolId],
        right_symbols: &[SymbolId],
        left: u64,
        right: u64,
    ) -> u64 {
        terms
            .evaluate_bitvec(term, |symbol| {
                symbolic_atom(symbol, left_symbols, right_symbols, left, right)
            })
            .unwrap()
            .into_iter()
            .enumerate()
            .fold(0, |value, (index, bit)| value | (u64::from(bit) << index))
    }

    fn symbolic_boolean(
        terms: &TermStore,
        term: super::TermId,
        left_symbols: &[SymbolId],
        right_symbols: &[SymbolId],
        left: u64,
        right: u64,
    ) -> bool {
        terms
            .evaluate_bool(term, |symbol| {
                symbolic_atom(symbol, left_symbols, right_symbols, left, right)
            })
            .unwrap()
    }

    fn symbolic_atom(
        symbol: SymbolId,
        left_symbols: &[SymbolId],
        right_symbols: &[SymbolId],
        left: u64,
        right: u64,
    ) -> bool {
        if let Some(index) = left_symbols
            .iter()
            .position(|&candidate| candidate == symbol)
        {
            left & (1 << index) != 0
        } else if let Some(index) = right_symbols
            .iter()
            .position(|&candidate| candidate == symbol)
        {
            right & (1 << index) != 0
        } else {
            panic!("unexpected symbolic bit {symbol:?}");
        }
    }

    fn built_value(
        terms: &mut TermStore,
        build: impl FnOnce(&mut TermStore) -> Result<super::TermId, super::TermError>,
    ) -> u64 {
        let term = build(terms).unwrap();
        value(terms, term)
    }

    fn built_boolean(
        terms: &mut TermStore,
        build: impl FnOnce(&mut TermStore) -> Result<super::TermId, super::TermError>,
    ) -> bool {
        let term = build(terms).unwrap();
        boolean(terms, term)
    }

    fn signed(value: u64, width: u32) -> i64 {
        let modulus = 1_i64 << width;
        let value = value as i64;
        if value & (1_i64 << (width - 1)) == 0 {
            value
        } else {
            value - modulus
        }
    }

    fn unsigned(value: i64, width: u32) -> u64 {
        value.rem_euclid(1_i64 << width) as u64
    }

    fn signed_modulo(dividend: i64, divisor: i64) -> i64 {
        if divisor == 0 {
            return dividend;
        }
        let remainder = dividend.unsigned_abs() % divisor.unsigned_abs();
        if remainder == 0 {
            0
        } else {
            match (dividend < 0, divisor < 0) {
                (false, false) => remainder as i64,
                (true, false) => divisor - remainder as i64,
                (false, true) => divisor + remainder as i64,
                (true, true) => -(remainder as i64),
            }
        }
    }
}
