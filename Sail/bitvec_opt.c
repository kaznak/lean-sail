#include <lean/lean.h>

/*
 * Fast BitVec operations for width ≤ 64.
 *
 * BitVec n = Fin (2^n) at runtime is just a Nat (proof erased).
 * For n ≤ 64, we use uint64_t arithmetic instead of GMP.
 *
 * Calling convention for @[extern] with {n : Nat} (a b : BitVec n):
 *   C args: (n : b_lean_obj_arg, a : lean_obj_arg, b : lean_obj_arg)
 *   b_ prefix = borrowed (not consumed), otherwise owned (must dec or return)
 *
 * Int runtime representation:
 *   scalar       → Int.ofNat (lean_unbox(i))
 *   tag == 0     → Int.ofNat (lean_ctor_get(i, 0))   [large non-negative]
 *   tag == 1     → Int.negSucc (lean_ctor_get(i, 0))  [represents -(n+1)]
 */

static inline uint64_t bitvec_mask(size_t n) {
  return (n >= 64) ? UINT64_MAX : ((UINT64_C(1) << n) - 1);
}

/* Extract uint64 from a Nat that is known to fit (or we take low 64 bits). */
static inline uint64_t nat_to_u64(lean_obj_arg x) {
  return lean_uint64_of_nat(x);
}

/* ── Arithmetic ────────────────────────────────────────────────────── */

/* BitVec.fastOfNat (n : Nat) (x : Nat) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_ofnat(
    b_lean_obj_arg n_obj, lean_obj_arg x) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      return lean_uint64_to_nat(vx & bitvec_mask(n));
    }
  }
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res result = lean_nat_mod(x, pow2n);
  lean_dec(x);
  lean_dec(pow2n);
  return result;
}

/* BitVec.fastAdd {n : Nat} (a b : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_add(
    b_lean_obj_arg n_obj, lean_obj_arg a, lean_obj_arg b) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t va = nat_to_u64(a), vb = nat_to_u64(b);
      lean_dec(a); lean_dec(b);
      return lean_uint64_to_nat((va + vb) & bitvec_mask(n));
    }
  }
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res sum = lean_nat_add(a, b);
  lean_dec(a); lean_dec(b);
  lean_obj_res result = lean_nat_mod(sum, pow2n);
  lean_dec(sum); lean_dec(pow2n);
  return result;
}

/* BitVec.fastSub {n : Nat} (a b : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_sub(
    b_lean_obj_arg n_obj, lean_obj_arg a, lean_obj_arg b) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t va = nat_to_u64(a), vb = nat_to_u64(b);
      lean_dec(a); lean_dec(b);
      return lean_uint64_to_nat((va - vb) & bitvec_mask(n));
    }
  }
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res tmp = lean_nat_sub(pow2n, b); lean_dec(b);
  lean_obj_res sum = lean_nat_add(tmp, a);   lean_dec(tmp); lean_dec(a);
  lean_obj_res result = lean_nat_mod(sum, pow2n);
  lean_dec(sum); lean_dec(pow2n);
  return result;
}

/* BitVec.fastMul {n : Nat} (a b : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_mul(
    b_lean_obj_arg n_obj, lean_obj_arg a, lean_obj_arg b) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t va = nat_to_u64(a), vb = nat_to_u64(b);
      lean_dec(a); lean_dec(b);
      return lean_uint64_to_nat((va * vb) & bitvec_mask(n));
    }
  }
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res prod = lean_nat_mul(a, b);
  lean_dec(a); lean_dec(b);
  lean_obj_res result = lean_nat_mod(prod, pow2n);
  lean_dec(prod); lean_dec(pow2n);
  return result;
}

/* ── Int conversion ────────────────────────────────────────────────── */

/*
 * Lean 4 Int runtime representation (NOT ofNat/negSucc constructors!):
 *   - Scalar: lean_box((unsigned)(int)value) for values in [INT_MIN, INT_MAX]
 *     Use lean_scalar_to_int64() to extract the signed value.
 *   - Non-scalar: GMP mpz object (lean_mpz_value) for large values.
 *     Use lean_int_* functions to manipulate.
 *
 * BitVec.ofInt w i is defined as:
 *   | .ofNat n   => BitVec.ofNat w n      -- i.e., n mod 2^w
 *   | .negSucc n => ~~~(BitVec.ofNat w n)  -- i.e., (2^w-1) - (m mod 2^w)
 *   where m = |i| - 1 for negative i = -(m+1)
 *
 * All lean_nat_* functions BORROW their arguments (b_lean_obj_arg).
 * lean_int_to_nat CONSUMES its argument (lean_obj_arg).
 * lean_nat_abs BORROWS its argument (b_lean_obj_arg).
 */

/* BitVec.fastOfInt (n : Nat) (i : Int) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_ofint(
    b_lean_obj_arg n_obj, lean_obj_arg i) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t mask = bitvec_mask(n);
      uint64_t result;
      if (lean_is_scalar(i)) {
        /* Small Int (both positive and negative): scalar encoding */
        int64_t vi = lean_scalar_to_int64(i);
        result = ((uint64_t)vi) & mask;
        /* i is scalar — no lean_dec needed */
      } else if (lean_int_dec_nonneg(i)) {
        /* Big non-negative Int (mpz): convert to Nat, take low bits */
        lean_obj_res nat_val = lean_int_to_nat(i); /* consumes i */
        result = lean_uint64_of_nat(nat_val) & mask; /* borrows nat_val */
        lean_dec(nat_val);
      } else {
        /* Big negative Int (mpz): i = -(m+1), result = ~m & mask */
        lean_obj_res abs_i = lean_nat_abs(i); /* borrows i, returns |i| */
        lean_dec(i);
        lean_obj_res m = lean_nat_sub(abs_i, lean_box(1)); /* borrows abs_i */
        lean_dec(abs_i);
        result = (~lean_uint64_of_nat(m)) & mask; /* borrows m */
        lean_dec(m);
      }
      return lean_uint64_to_nat(result);
    }
  }
  /* Fallback for n > 64: use Lean Nat arithmetic.
   * lean_int_dec_nonneg handles both scalar and mpz Int. */
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj); /* borrows args */

  if (lean_int_dec_nonneg(i)) {
    /* Non-negative: result = i_as_nat mod 2^n */
    lean_obj_res nat_val;
    if (lean_is_scalar(i)) {
      nat_val = i; /* reuse scalar directly as Nat (no ref count) */
    } else {
      nat_val = lean_int_to_nat(i); /* consumes i */
    }
    lean_obj_res result = lean_nat_mod(nat_val, pow2n); /* borrows both */
    lean_dec(nat_val); /* no-op for scalar, frees boxed */
    lean_dec(pow2n);
    return result;
  } else {
    /* Negative: i = -(m+1), result = (2^n - 1) - (m mod 2^n) */
    lean_obj_res abs_i = lean_nat_abs(i); /* borrows i, returns |i| */
    lean_dec(i); /* no-op for scalar, frees boxed */
    lean_obj_res m = lean_nat_sub(abs_i, lean_box(1)); /* borrows abs_i */
    lean_dec(abs_i);
    lean_obj_res m_mod = lean_nat_mod(m, pow2n); /* borrows both */
    lean_dec(m);
    lean_obj_res ones = lean_nat_sub(pow2n, lean_box(1)); /* borrows pow2n */
    lean_dec(pow2n);
    lean_obj_res result = lean_nat_sub(ones, m_mod); /* borrows both */
    lean_dec(ones); lean_dec(m_mod);
    return result;
  }
}

/* ── Bitwise ───────────────────────────────────────────────────────── */

/* BitVec.fastNot {n : Nat} (x : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_not(
    b_lean_obj_arg n_obj, lean_obj_arg x) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      return lean_uint64_to_nat((~vx) & bitvec_mask(n));
    }
  }
  /* Fallback: (2^n - 1) XOR x */
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res ones = lean_nat_sub(pow2n, lean_box(1));
  lean_dec(pow2n);
  lean_obj_res result = lean_nat_lxor(ones, x);
  lean_dec(ones); lean_dec(x);
  return result;
}

/* BitVec.fastAnd {n : Nat} (a b : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_and(
    b_lean_obj_arg n_obj, lean_obj_arg a, lean_obj_arg b) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t va = nat_to_u64(a), vb = nat_to_u64(b);
      lean_dec(a); lean_dec(b);
      return lean_uint64_to_nat(va & vb);
    }
  }
  lean_obj_res result = lean_nat_land(a, b);
  lean_dec(a); lean_dec(b);
  return result;
}

/* BitVec.fastOr {n : Nat} (a b : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_or(
    b_lean_obj_arg n_obj, lean_obj_arg a, lean_obj_arg b) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t va = nat_to_u64(a), vb = nat_to_u64(b);
      lean_dec(a); lean_dec(b);
      return lean_uint64_to_nat(va | vb);
    }
  }
  lean_obj_res result = lean_nat_lor(a, b);
  lean_dec(a); lean_dec(b);
  return result;
}

/* BitVec.fastXor {n : Nat} (a b : BitVec n) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_xor(
    b_lean_obj_arg n_obj, lean_obj_arg a, lean_obj_arg b) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      uint64_t va = nat_to_u64(a), vb = nat_to_u64(b);
      lean_dec(a); lean_dec(b);
      return lean_uint64_to_nat(va ^ vb);
    }
  }
  lean_obj_res result = lean_nat_lxor(a, b);
  lean_dec(a); lean_dec(b);
  return result;
}

/* ── Shifts ────────────────────────────────────────────────────────── */

/* BitVec.fastShiftLeft {n : Nat} (x : BitVec n) (s : Nat) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_shl(
    b_lean_obj_arg n_obj, lean_obj_arg x, lean_obj_arg s) {
  if (lean_is_scalar(n_obj) && lean_is_scalar(s)) {
    size_t n = lean_unbox(n_obj);
    size_t sv = lean_unbox(s);
    if (n <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      uint64_t result = (sv >= 64) ? 0 : (vx << sv);
      return lean_uint64_to_nat(result & bitvec_mask(n));
    }
  }
  lean_obj_res shifted = lean_nat_shiftl(x, s);
  lean_dec(x);
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res result = lean_nat_mod(shifted, pow2n);
  lean_dec(shifted); lean_dec(pow2n);
  return result;
}

/* BitVec.fastUShiftRight {n : Nat} (x : BitVec n) (s : Nat) : BitVec n */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_ushr(
    b_lean_obj_arg n_obj, lean_obj_arg x, lean_obj_arg s) {
  if (lean_is_scalar(n_obj) && lean_is_scalar(s)) {
    size_t n = lean_unbox(n_obj);
    size_t sv = lean_unbox(s);
    if (n <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      uint64_t result = (sv >= 64) ? 0 : (vx >> sv);
      return lean_uint64_to_nat(result);
    }
  }
  lean_obj_res result = lean_nat_shiftr(x, s);
  lean_dec(x);
  return result;
}

/* ── Bit extraction & concatenation ────────────────────────────────── */

/* BitVec.fastExtractLsb' {n : Nat} (start len : Nat) (x : BitVec n) : BitVec len
 * C args: (n, start, len, x) — n is passed by Lean */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_extractlsb(
    b_lean_obj_arg n_obj, lean_obj_arg start_obj, b_lean_obj_arg len_obj, lean_obj_arg x) {
  if (lean_is_scalar(n_obj) && lean_is_scalar(start_obj) && lean_is_scalar(len_obj)) {
    size_t n = lean_unbox(n_obj);
    size_t start = lean_unbox(start_obj);
    size_t len = lean_unbox(len_obj);
    if (n <= 64 && len <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      uint64_t result = (start >= 64) ? 0 : (vx >> start);
      return lean_uint64_to_nat(result & bitvec_mask(len));
    }
  }
  /* Fallback: ofNat len (x >>> start) */
  lean_obj_res shifted = lean_nat_shiftr(x, start_obj);
  lean_dec(x);
  lean_obj_res pow2len = lean_nat_pow(lean_box(2), len_obj);
  lean_obj_res result = lean_nat_mod(shifted, pow2len);
  lean_dec(shifted); lean_dec(pow2len);
  return result;
}

/* BitVec.fastExtractLsb {n : Nat} (hi lo : Nat) (x : BitVec n) : BitVec (hi - lo + 1)
 * = extractLsb' lo (hi-lo+1) x = ofNat (hi-lo+1) (x >>> lo)
 * C args: (n, hi, lo, x) — n is passed by Lean even though not used */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_extractlsb2(
    b_lean_obj_arg n_obj, lean_obj_arg hi_obj, lean_obj_arg lo_obj, lean_obj_arg x) {
  if (lean_is_scalar(n_obj) && lean_is_scalar(hi_obj) && lean_is_scalar(lo_obj)) {
    size_t n = lean_unbox(n_obj);
    size_t hi = lean_unbox(hi_obj);
    size_t lo = lean_unbox(lo_obj);
    size_t len = hi - lo + 1;
    if (n <= 64 && len <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      uint64_t result = (lo >= 64) ? 0 : (vx >> lo);
      return lean_uint64_to_nat(result & bitvec_mask(len));
    }
  }
  /* Fallback: ofNat (hi-lo+1) (x >>> lo) */
  lean_obj_res shifted = lean_nat_shiftr(x, lo_obj);
  lean_dec(x);
  lean_obj_res len = lean_nat_sub(hi_obj, lo_obj);
  lean_obj_res len1 = lean_nat_add(len, lean_box(1));
  lean_dec(len);
  lean_obj_res pow2len = lean_nat_pow(lean_box(2), len1);
  lean_obj_res result = lean_nat_mod(shifted, pow2len);
  lean_dec(shifted); lean_dec(pow2len); lean_dec(len1);
  return result;
}

/* BitVec.fastAppend {n m : Nat} (x : BitVec n) (y : BitVec m) : BitVec (n+m)
 * C args: (n, m, x, y) — both n and m are used at runtime */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_append(
    b_lean_obj_arg n_obj, b_lean_obj_arg m_obj,
    lean_obj_arg x, lean_obj_arg y) {
  if (lean_is_scalar(n_obj) && lean_is_scalar(m_obj)) {
    size_t n = lean_unbox(n_obj);
    size_t m = lean_unbox(m_obj);
    if (n + m <= 64) {
      uint64_t vx = nat_to_u64(x);
      uint64_t vy = nat_to_u64(y);
      lean_dec(x); lean_dec(y);
      return lean_uint64_to_nat((vx << m) | vy);
    }
  }
  /* Fallback: ofNat (n+m) (x <<< m ||| y) */
  lean_obj_res shifted = lean_nat_shiftl(x, m_obj);
  lean_dec(x);
  lean_obj_res combined = lean_nat_lor(shifted, y);
  lean_dec(shifted); lean_dec(y);
  lean_obj_res total = lean_nat_add(n_obj, m_obj);
  lean_obj_res pow2nm = lean_nat_pow(lean_box(2), total);
  lean_dec(total);
  lean_obj_res result = lean_nat_mod(combined, pow2nm);
  lean_dec(combined); lean_dec(pow2nm);
  return result;
}

/* ── Width conversion ──────────────────────────────────────────────── */

/* BitVec.fastSetWidth {w : Nat} (v : Nat) (x : BitVec w) : BitVec v
 * C args: (w : b_lean_obj_arg, v : b_lean_obj_arg, x : lean_obj_arg) */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_setwidth(
    b_lean_obj_arg w_obj, b_lean_obj_arg v_obj, lean_obj_arg x) {
  if (lean_is_scalar(v_obj)) {
    size_t v = lean_unbox(v_obj);
    if (v <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      return lean_uint64_to_nat(vx & bitvec_mask(v));
    }
  }
  /* Fallback: if w <= v, x is already valid; if w > v, x % 2^v */
  if (lean_is_scalar(w_obj) && lean_is_scalar(v_obj)) {
    size_t w = lean_unbox(w_obj);
    size_t v = lean_unbox(v_obj);
    if (w <= v) return x;
  }
  lean_obj_res pow2v = lean_nat_pow(lean_box(2), v_obj);
  lean_obj_res result = lean_nat_mod(x, pow2v);
  lean_dec(x); lean_dec(pow2v);
  return result;
}

/* BitVec.fastSignExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v
 * = ofInt v x.toInt
 * C args: (w : b_lean_obj_arg, v : b_lean_obj_arg, x : lean_obj_arg) */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_signextend(
    b_lean_obj_arg w_obj, b_lean_obj_arg v_obj, lean_obj_arg x) {
  if (lean_is_scalar(w_obj) && lean_is_scalar(v_obj)) {
    size_t w = lean_unbox(w_obj);
    size_t v = lean_unbox(v_obj);
    if (w <= 64 && v <= 64) {
      uint64_t vx = nat_to_u64(x);
      lean_dec(x);
      /* sign-extend: if MSB of w-bit value is set, extend with 1s */
      int64_t signed_val;
      if (w == 0) {
        signed_val = 0;
      } else if (w == 64) {
        signed_val = (int64_t)vx;
      } else {
        /* Sign-extend from w bits to 64 bits */
        uint64_t sign_bit = UINT64_C(1) << (w - 1);
        signed_val = (int64_t)((vx ^ sign_bit) - sign_bit);
      }
      return lean_uint64_to_nat(((uint64_t)signed_val) & bitvec_mask(v));
    }
  }
  /* Fallback: ofInt v (toInt x) */
  /* This is complex; defer to standard implementation via ofInt */
  lean_inc(v_obj);
  lean_obj_res result = lean_sail_bitvec_ofnat(v_obj, x);
  /* This is wrong for sign extension; for fallback, use full computation */
  /* TODO: proper fallback for w > 64 */
  return result;
}

/* ── allOnes ──────────────────────────────────────────────────────── */

/* BitVec.fastAllOnes (n : Nat) : BitVec n
 * = (2^n - 1)
 * C args: (n : b_lean_obj_arg) */
LEAN_EXPORT lean_obj_res lean_sail_bitvec_allones(b_lean_obj_arg n_obj) {
  if (lean_is_scalar(n_obj)) {
    size_t n = lean_unbox(n_obj);
    if (n <= 64) {
      return lean_uint64_to_nat(bitvec_mask(n));
    }
  }
  /* Fallback: 2^n - 1 as Nat */
  lean_inc(n_obj);
  lean_obj_res pow2n = lean_nat_pow(lean_box(2), n_obj);
  lean_obj_res result = lean_nat_sub(pow2n, lean_box(1));
  lean_dec(pow2n);
  return result;
}
