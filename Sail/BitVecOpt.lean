/- Fast BitVec operations that bypass GMP for width ≤ 64.

   Lean 4's BitVec operations go through Nat (GMP bignum) even for 64-bit
   values. This module provides @[extern] C implementations that use native
   uint64_t arithmetic, with @[csimp] theorems to transparently replace the
   standard operations in compiled code. -/

-- Arithmetic
@[extern "lean_sail_bitvec_ofnat"]
def BitVec.fastOfNat (n : Nat) (x : Nat) : BitVec n := BitVec.ofNat n x

@[extern "lean_sail_bitvec_add"]
def BitVec.fastAdd {n : Nat} (a b : BitVec n) : BitVec n := a + b

@[extern "lean_sail_bitvec_sub"]
def BitVec.fastSub {n : Nat} (a b : BitVec n) : BitVec n := a - b

@[extern "lean_sail_bitvec_mul"]
def BitVec.fastMul {n : Nat} (a b : BitVec n) : BitVec n := a * b

-- Int conversion
@[extern "lean_sail_bitvec_ofint"]
def BitVec.fastOfInt (n : Nat) (i : Int) : BitVec n := BitVec.ofInt n i

-- Bitwise
@[extern "lean_sail_bitvec_not"]
def BitVec.fastNot {n : Nat} (x : BitVec n) : BitVec n := ~~~x

@[extern "lean_sail_bitvec_and"]
def BitVec.fastAnd {n : Nat} (a b : BitVec n) : BitVec n := a &&& b

@[extern "lean_sail_bitvec_or"]
def BitVec.fastOr {n : Nat} (a b : BitVec n) : BitVec n := a ||| b

@[extern "lean_sail_bitvec_xor"]
def BitVec.fastXor {n : Nat} (a b : BitVec n) : BitVec n := a ^^^ b

-- Shifts
@[extern "lean_sail_bitvec_shl"]
def BitVec.fastShiftLeft {n : Nat} (x : BitVec n) (s : Nat) : BitVec n := x <<< s

@[extern "lean_sail_bitvec_ushr"]
def BitVec.fastUShiftRight {n : Nat} (x : BitVec n) (s : Nat) : BitVec n := x >>> s

-- Width conversion
@[extern "lean_sail_bitvec_setwidth"]
def BitVec.fastSetWidth {w : Nat} (v : Nat) (x : BitVec w) : BitVec v := BitVec.setWidth v x

@[extern "lean_sail_bitvec_signextend"]
def BitVec.fastSignExtend {w : Nat} (v : Nat) (x : BitVec w) : BitVec v := BitVec.signExtend v x

-- Bit extraction and concatenation
@[extern "lean_sail_bitvec_extractlsb"]
def BitVec.fastExtractLsb' {n : Nat} (start : Nat) (len : Nat) (x : BitVec n) : BitVec len :=
  BitVec.extractLsb' start len x

@[extern "lean_sail_bitvec_append"]
def BitVec.fastAppend {n m : Nat} (x : BitVec n) (y : BitVec m) : BitVec (n + m) :=
  BitVec.append x y

@[extern "lean_sail_bitvec_extractlsb2"]
def BitVec.fastExtractLsb {n : Nat} (hi lo : Nat) (x : BitVec n) : BitVec (hi - lo + 1) :=
  BitVec.extractLsb hi lo x

-- @[csimp] replacement theorems (all rfl since Lean defs are identical)

@[csimp] theorem BitVec.ofNat_eq_fast : @BitVec.ofNat = @BitVec.fastOfNat := by
  funext n x; rfl

@[csimp] theorem BitVec.add_eq_fast : @BitVec.add = @BitVec.fastAdd := by
  funext n a b; rfl

@[csimp] theorem BitVec.sub_eq_fast : @BitVec.sub = @BitVec.fastSub := by
  funext n a b; rfl

@[csimp] theorem BitVec.mul_eq_fast : @BitVec.mul = @BitVec.fastMul := by
  funext n a b; rfl

@[csimp] theorem BitVec.ofInt_eq_fast : @BitVec.ofInt = @BitVec.fastOfInt := by
  funext n i; rfl

@[csimp] theorem BitVec.not_eq_fast : @BitVec.not = @BitVec.fastNot := by
  funext n x; rfl

@[csimp] theorem BitVec.and_eq_fast : @BitVec.and = @BitVec.fastAnd := by
  funext n a b; rfl

@[csimp] theorem BitVec.or_eq_fast : @BitVec.or = @BitVec.fastOr := by
  funext n a b; rfl

@[csimp] theorem BitVec.xor_eq_fast : @BitVec.xor = @BitVec.fastXor := by
  funext n a b; rfl

@[csimp] theorem BitVec.shiftLeft_eq_fast : @BitVec.shiftLeft = @BitVec.fastShiftLeft := by
  funext n x s; rfl

@[csimp] theorem BitVec.ushiftRight_eq_fast : @BitVec.ushiftRight = @BitVec.fastUShiftRight := by
  funext n x s; rfl

@[csimp] theorem BitVec.setWidth_eq_fast : @BitVec.setWidth = @BitVec.fastSetWidth := by
  funext w v x; rfl

@[csimp] theorem BitVec.signExtend_eq_fast : @BitVec.signExtend = @BitVec.fastSignExtend := by
  funext w v x; rfl

@[csimp] theorem BitVec.extractLsb'_eq_fast : @BitVec.extractLsb' = @BitVec.fastExtractLsb' := by
  funext n start len x; rfl

@[csimp] theorem BitVec.extractLsb_eq_fast : @BitVec.extractLsb = @BitVec.fastExtractLsb := by
  funext n hi lo x; rfl

@[csimp] theorem BitVec.append_eq_fast : @BitVec.append = @BitVec.fastAppend := by
  funext n m x y; rfl

-- Instance-level replacements: the compiler resolves operators (a - b, a + b, ~~~a)
-- through typeclass instances (BitVec.instSub, etc.) and @[csimp] for the underlying
-- functions (BitVec.sub, etc.) doesn't catch these. We need instance-level constants.
def BitVec.fastInstSub {n : Nat} : Sub (BitVec n) := ⟨BitVec.fastSub⟩
def BitVec.fastInstAdd {n : Nat} : Add (BitVec n) := ⟨BitVec.fastAdd⟩
def BitVec.fastInstMul {n : Nat} : Mul (BitVec n) := ⟨BitVec.fastMul⟩
def BitVec.fastInstComplement {w : Nat} : Complement (BitVec w) := ⟨BitVec.fastNot⟩

@[csimp] theorem BitVec.instSub_eq_fast : @BitVec.instSub = @BitVec.fastInstSub := by
  funext n; rfl

@[csimp] theorem BitVec.instAdd_eq_fast : @BitVec.instAdd = @BitVec.fastInstAdd := by
  funext n; rfl

@[csimp] theorem BitVec.instMul_eq_fast : @BitVec.instMul = @BitVec.fastInstMul := by
  funext n; rfl

@[csimp] theorem BitVec.instComplement_eq_fast : @BitVec.instComplement = @BitVec.fastInstComplement := by
  funext w; rfl

-- Shift instances
def BitVec.fastInstHShiftLeftNat {w : Nat} : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.fastShiftLeft⟩
def BitVec.fastInstHShiftRightNat {w : Nat} : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.fastUShiftRight⟩

@[csimp] theorem BitVec.instHShiftLeftNat_eq_fast : @BitVec.instHShiftLeftNat = @BitVec.fastInstHShiftLeftNat := by
  funext w; rfl

@[csimp] theorem BitVec.instHShiftRightNat_eq_fast : @BitVec.instHShiftRightNat = @BitVec.fastInstHShiftRightNat := by
  funext w; rfl

-- BitVec-BitVec shift instances
def BitVec.fastInstHShiftLeft {m n : Nat} : HShiftLeft (BitVec m) (BitVec n) (BitVec m) :=
  ⟨fun x y => BitVec.fastShiftLeft x y.toNat⟩
def BitVec.fastInstHShiftRight {m n : Nat} : HShiftRight (BitVec m) (BitVec n) (BitVec m) :=
  ⟨fun x y => BitVec.fastUShiftRight x y.toNat⟩

@[csimp] theorem BitVec.instHShiftLeft_eq_fast : @BitVec.instHShiftLeft = @BitVec.fastInstHShiftLeft := by
  funext m n; rfl

@[csimp] theorem BitVec.instHShiftRight_eq_fast : @BitVec.instHShiftRight = @BitVec.fastInstHShiftRight := by
  funext m n; rfl

-- Append instance
def BitVec.fastInstHAppendHAddNat {w v : Nat} : HAppend (BitVec w) (BitVec v) (BitVec (w + v)) :=
  ⟨BitVec.fastAppend⟩

@[csimp] theorem BitVec.instHAppendHAddNat_eq_fast : @BitVec.instHAppendHAddNat = @BitVec.fastInstHAppendHAddNat := by
  funext w v; rfl

-- allOnes: defined as (2^n - 1), internally uses slow BitVec.ofNat
@[extern "lean_sail_bitvec_allones"]
def BitVec.fastAllOnes (n : Nat) : BitVec n := BitVec.allOnes n

@[csimp] theorem BitVec.allOnes_eq_fast : @BitVec.allOnes = @BitVec.fastAllOnes := by
  funext n; rfl
