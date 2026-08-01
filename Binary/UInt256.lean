-- `Binary.Fast`, not `Binary.ByteArray`: its `@[csimp]` replacements only reach
-- bodies compiled after them, and this module's codecs must get the fast path.
import Binary.Fast

/-!
# Binary.UInt256

A 256-bit unsigned integer type (the EVM word size), implemented as a wrapper
around Lean core's `BitVec 256` — mirroring how `UInt8` … `UInt64` are
implemented in core — together with the usual fixed-width endianness codec
(32 bytes) and its roundtrip theorems.

Contents:

* the type `UInt256` with `ofNat` / `toNat`, numerals, equality, `Repr`,
  and wrap-around arithmetic / bitwise operations inherited from `BitVec 256`;
* the bridge lemmas `toNat_lt`, `toNat_ofNat`, `toNat_inj`, `ofNat_toNat`;
* the byte codec `toBEBytes` / `toLEBytes` / `ofBEBytes` / `ofLEBytes`
  with the four roundtrip theorems;
* the `ByteArray` codec `toBEByteArray` / `toLEByteArray` / `ofBEByteArray` /
  `ofLEByteArray` with refinement lemmas (agreement with the `List UInt8`
  codec) and the four roundtrip theorems.
-/

namespace Binary

/-- A 256-bit unsigned integer. Wrap-around semantics modulo `2^256`. -/
structure UInt256 where
  /-- The underlying bit vector. -/
  toBitVec : BitVec 256
  deriving DecidableEq

namespace UInt256

/-- Wrap-around constructor from a natural number (`n mod 2^256`). -/
def ofNat (n : Nat) : UInt256 := ⟨BitVec.ofNat 256 n⟩

/-- The value as a natural number. -/
def toNat (x : UInt256) : Nat := x.toBitVec.toNat

/-- The modulus `2^256`. -/
def size : Nat := 2 ^ 256

/-- The byte width of `UInt256` (the EVM word size). -/
abbrev byteSize : Nat := 32

/-! ## Bridge lemmas between `ofNat` and `toNat` -/

theorem toNat_lt (x : UInt256) : x.toNat < size := x.toBitVec.isLt

theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % size :=
  BitVec.toNat_ofNat ..

theorem toNat_inj {x y : UInt256} : x.toNat = y.toNat ↔ x = y := by
  cases x with | mk a =>
  cases y with | mk b =>
  show (a.toNat = b.toNat) ↔ (UInt256.mk a = UInt256.mk b)
  rw [BitVec.toNat_inj]
  constructor
  · intro h; rw [h]
  · intro h; exact congrArg UInt256.toBitVec h

theorem ofNat_toNat (x : UInt256) : ofNat x.toNat = x := by
  apply toNat_inj.mp
  rw [toNat_ofNat, Nat.mod_eq_of_lt x.toNat_lt]

/-- The bound in the `256 ^ byteSize` form used by the byte-codec layer. -/
theorem toNat_lt_256 (x : UInt256) : x.toNat < 256 ^ byteSize := by
  have h := x.toNat_lt
  have e : 256 ^ byteSize = size := by decide
  rwa [e]

/-! ## Basic instances -/

instance : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩
instance : BEq UInt256 := ⟨fun a b => a.toBitVec == b.toBitVec⟩
instance : Repr UInt256 := ⟨fun x _ => repr x.toNat⟩
instance : ToString UInt256 := ⟨fun x => toString x.toNat⟩

/-! ## Wrap-around arithmetic and bitwise operations (inherited from `BitVec 256`) -/

protected def add (a b : UInt256) : UInt256 := ⟨a.toBitVec + b.toBitVec⟩
protected def sub (a b : UInt256) : UInt256 := ⟨a.toBitVec - b.toBitVec⟩
protected def mul (a b : UInt256) : UInt256 := ⟨a.toBitVec * b.toBitVec⟩
protected def and (a b : UInt256) : UInt256 := ⟨a.toBitVec &&& b.toBitVec⟩
protected def or (a b : UInt256) : UInt256 := ⟨a.toBitVec ||| b.toBitVec⟩
protected def xor (a b : UInt256) : UInt256 := ⟨a.toBitVec ^^^ b.toBitVec⟩
protected def not (a : UInt256) : UInt256 := ⟨~~~ a.toBitVec⟩
protected def shiftLeft (a : UInt256) (n : Nat) : UInt256 := ⟨a.toBitVec <<< n⟩
protected def shiftRight (a : UInt256) (n : Nat) : UInt256 := ⟨a.toBitVec >>> n⟩

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : AndOp UInt256 := ⟨UInt256.and⟩
instance : OrOp UInt256 := ⟨UInt256.or⟩
instance : XorOp UInt256 := ⟨UInt256.xor⟩
instance : Complement UInt256 := ⟨UInt256.not⟩
instance : HShiftLeft UInt256 Nat UInt256 := ⟨UInt256.shiftLeft⟩
instance : HShiftRight UInt256 Nat UInt256 := ⟨UInt256.shiftRight⟩

theorem toNat_add (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % size :=
  BitVec.toNat_add ..

theorem toNat_mul (a b : UInt256) : (a * b).toNat = (a.toNat * b.toNat) % size :=
  BitVec.toNat_mul ..

theorem toNat_sub (a b : UInt256) : (a - b).toNat = (size - b.toNat + a.toNat) % size :=
  BitVec.toNat_sub ..

/-! ## Byte codec (`byteSize` bytes) -/

/-- `UInt256` → `byteSize` big-endian bytes. -/
def toBEBytes (x : UInt256) : List UInt8 := encodeBEU byteSize x.toNat

/-- `UInt256` → `byteSize` little-endian bytes. -/
def toLEBytes (x : UInt256) : List UInt8 := encodeLEU byteSize x.toNat

/-- Big-endian bytes → `UInt256` (the decoded value modulo `2^256`). -/
def ofBEBytes (bs : List UInt8) : UInt256 := ofNat (decodeBEU bs)

/-- Little-endian bytes → `UInt256`. -/
def ofLEBytes (bs : List UInt8) : UInt256 := ofNat (decodeLEU bs)

@[simp] theorem length_toBEBytes (x : UInt256) : (toBEBytes x).length = byteSize := by
  simp [toBEBytes]

@[simp] theorem length_toLEBytes (x : UInt256) : (toLEBytes x).length = byteSize := by
  simp [toLEBytes]

/-- **Roundtrip**: encoding a `UInt256` to big-endian bytes and decoding is the identity. -/
theorem ofBEBytes_toBEBytes (x : UInt256) : ofBEBytes (toBEBytes x) = x := by
  have h := decodeBEU_encodeBEU (UInt256.toNat_lt_256 x)
  show ofNat (decodeBEU (encodeBEU byteSize x.toNat)) = x
  rw [h, ofNat_toNat]

/-- **Roundtrip**: encoding a `UInt256` to little-endian bytes and decoding is the identity. -/
theorem ofLEBytes_toLEBytes (x : UInt256) : ofLEBytes (toLEBytes x) = x := by
  have h := decodeLEU_encodeLEU (UInt256.toNat_lt_256 x)
  show ofNat (decodeLEU (encodeLEU byteSize x.toNat)) = x
  rw [h, ofNat_toNat]

/-- Exactly `byteSize` bytes fit, so no truncation happens on the way in:
the decoded word's `toNat` is the byte string's value on the nose. -/
theorem toNat_ofBEBytes_of_length {bs : List UInt8} (h : bs.length = byteSize) :
    (ofBEBytes bs).toNat = decodeBEU bs := by
  show (ofNat (decodeBEU bs)).toNat = decodeBEU bs
  rw [toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb := decodeBEU_lt bs
  rwa [h] at hb

/-- **Roundtrip**: decoding exactly `byteSize` big-endian bytes and re-encoding is the identity. -/
theorem toBEBytes_ofBEBytes {bs : List UInt8} (h : bs.length = byteSize) :
    toBEBytes (ofBEBytes bs) = bs := by
  show encodeBEU byteSize (ofBEBytes bs).toNat = bs
  rw [toNat_ofBEBytes_of_length h, ← h]
  exact encodeBEU_decodeBEU bs

/-- **Roundtrip**: decoding exactly `byteSize` little-endian bytes and re-encoding is the identity. -/
theorem toLEBytes_ofLEBytes {bs : List UInt8} (h : bs.length = byteSize) :
    toLEBytes (ofLEBytes bs) = bs := by
  have e : (ofLEBytes bs).toNat = decodeLEU bs := by
    show (ofNat (decodeLEU bs)).toNat = decodeLEU bs
    rw [toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hb := decodeLEU_lt bs
    rwa [h] at hb
  show encodeLEU byteSize (ofLEBytes bs).toNat = bs
  rw [e, ← h]
  exact encodeLEU_decodeLEU bs

/-! ## `ByteArray` codec (`byteSize` bytes, runtime I/O layer) -/

/-- `UInt256` → `byteSize` big-endian bytes as a `ByteArray`. -/
def toBEByteArray (x : UInt256) : ByteArray := encodeBEBytes byteSize x.toNat

/-- `UInt256` → `byteSize` little-endian bytes as a `ByteArray`. -/
def toLEByteArray (x : UInt256) : ByteArray := encodeLEBytes byteSize x.toNat

/-- Big-endian `ByteArray` → `UInt256` (the decoded value modulo `2^256`). -/
def ofBEByteArray (ba : ByteArray) : UInt256 := ofNat (decodeBEBytes ba)

/-- Little-endian `ByteArray` → `UInt256`. -/
def ofLEByteArray (ba : ByteArray) : UInt256 := ofNat (decodeLEBytes ba)

/-- **Refinement**: the `ByteArray` encoder agrees with the `List UInt8` encoder. -/
theorem toList_toBEByteArray (x : UInt256) :
    (toBEByteArray x).data.toList = toBEBytes x := by
  simp only [toBEByteArray, encodeBEBytes, toBEBytes, List.data_toByteArray,
    List.toList_toArray]

/-- **Refinement**: the `ByteArray` encoder agrees with the `List UInt8` encoder
    (little-endian). -/
theorem toList_toLEByteArray (x : UInt256) :
    (toLEByteArray x).data.toList = toLEBytes x := by
  simp only [toLEByteArray, encodeLEBytes, toLEBytes, List.data_toByteArray,
    List.toList_toArray]

/-- **Refinement**: the `ByteArray` decoder agrees with the `List UInt8` decoder. -/
theorem ofBEByteArray_eq_ofBEBytes (ba : ByteArray) :
    ofBEByteArray ba = ofBEBytes ba.data.toList := rfl

/-- **Refinement**: the `ByteArray` decoder agrees with the `List UInt8` decoder
    (little-endian). -/
theorem ofLEByteArray_eq_ofLEBytes (ba : ByteArray) :
    ofLEByteArray ba = ofLEBytes ba.data.toList := rfl

@[simp] theorem size_toBEByteArray (x : UInt256) : (toBEByteArray x).size = byteSize := by
  simp only [toBEByteArray, size_encodeBEBytes]

@[simp] theorem size_toLEByteArray (x : UInt256) : (toLEByteArray x).size = byteSize := by
  simp only [toLEByteArray, size_encodeLEBytes]

/-- The value decoded from a `byteSize`-wide big-endian `ByteArray`, as a natural. -/
theorem toNat_ofBEByteArray_of_size {ba : ByteArray} (h : ba.size = byteSize) :
    (ofBEByteArray ba).toNat = decodeBEBytes ba := by
  have hlen : ba.data.toList.length = byteSize := by
    rw [← ByteArray.size_eq_toList_length]; exact h
  exact toNat_ofBEBytes_of_length hlen

/-- The value decoded from a `byteSize`-wide little-endian `ByteArray`, as a natural. -/
theorem toNat_ofLEByteArray_of_size {ba : ByteArray} (h : ba.size = byteSize) :
    (ofLEByteArray ba).toNat = decodeLEBytes ba := by
  have hlen : ba.data.toList.length = byteSize := by
    rw [← ByteArray.size_eq_toList_length]; exact h
  have hb := decodeLEU_lt ba.data.toList
  rw [hlen] at hb
  have e : 256 ^ byteSize = size := by decide
  rw [e] at hb
  show (ofNat (decodeLEU ba.data.toList)).toNat = decodeLEU ba.data.toList
  rw [toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- **Roundtrip**: encoding a `UInt256` to a big-endian `ByteArray` and decoding
    is the identity. -/
theorem ofBEByteArray_toBEByteArray (x : UInt256) :
    ofBEByteArray (toBEByteArray x) = x := by
  rw [ofBEByteArray_eq_ofBEBytes, toList_toBEByteArray, ofBEBytes_toBEBytes]

/-- **Roundtrip**: encoding a `UInt256` to a little-endian `ByteArray` and decoding
    is the identity. -/
theorem ofLEByteArray_toLEByteArray (x : UInt256) :
    ofLEByteArray (toLEByteArray x) = x := by
  rw [ofLEByteArray_eq_ofLEBytes, toList_toLEByteArray, ofLEBytes_toLEBytes]

/-- **Roundtrip**: decoding a `byteSize`-wide big-endian `ByteArray` and re-encoding
    is the identity. -/
theorem toBEByteArray_ofBEByteArray {ba : ByteArray} (h : ba.size = byteSize) :
    toBEByteArray (ofBEByteArray ba) = ba := by
  show encodeBEBytes byteSize (ofBEByteArray ba).toNat = ba
  rw [toNat_ofBEByteArray_of_size h, ← h]
  exact encodeBEBytes_decodeBEBytes_size ba

/-- **Roundtrip**: decoding a `byteSize`-wide little-endian `ByteArray` and
    re-encoding is the identity. -/
theorem toLEByteArray_ofLEByteArray {ba : ByteArray} (h : ba.size = byteSize) :
    toLEByteArray (ofLEByteArray ba) = ba := by
  show encodeLEBytes byteSize (ofLEByteArray ba).toNat = ba
  rw [toNat_ofLEByteArray_of_size h, ← h]
  exact encodeLEBytes_decodeLEBytes_size ba

end UInt256

end Binary
