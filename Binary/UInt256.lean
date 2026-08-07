-- `Binary.Fast`, not `Binary.ByteArray`: its `@[csimp]` replacements only reach
-- bodies compiled after them, and this module's codecs must get the fast path.
import Binary.Fast

/-!
# Binary.UInt256

A 256-bit unsigned integer type (the EVM word size), held as four `UInt64`
limbs, together with the usual fixed-width endianness codec (32 bytes) and its
roundtrip theorems.

`BitVec 256` is the obvious representation and was the one used here, but it
is `Fin (2 ^ 256)`, which is a `Nat`, which above `2 ^ 63` is a heap GMP
integer — so every operation on a word allocates, the byte codec most of all.
Four limbs are one heap object with four unboxed scalars.  `toBitVec` is still
here, now computed rather than stored, and every theorem is still stated
through it or through `toNat`.

Contents:

* the type `UInt256` with `toBitVec` / `ofBitVec` and their roundtrips,
  `ofNat` / `toNat`, numerals, equality, `Repr`, and wrap-around arithmetic /
  bitwise operations defined through the bit vector;
* the bridge lemmas `toNat_lt`, `toNat_ofNat`, `toNat_inj`, `ofNat_toNat`,
  and the two limb decompositions — `toNat_eq_limbs` for building a value out
  of limbs, `toNat_window_l0` … `l3` for reading them back out;
* the byte codec `toBEBytes` / `toLEBytes` / `ofBEBytes` / `ofLEBytes`
  with the four roundtrip theorems;
* the `ByteArray` codec `toBEByteArray` / `toLEByteArray` / `ofBEByteArray` /
  `ofLEByteArray` with refinement lemmas (agreement with the `List UInt8`
  codec) and the four roundtrip theorems;
* and the two limb-direct entry points that make the representation pay —
  `toBEByteArrayFast`, swapped in for `toBEByteArray` by `@[csimp]`, and
  `ofBEByteArrayAt` for reading a word at a known offset, with
  `toNat_ofBEByteArrayAt` as its agreement.  Neither builds a `Nat`; asking
  either result for its `toNat` gives the cost straight back.
-/

namespace Binary

/-- A 256-bit unsigned integer, as four 64-bit limbs, most significant first.

`BitVec 256` would be the obvious field, and was: it is `Fin (2 ^ 256)`, which
is a `Nat`, which above `2 ^ 63` is a heap GMP integer.  Every operation on
one — including each step of the byte codec — then allocates.  Four `UInt64`s
are one heap object with four unboxed scalars, and reading a 32-byte word into
them costs 29 ns where the `Nat` costs 908.

`toBitVec` below is the same bit vector, now computed rather than stored: it
is the *denotation*, and every theorem in this file is still stated through
it or through `toNat`.  Nothing in the codec calls it. -/
structure UInt256 where
  /-- Bits 255…192. -/
  l0 : UInt64
  /-- Bits 191…128. -/
  l1 : UInt64
  /-- Bits 127…64. -/
  l2 : UInt64
  /-- Bits 63…0. -/
  l3 : UInt64
  deriving DecidableEq

namespace UInt256

/-- The bit vector a word denotes — the four limbs concatenated. -/
def toBitVec (x : UInt256) : BitVec 256 :=
  x.l0.toBitVec ++ x.l1.toBitVec ++ x.l2.toBitVec ++ x.l3.toBitVec

/-- Split a bit vector into limbs.  Inverse to `toBitVec`. -/
def ofBitVec (v : BitVec 256) : UInt256 :=
  ⟨⟨v.extractLsb' 192 64⟩, ⟨v.extractLsb' 128 64⟩, ⟨v.extractLsb' 64 64⟩, ⟨v.extractLsb' 0 64⟩⟩

@[simp] theorem toBitVec_ofBitVec (v : BitVec 256) : (ofBitVec v).toBitVec = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [toBitVec, ofBitVec, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have h4 : i - 64 - 64 - 64 < 64 := by omega
  by_cases h1 : i < 64
  · simp [h1]
  · by_cases h2 : i - 64 < 64
    · rw [if_neg h1, if_pos h2, show (64 : Nat) + (i - 64) = i from by omega]
      simp [h2]
    · by_cases h3 : i - 64 - 64 < 64
      · rw [if_neg h1, if_neg h2, if_pos h3,
          show (128 : Nat) + (i - 64 - 64) = i from by omega]
        simp [h3]
      · rw [if_neg h1, if_neg h2, if_neg h3,
          show (192 : Nat) + (i - 64 - 64 - 64) = i from by omega]
        simp [h4]

/-! Reading a limb back out of the concatenation.  Core has no
`extractLsb'`-of-`append` lemma, so each of the four is the same `getLsbD`
argument: peel the three `append`s, then rewrite the index. -/

private theorem getLsbD_l0 (a b c d : BitVec 64) {i : Nat} (hi : i < 64) :
    (a ++ b ++ c ++ d).getLsbD (192 + i) = a.getLsbD i := by
  simp only [BitVec.getLsbD_append]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 192 + i - 64 - 64 - 64 = i from by omega]

private theorem getLsbD_l1 (a b c d : BitVec 64) {i : Nat} (hi : i < 64) :
    (a ++ b ++ c ++ d).getLsbD (128 + i) = b.getLsbD i := by
  simp only [BitVec.getLsbD_append]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 128 + i - 64 - 64 = i from by omega]

private theorem getLsbD_l2 (a b c d : BitVec 64) {i : Nat} (hi : i < 64) :
    (a ++ b ++ c ++ d).getLsbD (64 + i) = c.getLsbD i := by
  simp only [BitVec.getLsbD_append]
  rw [if_neg (by omega), if_pos (by omega), show 64 + i - 64 = i from by omega]

private theorem getLsbD_l3 (a b c d : BitVec 64) {i : Nat} (hi : i < 64) :
    (a ++ b ++ c ++ d).getLsbD i = d.getLsbD i := by
  simp only [BitVec.getLsbD_append]
  rw [if_pos (by omega)]

theorem ofBitVec_toBitVec (x : UInt256) : ofBitVec x.toBitVec = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [ofBitVec, toBitVec, UInt256.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt64.toBitVec_inj.1 <;>
    (apply BitVec.eq_of_getLsbD_eq; intro i hi;
     simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and])
  · exact getLsbD_l0 _ _ _ _ hi
  · exact getLsbD_l1 _ _ _ _ hi
  · exact getLsbD_l2 _ _ _ _ hi
  · simpa using getLsbD_l3 a.toBitVec b.toBitVec c.toBitVec d.toBitVec hi

/-- Wrap-around constructor from a natural number (`n mod 2^256`). -/
def ofNat (n : Nat) : UInt256 := ofBitVec (BitVec.ofNat 256 n)

/-- The value as a natural number. -/
def toNat (x : UInt256) : Nat := x.toBitVec.toNat

/-- The modulus `2^256`. -/
def size : Nat := 2 ^ 256

/-- The byte width of `UInt256` (the EVM word size). -/
abbrev byteSize : Nat := 32

/-! ## Bridge lemmas between `ofNat` and `toNat` -/

theorem toNat_lt (x : UInt256) : x.toNat < size := x.toBitVec.isLt

theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % size := by
  rw [toNat, ofNat, toBitVec_ofBitVec]
  exact BitVec.toNat_ofNat ..

theorem toNat_inj {x y : UInt256} : x.toNat = y.toNat ↔ x = y := by
  constructor
  · intro h
    have hb : x.toBitVec = y.toBitVec := BitVec.toNat_inj.mp h
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y, hb]
  · intro h; rw [h]

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
instance : BEq UInt256 := ⟨fun a b => a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3⟩
instance : Repr UInt256 := ⟨fun x _ => repr x.toNat⟩
instance : ToString UInt256 := ⟨fun x => toString x.toNat⟩

/-! ## Wrap-around arithmetic and bitwise operations (inherited from `BitVec 256`) -/

protected def add (a b : UInt256) : UInt256 := ofBitVec (a.toBitVec + b.toBitVec)
protected def sub (a b : UInt256) : UInt256 := ofBitVec (a.toBitVec - b.toBitVec)
protected def mul (a b : UInt256) : UInt256 := ofBitVec (a.toBitVec * b.toBitVec)
protected def and (a b : UInt256) : UInt256 := ofBitVec (a.toBitVec &&& b.toBitVec)
protected def or (a b : UInt256) : UInt256 := ofBitVec (a.toBitVec ||| b.toBitVec)
protected def xor (a b : UInt256) : UInt256 := ofBitVec (a.toBitVec ^^^ b.toBitVec)
protected def not (a : UInt256) : UInt256 := ofBitVec (~~~ a.toBitVec)
protected def shiftLeft (a : UInt256) (n : Nat) : UInt256 := ofBitVec (a.toBitVec <<< n)
protected def shiftRight (a : UInt256) (n : Nat) : UInt256 := ofBitVec (a.toBitVec >>> n)

/-! ### the bitwise operations, limb-native

The definitions above are the specification — a word operation *means* the
`BitVec 256` one.  They were also how it got computed, and that is the bignum
back: `toBitVec` rebuilds a 256-bit `BitVec`, which is a `Fin (2 ^ 256)`, which
is a `Nat`, so a heap GMP integer above `2 ^ 63`; the operation runs on that;
`ofBitVec` takes it apart again.  The limbs were paying for storage only.

Bitwise operations are exactly limbwise — `BitVec.and_append` and its siblings
say the concatenation distributes — so no carry reasoning is needed.
`@[csimp]` redirects code generation and leaves the definitions, and every
theorem about them, alone.

Everything below is limb-native except the shifts, which stay on the `BitVec`
route deliberately: the shift amount is a runtime `Nat`, so a limb version wants
case analysis on `n / 64` and `n % 64` plus the `UInt64 >>> 64` boundary —
bit-level reasoning rather than the arithmetic the other six needed — and
nothing depends on them yet.  Measured at ~2750 ns an operation against ~14 for
the bitwise three, if that changes.

`bv_decide` would discharge any of these in a line and must not be used: it
emits a per-proof native axiom, which would land in the trust base of everything
downstream.  These proofs need `propext` and `Quot.sound`, and `Classical.choice`
for `not`, `sub` and `mul`. -/

protected def andFast (a b : UInt256) : UInt256 :=
  ⟨a.l0 &&& b.l0, a.l1 &&& b.l1, a.l2 &&& b.l2, a.l3 &&& b.l3⟩

protected def orFast (a b : UInt256) : UInt256 :=
  ⟨a.l0 ||| b.l0, a.l1 ||| b.l1, a.l2 ||| b.l2, a.l3 ||| b.l3⟩

protected def xorFast (a b : UInt256) : UInt256 :=
  ⟨a.l0 ^^^ b.l0, a.l1 ^^^ b.l1, a.l2 ^^^ b.l2, a.l3 ^^^ b.l3⟩

protected def notFast (a : UInt256) : UInt256 :=
  ⟨~~~a.l0, ~~~a.l1, ~~~a.l2, ~~~a.l3⟩

/-- Every swap below is this step: the fast form denotes the same bit vector,
so `ofBitVec` of that bit vector *is* the fast form. -/
private theorem ofBitVec_eq {x : UInt256} {v : BitVec 256} (h : v = x.toBitVec) :
    ofBitVec v = x := by rw [h, ofBitVec_toBitVec]

@[csimp] theorem and_eq_andFast : @UInt256.and = @UInt256.andFast := by
  funext a b
  exact ofBitVec_eq (by
    simp only [toBitVec, UInt256.andFast, UInt64.toBitVec_and, ← BitVec.and_append])

@[csimp] theorem or_eq_orFast : @UInt256.or = @UInt256.orFast := by
  funext a b
  exact ofBitVec_eq (by
    simp only [toBitVec, UInt256.orFast, UInt64.toBitVec_or, ← BitVec.or_append])

@[csimp] theorem xor_eq_xorFast : @UInt256.xor = @UInt256.xorFast := by
  funext a b
  exact ofBitVec_eq (by
    simp only [toBitVec, UInt256.xorFast, UInt64.toBitVec_xor, ← BitVec.xor_append])

@[csimp] theorem not_eq_notFast : @UInt256.not = @UInt256.notFast := by
  funext a
  exact ofBitVec_eq (by
    simp only [toBitVec, UInt256.notFast, UInt64.toBitVec_not, ← BitVec.not_append])

/-- The value in terms of its limbs.  `BitVec.toNat_append` gives the `|||`
form; each `or` is an `add` because the lower part is below the shift. -/
theorem toNat_eq_limbs (x : UInt256) :
    x.toNat = ((x.l0.toNat * 2 ^ 64 + x.l1.toNat) * 2 ^ 64 + x.l2.toNat) * 2 ^ 64
      + x.l3.toNat := by
  have h1 := x.l1.toBitVec.isLt
  have h2 := x.l2.toBitVec.isLt
  have h3 := x.l3.toBitVec.isLt
  simp only [toNat, toBitVec, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using h3),
    ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using h2),
    ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using h1)]
  simp only [Nat.shiftLeft_eq]
  rfl

/-! ### addition, limb-native

`add` cannot be done by a distribution lemma the way the bitwise four were: it
carries across limbs.  So the schoolbook chain, least significant limb first,
with the carry out of each step detected by wraparound — `x + y` wraps iff the
sum landed below `x`, and adding the incoming carry can wrap once more.

The specification stays `ofBitVec (a.toBitVec + b.toBitVec)`; the swap is proved
through `toNat`, where `toNat_add` already says what the specification computes
and `toNat_eq_limbs` says what the limbs denote.  `omega` does the rest, one
limb at a time. -/

/-- One limb of the chain: `x + y + c`, and the carry out.  `x + y` wraps iff
the sum landed below `x`, and adding the incoming carry can wrap once more; at
most one of the two happens, so a single `||` is the carry. -/
@[inline] private def addLimb (x y c : UInt64) : UInt64 × UInt64 :=
  let s := x + y
  let t := s + c
  (t, if s < x || t < s then 1 else 0)

/-- The limb step is exactly division with remainder by `2 ^ 64`: the low half
is the sum modulo, the carry is the quotient. -/
private theorem addLimb_spec (x y c : UInt64) (hc : c.toNat ≤ 1) :
    (addLimb x y c).1.toNat + 2 ^ 64 * (addLimb x y c).2.toNat
      = x.toNat + y.toNat + c.toNat := by
  -- in `2 ^ 64` form, not `UInt64.size`: `omega` treats the latter as opaque
  have hx : x.toNat < 2 ^ 64 := UInt64.toNat_lt x
  have hy : y.toNat < 2 ^ 64 := UInt64.toNat_lt y
  have hlow : (addLimb x y c).1.toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ 64 := by
    simp only [addLimb, UInt64.toNat_add]
    omega
  have hcarry : (addLimb x y c).2.toNat = (x.toNat + y.toNat + c.toNat) / 2 ^ 64 := by
    simp only [addLimb]
    split
    · next h =>
        simp only [Bool.or_eq_true, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
          decide_eq_true_eq] at h
        simp only [UInt64.toNat_ofNat]
        omega
    · next h =>
        simp only [Bool.or_eq_true, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
          decide_eq_true_eq, not_or, Nat.not_lt] at h
        simp only [UInt64.toNat_ofNat]
        omega
  rw [hlow, hcarry]
  omega

/-- Everything the chain needs of one step, in one place: the pair is division
with remainder by `2 ^ 64` — low half the remainder, carry the quotient — the
carry is a bit, which is what lets the next step apply, and the low half is
bounded, which `omega` cannot read off the type.  Bundled so the caller never
has to spell the nested `addLimb` terms out. -/
private theorem addLimb_ok (x y c : UInt64) (hc : c.toNat ≤ 1) :
    (addLimb x y c).1.toNat + 2 ^ 64 * (addLimb x y c).2.toNat
        = x.toNat + y.toNat + c.toNat
      ∧ (addLimb x y c).2.toNat ≤ 1
      ∧ (addLimb x y c).1.toNat < 2 ^ 64 :=
  ⟨addLimb_spec x y c hc, by simp only [addLimb]; split <;> simp, UInt64.toNat_lt _⟩

protected def addFast (a b : UInt256) : UInt256 :=
  let p3 := addLimb a.l3 b.l3 0
  let p2 := addLimb a.l2 b.l2 p3.2
  let p1 := addLimb a.l1 b.l1 p2.2
  let p0 := addLimb a.l0 b.l0 p1.2
  ⟨p0.1, p1.1, p2.1, p3.1⟩

/-- What the specification computes, spelled out here rather than taken from
`toNat_add`: that one is stated over `+`, so it lives below the `Add` instance,
and the `@[csimp]` has to sit above the instance to reach it. -/
private theorem toNat_add_def (a b : UInt256) :
    (UInt256.add a b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  rw [UInt256.add, toNat, toBitVec_ofBitVec]; exact BitVec.toNat_add ..

@[csimp] theorem add_eq_addFast : @UInt256.add = @UInt256.addFast := by
  funext a b
  rw [← toNat_inj]
  -- each step's incoming carry is inferred from the previous step's bound
  have h3 := addLimb_ok a.l3 b.l3 0 (by simp)
  have h2 := addLimb_ok a.l2 b.l2 _ h3.2.1
  have h1 := addLimb_ok a.l1 b.l1 _ h2.2.1
  have h0 := addLimb_ok a.l0 b.l0 _ h1.2.1
  -- without this the chain starts from an opaque `UInt64.toNat 0`
  simp only [show (0 : UInt64).toNat = 0 from rfl] at h3
  -- `omega` cannot get a limb's bound from its type
  have ba0 := UInt64.toNat_lt a.l0; have ba1 := UInt64.toNat_lt a.l1
  have ba2 := UInt64.toNat_lt a.l2; have ba3 := UInt64.toNat_lt a.l3
  have bb0 := UInt64.toNat_lt b.l0; have bb1 := UInt64.toNat_lt b.l1
  have bb2 := UInt64.toNat_lt b.l2; have bb3 := UInt64.toNat_lt b.l3
  rw [toNat_add_def, UInt256.addFast]
  simp only [toNat_eq_limbs]
  omega

/-- `a - b` as `a + ~b + 1`, the two's-complement identity, so subtraction
reuses the limb adder rather than needing a borrow chain of its own.  Two adds
and a complement is more work than a dedicated chain would be, and a great deal
less than rebuilding a bignum. -/
protected def subFast (a b : UInt256) : UInt256 :=
  UInt256.addFast (UInt256.addFast a (UInt256.notFast b)) ⟨0, 0, 0, 1⟩

@[csimp] theorem sub_eq_subFast : @UInt256.sub = @UInt256.subFast := by
  funext a b
  rw [← toNat_inj]
  have hb : b.toNat < 2 ^ 256 := b.toNat_lt
  have hnot : (UInt256.notFast b).toNat = 2 ^ 256 - 1 - b.toNat := by
    rw [← not_eq_notFast, UInt256.not, toNat, toBitVec_ofBitVec]
    exact BitVec.toNat_not
  have hone : (⟨0, 0, 0, 1⟩ : UInt256).toNat = 1 := by rw [toNat_eq_limbs]; rfl
  have hsub : (UInt256.sub a b).toNat = (2 ^ 256 - b.toNat + a.toNat) % 2 ^ 256 := by
    rw [UInt256.sub, toNat, toBitVec_ofBitVec]; exact BitVec.toNat_sub ..
  have hadd : ∀ x y : UInt256,
      (UInt256.addFast x y).toNat = (x.toNat + y.toNat) % 2 ^ 256 := fun x y => by
    rw [← add_eq_addFast]; exact toNat_add_def x y
  rw [hsub, UInt256.subFast, hadd, hadd, hnot, hone]
  omega

/-- The full `64×64 → 128` product, as `(low, high)` — low half first, the same
convention as `addLimb` and `acc`, so the spec equations all read
`.1 + 2 ^ 64 * .2`. -/
@[inline] private def mul64 (x y : UInt64) : UInt64 × UInt64 :=
  let b : UInt64 := 4294967296
  let xl := x % b; let xh := x / b
  let yl := y % b; let yh := y / b
  let ll := xl * yl
  let lh := xl * yh
  let hl := xh * yl
  let t := ll / b + lh % b + hl % b
  (t % b * b + ll % b, xh * yh + lh / b + hl / b + t / b)

/-- The product is `low + 2 ^ 64 * high`, and the low half is a word — the
same bundle shape as `addLimb_ok`, so the capstone proof never spells the
`mul64` terms out to state a bound. -/
private theorem mul64_spec (x y : UInt64) :
    (mul64 x y).1.toNat + 2 ^ 64 * (mul64 x y).2.toNat = x.toNat * y.toNat
      ∧ (mul64 x y).1.toNat < 2 ^ 64 := by
  refine ⟨?_, UInt64.toNat_lt _⟩
  have hb : (4294967296 : UInt64).toNat = 2 ^ 32 := rfl
  have hx := UInt64.toNat_lt x
  have hy := UInt64.toNat_lt y
  -- tight bounds on the half-products: the high half fits only just
  have q1 : x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : x.toNat % 2 ^ 32 * (y.toNat / 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q3 : x.toNat / 2 ^ 32 * (y.toNat % 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q4 : x.toNat / 2 ^ 32 * (y.toNat / 2 ^ 32) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  -- the expansion `omega` cannot do: variable times variable, and no `ring` here
  have hexp : ∀ xh xl yh yl : Nat,
      (xh * 2 ^ 32 + xl) * (yh * 2 ^ 32 + yl)
        = xh * yh * 2 ^ 64 + (xh * yl + xl * yh) * 2 ^ 32 + xl * yl := by
    intro xh xl yh yl
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  have hxy := hexp (x.toNat / 2 ^ 32) (x.toNat % 2 ^ 32) (y.toNat / 2 ^ 32) (y.toNat % 2 ^ 32)
  rw [Nat.div_add_mod', Nat.div_add_mod'] at hxy
  simp only [mul64, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div,
    UInt64.toNat_mod, hb]
  omega

/-- One accumulation step: add `v` into the running low half, counting the
wraps.  The carry is compared out, not branched on — an `if` here would put the
pair constructor under a branch and the compiler then boxes both halves through
the join point, a heap allocation per step. -/
@[inline] private def acc (s : UInt64 × UInt64) (v : UInt64) : UInt64 × UInt64 :=
  let t := s.1 + v
  (t, s.2 + (decide (t < s.1)).toUInt64)

/-- `acc` preserves the running value `low + 2 ^ 64 * count`. -/
private theorem acc_ok (s : UInt64 × UInt64) (v : UInt64) (hs : s.2.toNat < 2 ^ 64 - 1) :
    (acc s v).1.toNat + 2 ^ 64 * (acc s v).2.toNat
        = s.1.toNat + 2 ^ 64 * s.2.toNat + v.toNat
      ∧ (acc s v).2.toNat ≤ s.2.toNat + 1 := by
  have hv := UInt64.toNat_lt v
  have h1 := UInt64.toNat_lt s.1
  by_cases h : s.1 + v < s.1
  · have hb : ((decide (s.1 + v < s.1)).toUInt64).toNat = 1 := by rw [decide_eq_true h]; rfl
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    refine ⟨?_, ?_⟩ <;> simp only [acc, UInt64.toNat_add, hb] <;> omega
  · have hb : ((decide (s.1 + v < s.1)).toUInt64).toNat = 0 := by rw [decide_eq_false h]; rfl
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    refine ⟨?_, ?_⟩ <;> simp only [acc, UInt64.toNat_add, hb] <;> omega

/-- Folding `acc` over a list of addends preserves the running value and grows
the carry count by at most one a step.  The list is a proof device only: the
multiplier's unrolled `acc (acc (s, 0) v₁) v₂` *is* `[v₁, v₂].foldl acc (s, 0)`
definitionally, so nothing is allocated at runtime. -/
private theorem accs_ok : ∀ (vs : List UInt64) (s : UInt64 × UInt64),
    s.2.toNat + vs.length < 2 ^ 64 - 1 →
    (vs.foldl acc s).1.toNat + 2 ^ 64 * (vs.foldl acc s).2.toNat
        = s.1.toNat + 2 ^ 64 * s.2.toNat + (vs.map UInt64.toNat).sum
      ∧ (vs.foldl acc s).2.toNat ≤ s.2.toNat + vs.length
  | [], s, _ => by simp
  | v :: vs, s, h => by
      have h1 := acc_ok s v (by simp at h; omega)
      have h2 := accs_ok vs (acc s v) (by simp at h; omega)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

/-- The two accumulation widths the multiplier uses, named so the assembly
proof and the definition mention the same term.  Each is `accs_ok` at a literal
list, which is definitionally the unrolled fold. -/
@[inline] private def acc2 (s v₁ v₂ : UInt64) : UInt64 × UInt64 :=
  acc (acc (s, 0) v₁) v₂

@[inline] private def acc5 (s v₁ v₂ v₃ v₄ v₅ : UInt64) : UInt64 × UInt64 :=
  acc (acc (acc (acc (acc (s, 0) v₁) v₂) v₃) v₄) v₅

/-- Value equation and the word bound on the low half, bundled like
`addLimb_ok` so the capstone proof never spells the nested terms out. -/
private theorem acc2_ok (s v₁ v₂ : UInt64) :
    (acc2 s v₁ v₂).1.toNat + 2 ^ 64 * (acc2 s v₁ v₂).2.toNat
        = s.toNat + (v₁.toNat + v₂.toNat)
      ∧ (acc2 s v₁ v₂).1.toNat < 2 ^ 64 :=
  ⟨by simpa [acc2] using (accs_ok [v₁, v₂] (s, 0) (by simp)).1, UInt64.toNat_lt _⟩

private theorem acc5_ok (s v₁ v₂ v₃ v₄ v₅ : UInt64) :
    (acc5 s v₁ v₂ v₃ v₄ v₅).1.toNat + 2 ^ 64 * (acc5 s v₁ v₂ v₃ v₄ v₅).2.toNat
        = s.toNat + (v₁.toNat + (v₂.toNat + (v₃.toNat + (v₄.toNat + v₅.toNat))))
      ∧ (acc5 s v₁ v₂ v₃ v₄ v₅).1.toNat < 2 ^ 64 :=
  ⟨by simpa [acc5] using (accs_ok [v₁, v₂, v₃, v₄, v₅] (s, 0) (by simp)).1,
   UInt64.toNat_lt _⟩

/-- Six full limb products accumulated into three weights, and a fourth row of
wrapping products.  Products of total weight four and above are dropped: they
are multiples of `2 ^ 256`.  In the weight-3 row even the carries are weight
four, so its four products need only their low halves — the wrapping `*` — and
the whole row is a plain wrapping sum. -/
protected def mulFast (a b : UInt256) : UInt256 :=
  -- limbs least-significant first
  let A0 := a.l3; let A1 := a.l2; let A2 := a.l1; let A3 := a.l0
  let B0 := b.l3; let B1 := b.l2; let B2 := b.l1; let B3 := b.l0
  let p00 := mul64 A0 B0
  let p01 := mul64 A0 B1; let p10 := mul64 A1 B0
  let p02 := mul64 A0 B2; let p11 := mul64 A1 B1; let p20 := mul64 A2 B0
  let w1 := acc2 p00.2 p01.1 p10.1
  let w2 := acc5 w1.2 p01.2 p10.2 p02.1 p11.1 p20.1
  let w3 := w2.2 + p02.2 + p11.2 + p20.2 + A0 * B3 + A1 * B2 + A2 * B1 + A3 * B0
  ⟨w3, w2.1, w1.1, p00.1⟩

/-- What the specification computes, as `toNat_add_def` does for addition. -/
private theorem toNat_mul_def (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  rw [UInt256.mul, toNat, toBitVec_ofBitVec]; exact BitVec.toNat_mul ..

@[csimp] theorem mul_eq_mulFast : @UInt256.mul = @UInt256.mulFast := by
  funext a b
  rw [← toNat_inj]
  -- the six full limb products (the weight-3 row is wrapping `*`, handled below)
  have m00 := mul64_spec a.l3 b.l3
  have m01 := mul64_spec a.l3 b.l2
  have m10 := mul64_spec a.l2 b.l3
  have m02 := mul64_spec a.l3 b.l1
  have m11 := mul64_spec a.l2 b.l2
  have m20 := mul64_spec a.l1 b.l3
  -- the two carry-counted accumulations, values and bounds bundled
  have hw1 := acc2_ok (mul64 a.l3 b.l3).2 (mul64 a.l3 b.l2).1 (mul64 a.l2 b.l3).1
  have hw2 := acc5_ok (acc2 (mul64 a.l3 b.l3).2 (mul64 a.l3 b.l2).1 (mul64 a.l2 b.l3).1).2
    (mul64 a.l3 b.l2).2 (mul64 a.l2 b.l3).2 (mul64 a.l3 b.l1).1 (mul64 a.l2 b.l2).1
    (mul64 a.l1 b.l3).1
  -- the sixteen-term expansion: `omega` cannot multiply two variables, and the
  -- terms of weight four and above are the multiple of `2 ^ 256` that vanishes
  have hexp : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Nat,
      (((a0 * 2^64 + a1) * 2^64 + a2) * 2^64 + a3) * (((b0 * 2^64 + b1) * 2^64 + b2) * 2^64 + b3)
        = (a3*b3 + (a3*b2 + a2*b3) * 2^64 + (a3*b1 + a2*b2 + a1*b3) * 2^128
           + (a3*b0 + a2*b1 + a1*b2 + a0*b3) * 2^192)
          + 2^256 * ((a2*b0 + a1*b1 + a0*b2) + (a1*b0 + a0*b1) * 2^64 + a0*b0 * 2^128) := by
    intro a0 a1 a2 a3 b0 b1 b2 b3
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  have hab := hexp a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat
    b.l0.toNat b.l1.toNat b.l2.toNat b.l3.toNat
  rw [toNat_mul_def, UInt256.mulFast]
  -- `toNat_add`/`toNat_mul` turn the wrapping weight-3 row into `%`-arithmetic
  simp only [toNat_eq_limbs, UInt64.toNat_add, UInt64.toNat_mul]
  omega

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
  by rw [show a + b = UInt256.add a b from rfl, UInt256.add, toNat, toBitVec_ofBitVec]; exact BitVec.toNat_add ..

theorem toNat_mul (a b : UInt256) : (a * b).toNat = (a.toNat * b.toNat) % size :=
  by rw [show a * b = UInt256.mul a b from rfl, UInt256.mul, toNat, toBitVec_ofBitVec]; exact BitVec.toNat_mul ..

theorem toNat_sub (a b : UInt256) : (a - b).toNat = (size - b.toNat + a.toNat) % size :=
  by rw [show a - b = UInt256.sub a b from rfl, UInt256.sub, toNat, toBitVec_ofBitVec]; exact BitVec.toNat_sub ..

/-! ## limb decomposition

What the byte codec needs: the value a word denotes, in terms of its limbs.
`BitVec.toNat_append` gives the `|||` form; each `or` is an `add` because the
lower part is below the shift. -/

/-- Each limb is the corresponding 64-bit window of the value.  Stated in the
`>>> s % 2 ^ 64` form because that is what the byte codec's `encodeBEU_add`
chain produces.  Proved of `ofBitVec` first, where the limbs are literally
the windows, then transported along `ofBitVec_toBitVec`. -/
private theorem window_ofBitVec (v : BitVec 256) :
    (v.toNat >>> 192 % 2 ^ 64 = (ofBitVec v).l0.toNat)
    ∧ (v.toNat >>> 128 % 2 ^ 64 = (ofBitVec v).l1.toNat)
    ∧ (v.toNat >>> 64 % 2 ^ 64 = (ofBitVec v).l2.toNat)
    ∧ (v.toNat >>> 0 % 2 ^ 64 = (ofBitVec v).l3.toNat) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem toNat_window_l0 (x : UInt256) : x.toNat >>> 192 % 2 ^ 64 = x.l0.toNat := by
  have h := (window_ofBitVec x.toBitVec).1; rwa [ofBitVec_toBitVec] at h

theorem toNat_window_l1 (x : UInt256) : x.toNat >>> 128 % 2 ^ 64 = x.l1.toNat := by
  have h := (window_ofBitVec x.toBitVec).2.1; rwa [ofBitVec_toBitVec] at h

theorem toNat_window_l2 (x : UInt256) : x.toNat >>> 64 % 2 ^ 64 = x.l2.toNat := by
  have h := (window_ofBitVec x.toBitVec).2.2.1; rwa [ofBitVec_toBitVec] at h

theorem toNat_window_l3 (x : UInt256) : x.toNat % 2 ^ 64 = x.l3.toNat := by
  have h := (window_ofBitVec x.toBitVec).2.2.2; rwa [ofBitVec_toBitVec] at h

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

/-! ### the encoder, limb-direct

`toBEByteArray` above goes through `toNat`, which builds the bit vector and so
the bignum — exactly the cost the limbs exist to avoid.  `toBEByteArrayFast`
pushes the four limbs straight into the buffer, and `@[csimp]` swaps it in at
code generation, so the definition above stays the one every theorem is
about. -/

/-- The four limbs pushed straight out, most significant first. -/
def toBEByteArrayFast (x : UInt256) : ByteArray :=
  pushBEChunk 8 x.l3 (pushBEChunk 8 x.l2 (pushBEChunk 8 x.l1
    (pushBEChunk 8 x.l0 (ByteArray.emptyWithCapacity byteSize))))

/-- The width-32 encoding is the four limb encodings in order.  Each step
splits eight bytes off the bottom with `encodeBEU_add`; each limb is then the
matching window of the value, which is what `toNat_window_*` says. -/
private theorem encodeBEU_byteSize_limbs (x : UInt256) :
    encodeBEU byteSize x.toNat =
      encodeBEU 8 x.l0.toNat ++ encodeBEU 8 x.l1.toNat ++ encodeBEU 8 x.l2.toNat
        ++ encodeBEU 8 x.l3.toNat := by
  have hdvd : (256 : Nat) ^ 8 ∣ 2 ^ 64 := by omega
  -- one limb: the quotient's low 64 bits are the window, and a width-8
  -- encoding only reads that far, so the `% 2 ^ 64` can be dropped
  have step : ∀ {e s k : Nat}, (256 : Nat) ^ e = 2 ^ s → x.toNat >>> s % 2 ^ 64 = k →
      encodeBEU 8 (x.toNat / 256 ^ e) = encodeBEU 8 k := by
    intro e s k he hw
    rw [← hw, Nat.shiftRight_eq_div_pow, encodeBEU_mod_of_dvd hdvd, he]
  have hl0 := step (by omega : (256 : Nat) ^ 24 = 2 ^ 192) (toNat_window_l0 x)
  have hl1 := step (by omega : (256 : Nat) ^ 16 = 2 ^ 128) (toNat_window_l1 x)
  have hl2 := step (by omega : (256 : Nat) ^ 8 = 2 ^ 64) (toNat_window_l2 x)
  have hl3 : encodeBEU 8 x.toNat = encodeBEU 8 x.l3.toNat := by
    rw [← toNat_window_l3 x, encodeBEU_mod_of_dvd hdvd]
  have d1 : x.toNat / 256 ^ 8 / 256 ^ 8 = x.toNat / 256 ^ 16 := by
    rw [Nat.div_div_eq_div_mul]
  have d2 : x.toNat / 256 ^ 16 / 256 ^ 8 = x.toNat / 256 ^ 24 := by
    rw [Nat.div_div_eq_div_mul]
  show encodeBEU (8 + 24) x.toNat = _
  rw [encodeBEU_add 8 24 x.toNat, show (24 : Nat) = 8 + 16 from rfl,
    encodeBEU_add 8 16 (x.toNat / 256 ^ 8), show (16 : Nat) = 8 + 8 from rfl,
    encodeBEU_add 8 8 (x.toNat / 256 ^ 8 / 256 ^ 8), d1, d2, hl0, hl1, hl2, hl3]

/-- The swap the compiler acts on. -/
@[csimp] theorem toBEByteArray_eq_fast : @toBEByteArray = @toBEByteArrayFast := by
  funext x
  apply ByteArray.data_inj
  rw [← Array.toList_inj]
  simp only [toBEByteArray, encodeBEBytes, List.data_toByteArray, List.toList_toArray,
    toBEByteArrayFast, pushBEChunk_eq,
    show (ByteArray.emptyWithCapacity byteSize).data.toList = [] from rfl, List.nil_append]
  exact encodeBEU_byteSize_limbs x


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

/-! ### the reader, limb-direct

`ofBEByteArray` takes a buffer of any length and goes through `decodeBEBytes`,
so it builds the `Nat`.  A word read at a known offset does not have to:
`ofBEByteArrayAt` is four `beWord8At`s straight into limbs.  The bound is an
argument rather than a `!`, so the thirty-two reads are unchecked — a caller
reading a word has already established it to know the word is there. -/

/-- Read the 32-byte big-endian word at `off`, straight into limbs. -/
def ofBEByteArrayAt (ba : ByteArray) (off : Nat) (h : off + 32 ≤ ba.size) : UInt256 :=
  ⟨beWord8At ba off        (by omega),
   beWord8At ba (off + 8)  (by omega),
   beWord8At ba (off + 16) (by omega),
   beWord8At ba (off + 24) (by omega)⟩

/-- **Agreement**: the limb read denotes the windowed `Nat` read.  Four
unfoldings of the chunked loop, which under the bound takes its eight-byte
branch every time, then stops on an empty tail. -/
theorem toNat_ofBEByteArrayAt (ba : ByteArray) (off : Nat) (h : off + 32 ≤ ba.size) :
    (ofBEByteArrayAt ba off h).toNat = decodeBEBytesFrom ba off 32 := by
  rw [decodeBEBytesFrom_eq_fast]
  show _ = decodeBEFromFast.loop ba 0 off (min (off + 32) ba.size)
  rw [show min (off + 32) ba.size = off + 32 from by omega,
    decodeBEFromFast.loop, if_pos (by omega), decodeBEFromFast.loop, if_pos (by omega),
    decodeBEFromFast.loop, if_pos (by omega), decodeBEFromFast.loop, if_pos (by omega),
    decodeBEFromFast.loop, if_neg (by omega), decodeBEFromFast.byteLoop, if_neg (by omega),
    toNat_eq_limbs, ofBEByteArrayAt]
  simp only [beWord8At_eq, Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add]

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
