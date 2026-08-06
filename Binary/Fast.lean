import Binary.ByteArray

/-!
# Binary.Fast

Efficient **compiled implementations** of the codecs, each proved equal to the
definition it replaces and registered with `@[csimp]`.

## What costs what

`encodeLE` walks the value one digit at a time:

```
| len+1, n => (n % 256) :: encodeLE len (n / 256)
```

`n` is an arbitrary `Nat`, so above `2 ^ 63` it is a GMP bignum and each `/`
and `%` is a call that allocates.  A 32-byte word costs 32 of them — about
4.8 µs, against ~30 ns for all the list plumbing around it.  Decoding is the
mirror image: one bignum multiply-and-add per byte.

## The fix: one bignum operation per eight bytes

`Nat` arithmetic is only expensive while the operand is a bignum.  The fast
codecs therefore work **eight bytes at a time**: `UInt64.ofNat n` takes the low
64 bits into a machine word (no allocation), those eight bytes are produced or
consumed with `UInt64` shifts and multiplies (free), and a single `n >>> 64`
advances to the next chunk.  A 32-byte word costs 4 bignum operations instead
of 32 — measured 9–13× faster (`lake build bench`).

Chunking is licensed by two `Binary.Core` laws, `encodeLE_add` (a fixed-width
encoding may be computed in pieces) and `encodeLE_mod_of_dvd` (the low `len`
bytes only depend on `n` modulo anything `256 ^ len` divides, which is what
makes it sound to read a chunk out of a *truncating* `UInt64`), together with
their `Binary.UInt8` liftings.  This module adds only what is specific to the
64-bit window and the machine-word arithmetic.

## Why `@[csimp]`

The definitions — and therefore every theorem about them — are untouched; the
compiler is told to run a different function, on the strength of a proof that
the two are equal.  Nothing here is trusted: each `..._eq_fast` theorem is an
ordinary theorem, and deleting the `@[csimp]` attributes would change
performance and nothing else.

`@[csimp]` rewrites calls in modules compiled *after* the attribute is in
scope, so this module is imported by `Binary.Fixed` and `Binary.UInt256` rather
than the other way round; anything downstream of those gets the fast code too.
-/

namespace Binary

/-! ## The 64-bit window

`UInt64.ofNat n` truncates to `n % 2 ^ 64`.  These four facts say that this is
invisible to the low eight bytes, and that `n >>> 64` is exactly "drop them". -/

/-- `2 ^ 64` is eight bytes' worth: the radix of every chunk step. -/
theorem two_pow_64_eq : (2 : Nat) ^ 64 = 256 ^ 8 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-- Advancing to the next chunk is division by the radix. -/
theorem shiftRight_64 (n : Nat) : n >>> 64 = n / 256 ^ 8 := by
  rw [Nat.shiftRight_eq_div_pow, two_pow_64_eq]

/-- Attaching a decoded chunk is multiplication by the radix. -/
theorem shiftLeft_64 (n : Nat) : n <<< 64 = n * 256 ^ 8 := by
  rw [Nat.shiftLeft_eq, two_pow_64_eq]

/-- `256 ^ len` divides `2 ^ 64` whenever `len ≤ 8`: the side condition that
lets a `len`-byte encoding be read out of a truncating `UInt64`. -/
theorem pow256_dvd_two_pow_64 {len : Nat} (h : len ≤ 8) : 256 ^ len ∣ 2 ^ 64 := by
  rw [show (256 : Nat) ^ len = 2 ^ (8 * len) by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]
  exact Nat.pow_dvd_pow 2 (by omega)

/-- Up to eight bytes do not notice the 64-bit window. -/
theorem encodeLEU_window {len : Nat} (h : len ≤ 8) (n : Nat) :
    encodeLEU len (UInt64.ofNat n).toNat = encodeLEU len n := by
  rw [UInt64.toNat_ofNat', encodeLEU_mod_of_dvd (pow256_dvd_two_pow_64 h)]

theorem encodeBEU_window {len : Nat} (h : len ≤ 8) (n : Nat) :
    encodeBEU len (UInt64.ofNat n).toNat = encodeBEU len n := by
  rw [UInt64.toNat_ofNat', encodeBEU_mod_of_dvd (pow256_dvd_two_pow_64 h)]

/-- One chunk step: the low eight bytes come from the machine word, the rest
from `n` shifted down by 64 bits. -/
theorem encodeLEU_chunk {len : Nat} (h : 8 ≤ len) (n : Nat) :
    encodeLEU len n = encodeLEU 8 (UInt64.ofNat n).toNat ++ encodeLEU (len - 8) (n >>> 64) := by
  rw [encodeLEU_window (Nat.le_refl 8), shiftRight_64, ← encodeLEU_add,
    show 8 + (len - 8) = len by omega]

theorem encodeBEU_chunk {len : Nat} (h : 8 ≤ len) (n : Nat) :
    encodeBEU len n = encodeBEU (len - 8) (n >>> 64) ++ encodeBEU 8 (UInt64.ofNat n).toNat := by
  rw [encodeBEU_window (Nat.le_refl 8), shiftRight_64, ← encodeBEU_add,
    show 8 + (len - 8) = len by omega]

/-! ## Emitting a chunk

Four emitters, one per output shape the fast encoders need: a list built
directly, a list consed onto an accumulator, and the two `ByteArray`
equivalents.  All four run on `UInt64` alone. -/

/-- Shifting a machine word right by 8 divides its value by 256. -/
theorem toNat_shiftRight_eight (x : UInt64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [UInt64.toNat_shiftRight, show (UInt64.toNat 8 % 64) = 8 by decide,
    Nat.shiftRight_eq_div_pow]

/-- A machine word's byte `0` is the `Nat` digit `n % 256`. -/
theorem toUInt8_eq_ofNat_mod (x : UInt64) : x.toUInt8 = UInt8.ofNat (x.toNat % 256) := by
  rw [← UInt8.toNat_inj, UInt64.toNat_toUInt8, UInt8.toNat_ofNat']
  show x.toNat % 256 = x.toNat % 256 % 256
  rw [Nat.mod_mod]

/-- The low `len` bytes of a machine word, least significant first. -/
def leChunk (len : Nat) (x : UInt64) : List UInt8 :=
  match len with
  | 0 => []
  | l + 1 => x.toUInt8 :: leChunk l (x >>> 8)

/-- The low `len` bytes of a machine word, most significant first, consed onto
`acc` (so the caller supplies the *more* significant part). -/
def beChunk (len : Nat) (x : UInt64) (acc : List UInt8) : List UInt8 :=
  match len with
  | 0 => acc
  | l + 1 => beChunk l (x >>> 8) (x.toUInt8 :: acc)

/-- The low `len` bytes of a machine word pushed onto a `ByteArray`, least
significant first. -/
def pushLEChunk (len : Nat) (x : UInt64) (acc : ByteArray) : ByteArray :=
  match len with
  | 0 => acc
  | l + 1 => pushLEChunk l (x >>> 8) (acc.push x.toUInt8)

/-- The low `len` bytes of a machine word pushed onto a `ByteArray`, most
significant first: recurse on the higher bytes, then push. -/
def pushBEChunk (len : Nat) (x : UInt64) (acc : ByteArray) : ByteArray :=
  match len with
  | 0 => acc
  | l + 1 => (pushBEChunk l (x >>> 8) acc).push x.toUInt8

theorem leChunk_eq (len : Nat) (x : UInt64) : leChunk len x = encodeLEU len x.toNat := by
  induction len generalizing x with
  | zero => rfl
  | succ l ih =>
      rw [leChunk, ih, toNat_shiftRight_eight, encodeLEU_succ, toUInt8_eq_ofNat_mod]

theorem beChunk_eq (len : Nat) (x : UInt64) (acc : List UInt8) :
    beChunk len x acc = encodeBEU len x.toNat ++ acc := by
  induction len generalizing x acc with
  | zero => rfl
  | succ l ih =>
      rw [beChunk, ih, toNat_shiftRight_eight, encodeBEU_succ, toUInt8_eq_ofNat_mod,
        List.append_assoc, List.cons_append, List.nil_append]

theorem pushLEChunk_eq (len : Nat) (x : UInt64) (acc : ByteArray) :
    (pushLEChunk len x acc).data.toList = acc.data.toList ++ encodeLEU len x.toNat := by
  induction len generalizing x acc with
  | zero => simp [pushLEChunk, encodeLEU, natsToUInt8, encodeLE]
  | succ l ih =>
      rw [pushLEChunk, ih, ByteArray.data_push, Array.toList_push, toNat_shiftRight_eight,
        encodeLEU_succ, toUInt8_eq_ofNat_mod, List.append_assoc, List.cons_append,
        List.nil_append]

theorem pushBEChunk_eq (len : Nat) (x : UInt64) (acc : ByteArray) :
    (pushBEChunk len x acc).data.toList = acc.data.toList ++ encodeBEU len x.toNat := by
  induction len generalizing x with
  | zero => simp [pushBEChunk, encodeBEU, natsToUInt8, encodeBE, encodeLE]
  | succ l ih =>
      rw [pushBEChunk, ByteArray.data_push, Array.toList_push, ih, toNat_shiftRight_eight,
        encodeBEU_succ, toUInt8_eq_ofNat_mod, List.append_assoc]

/-! ## Fast encoders

Each is the same loop over the four emitters: peel eight bytes while more than
eight remain, then emit the short tail straight out of the machine word. -/

/-- Little-endian `List UInt8` encoding, eight bytes per bignum operation. -/
def encodeLEUFast (len n : Nat) : List UInt8 :=
  if 8 < len then leChunk 8 (UInt64.ofNat n) ++ encodeLEUFast (len - 8) (n >>> 64)
  else leChunk len (UInt64.ofNat n)
termination_by len

/-- Big-endian `List UInt8` encoding: the chunks arrive least significant
first, so they are consed onto an accumulator. -/
def encodeBEUFast.loop (acc : List UInt8) (len n : Nat) : List UInt8 :=
  if 8 < len then loop (beChunk 8 (UInt64.ofNat n) acc) (len - 8) (n >>> 64)
  else beChunk len (UInt64.ofNat n) acc
termination_by len

/-- Big-endian `List UInt8` encoding, eight bytes per bignum operation. -/
def encodeBEUFast (len n : Nat) : List UInt8 := encodeBEUFast.loop [] len n

/-- Little-endian `ByteArray` encoding: no list is built at all. -/
def encodeLEBytesFast.loop (acc : ByteArray) (len n : Nat) : ByteArray :=
  if 8 < len then loop (pushLEChunk 8 (UInt64.ofNat n) acc) (len - 8) (n >>> 64)
  else pushLEChunk len (UInt64.ofNat n) acc
termination_by len

/-- Little-endian `ByteArray` encoding, into a buffer sized in advance. -/
def encodeLEBytesFast (len n : Nat) : ByteArray :=
  encodeLEBytesFast.loop (ByteArray.emptyWithCapacity len) len n

/-- Big-endian `ByteArray` encoding: recurse on the more significant chunks
first, then push the low eight bytes. -/
def encodeBEBytesFast.loop (acc : ByteArray) (len n : Nat) : ByteArray :=
  if 8 < len then pushBEChunk 8 (UInt64.ofNat n) (loop acc (len - 8) (n >>> 64))
  else pushBEChunk len (UInt64.ofNat n) acc
termination_by len

/-- Big-endian `ByteArray` encoding, into a buffer sized in advance.

`@[extern]` sends the compiled call to `c/binary_shim.c`, which exports the
whole value in one `mpz_export` instead of peeling it a chunk at a time.  The
body below is unchanged and is still the definition every theorem here is
stated over; the attribute only redirects code generation, as it already does
for `ByteArray.push`. -/
@[extern "lean_binary_encode_be_bytes"]
def encodeBEBytesFast (len n : Nat) : ByteArray :=
  encodeBEBytesFast.loop (ByteArray.emptyWithCapacity len) len n

/-- `ByteArray.emptyWithCapacity` reserves space but starts empty. -/
theorem toList_emptyWithCapacity (c : Nat) :
    (ByteArray.emptyWithCapacity c).data.toList = [] := rfl

@[csimp] theorem encodeLEU_eq_fast : @encodeLEU = @encodeLEUFast := by
  funext len n
  induction len, n using encodeLEUFast.induct with
  | case1 len n h ih =>
      rw [encodeLEUFast, if_pos h, leChunk_eq, ← ih, ← encodeLEU_chunk (by omega)]
  | case2 len n h => rw [encodeLEUFast, if_neg h, leChunk_eq, encodeLEU_window (by omega)]

theorem encodeBEUFast.loop_eq (acc : List UInt8) (len n : Nat) :
    encodeBEUFast.loop acc len n = encodeBEU len n ++ acc := by
  induction acc, len, n using encodeBEUFast.loop.induct with
  | case1 acc len n h ih =>
      rw [encodeBEUFast.loop, if_pos h, ih, beChunk_eq, ← List.append_assoc,
        ← encodeBEU_chunk (by omega)]
  | case2 acc len n h =>
      rw [encodeBEUFast.loop, if_neg h, beChunk_eq, encodeBEU_window (by omega)]

@[csimp] theorem encodeBEU_eq_fast : @encodeBEU = @encodeBEUFast := by
  funext len n
  rw [encodeBEUFast, encodeBEUFast.loop_eq, List.append_nil]

theorem encodeLEBytesFast.loop_eq (acc : ByteArray) (len n : Nat) :
    (encodeLEBytesFast.loop acc len n).data.toList = acc.data.toList ++ encodeLEU len n := by
  induction acc, len, n using encodeLEBytesFast.loop.induct with
  | case1 acc len n h ih =>
      rw [encodeLEBytesFast.loop, if_pos h, ih, pushLEChunk_eq, List.append_assoc,
        ← encodeLEU_chunk (by omega)]
  | case2 acc len n h =>
      rw [encodeLEBytesFast.loop, if_neg h, pushLEChunk_eq, encodeLEU_window (by omega)]

theorem encodeBEBytesFast.loop_eq (acc : ByteArray) (len n : Nat) :
    (encodeBEBytesFast.loop acc len n).data.toList = acc.data.toList ++ encodeBEU len n := by
  induction len, n using encodeBEBytesFast.loop.induct with
  | case1 len n h ih =>
      rw [encodeBEBytesFast.loop, if_pos h, pushBEChunk_eq, ih, List.append_assoc,
        ← encodeBEU_chunk (by omega)]
  | case2 len n h =>
      rw [encodeBEBytesFast.loop, if_neg h, pushBEChunk_eq, encodeBEU_window (by omega)]

@[csimp] theorem encodeLEBytes_eq_fast : @encodeLEBytes = @encodeLEBytesFast := by
  funext len n
  apply ByteArray.data_inj
  rw [← Array.toList_inj, encodeLEBytesFast, encodeLEBytesFast.loop_eq,
    toList_emptyWithCapacity, List.nil_append, encodeLEBytes, List.toList_data_toByteArray]

@[csimp] theorem encodeBEBytes_eq_fast : @encodeBEBytes = @encodeBEBytesFast := by
  funext len n
  apply ByteArray.data_inj
  rw [← Array.toList_inj, encodeBEBytesFast, encodeBEBytesFast.loop_eq,
    toList_emptyWithCapacity, List.nil_append, encodeBEBytes, List.toList_data_toByteArray]

/-! ## Accumulating a chunk

The decoding direction: shift bytes into a machine word, which is sound as long
as what has accumulated still fits in 64 bits. -/

/-- Shift one byte into a machine word. -/
def beWordStep (acc : UInt64) (b : UInt8) : UInt64 := acc * 256 + b.toUInt64

theorem toNat_beWordStep {acc : UInt64} (b : UInt8) (h : acc.toNat * 256 + 256 ≤ 2 ^ 64) :
    (beWordStep acc b).toNat = acc.toNat * 256 + b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  rw [beWordStep, UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64,
    show (256 : UInt64).toNat = 256 by decide, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- Folding bytes into a machine word computes the big-endian value they denote,
provided the result fits.  The hypothesis reads "`acc` followed by `bs.length`
more bytes still fits in 64 bits". -/
theorem toNat_foldl_beWordStep (acc : UInt64) (bs : List UInt8)
    (h : (acc.toNat + 1) * 256 ^ bs.length ≤ 2 ^ 64) :
    (bs.foldl beWordStep acc).toNat = acc.toNat * 256 ^ bs.length + decodeBEU bs := by
  induction bs generalizing acc with
  | nil => simp [decodeBEU, decodeBE, decodeLE, uint8ToNats]
  | cons b bs ih =>
      have hpow : (256 : Nat) ^ (b :: bs).length = 256 * 256 ^ bs.length := by
        rw [List.length_cons, Nat.pow_add_one, Nat.mul_comm]
      -- restate the hypothesis with the head's contribution split off
      rw [show (acc.toNat + 1) * 256 ^ (b :: bs).length =
          (acc.toNat * 256 + 256) * 256 ^ bs.length by
        rw [hpow, ← Nat.mul_assoc, Nat.add_mul, Nat.one_mul]] at h
      -- the head byte fits: the tail's `256 ^ n` factor only makes it bigger
      have hstep := toNat_beWordStep (acc := acc) b
        (Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))) h)
      -- and the tail still fits once the head has been shifted in
      have htail : ((beWordStep acc b).toNat + 1) * 256 ^ bs.length ≤ 2 ^ 64 :=
        Nat.le_trans (Nat.mul_le_mul_right _ (by rw [hstep]; have := b.toNat_lt; omega)) h
      rw [List.foldl_cons, ih _ htail, hstep, decodeBEU_cons, hpow, Nat.add_mul, Nat.mul_assoc,
        Nat.add_assoc]

/-- Eight bytes accumulated into one machine word, most significant first. -/
def beWord8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  beWordStep (beWordStep (beWordStep (beWordStep (beWordStep (beWordStep (beWordStep
    (beWordStep 0 b0) b1) b2) b3) b4) b5) b6) b7

theorem toNat_beWord8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (beWord8 b0 b1 b2 b3 b4 b5 b6 b7).toNat = decodeBEU [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have h := toNat_foldl_beWordStep 0 [b0, b1, b2, b3, b4, b5, b6, b7] (by
    show (0 + 1) * 256 ^ 8 ≤ 2 ^ 64
    rw [← two_pow_64_eq, Nat.one_mul]
    exact Nat.le_refl _)
  rw [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add] at h
  rw [← h]
  rfl

/-! ## Fast decoders -/

/-- Big-endian `List UInt8` decoding, eight bytes per bignum operation.  The
accumulator advances by `<<< 64`, mirroring the encoders' `>>> 64`. -/
def decodeBEUFast.loop (acc : Nat) : List UInt8 → Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      loop ((acc <<< 64) + (beWord8 b0 b1 b2 b3 b4 b5 b6 b7).toNat) rest
  | bs => bs.foldl (fun acc b => acc * 256 + b.toNat) acc

/-- Big-endian `List UInt8` decoding, eight bytes per bignum operation. -/
def decodeBEUFast (bs : List UInt8) : Nat := decodeBEUFast.loop 0 bs

/-- Little-endian `List UInt8` decoding: the chunks arrive least significant
first, so the recursion multiplies up rather than accumulating down. -/
def decodeLEUFast : List UInt8 → Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      (beWord8 b7 b6 b5 b4 b3 b2 b1 b0).toNat + (decodeLEUFast rest <<< 64)
  | bs => bs.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem decodeBEUFast.loop_eq (acc : Nat) (bs : List UInt8) :
    decodeBEUFast.loop acc bs = acc * 256 ^ bs.length + decodeBEU bs := by
  induction acc, bs using decodeBEUFast.loop.induct with
  | case1 acc b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
      rw [decodeBEUFast.loop, ih, toNat_beWord8, shiftLeft_64,
        show (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
          [b0, b1, b2, b3, b4, b5, b6, b7] ++ rest from rfl,
        decodeBEU_append, List.length_append, Nat.pow_add,
        show ([b0, b1, b2, b3, b4, b5, b6, b7] : List UInt8).length = 8 from rfl,
        Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  | case2 acc bs hne =>
      rw [decodeBEUFast.loop, decodeBEU_foldl]
      exact hne

@[csimp] theorem decodeBEU_eq_fast : @decodeBEU = @decodeBEUFast := by
  funext bs
  rw [decodeBEUFast, decodeBEUFast.loop_eq, Nat.zero_mul, Nat.zero_add]

@[csimp] theorem decodeLEU_eq_fast : @decodeLEU = @decodeLEUFast := by
  funext bs
  induction bs using decodeLEUFast.induct with
  | case1 b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
      have hchunk : (beWord8 b7 b6 b5 b4 b3 b2 b1 b0).toNat =
          decodeLEU [b0, b1, b2, b3, b4, b5, b6, b7] := by
        rw [toNat_beWord8, ← decodeBEU_reverse]; rfl
      rw [decodeLEUFast, hchunk, ← ih,
        show (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
          [b0, b1, b2, b3, b4, b5, b6, b7] ++ rest from rfl,
        decodeLEU_append,
        show ([b0, b1, b2, b3, b4, b5, b6, b7] : List UInt8).length = 8 from rfl,
        Nat.mul_comm (256 ^ 8) (decodeLEU rest), ← shiftLeft_64]
  | case2 bs hne =>
      rw [decodeLEUFast, decodeLEU_foldr]
      exact hne

/-! ## The `ByteArray` decoders

`decodeLEBytes` and `decodeBEBytes` are already defined as their `List UInt8`
counterparts applied to `ba.data.toList`, so all they need is to reach the
chunked decoders — but their bodies were compiled in `Binary.ByteArray`, before
this module's `@[csimp]` attributes existed, so they still call the unchunked
ones.  Redirecting them is a one-line definition each.

An earlier draft instead gave them index-based loops that avoided
`ByteArray.data`, an `@[extern]` conversion that copies the packed bytes into a
boxed `Array UInt8`.  Measured against the chunked list decoder those loops
were *six times slower*: they went back to one bignum multiply-and-add per
byte, which costs far more than the copy saves.  Skipping the copy is worth
doing, but only on top of chunking, not instead of it. -/

/-- Big-endian `ByteArray` decoding via the chunked list decoder. -/
def decodeBEBytesFast (ba : ByteArray) : Nat := decodeBEUFast ba.data.toList

/-- Little-endian `ByteArray` decoding via the chunked list decoder. -/
def decodeLEBytesFast (ba : ByteArray) : Nat := decodeLEUFast ba.data.toList

@[csimp] theorem decodeBEBytes_eq_fast : @decodeBEBytes = @decodeBEBytesFast := by
  funext ba
  show decodeBEU ba.data.toList = decodeBEUFast ba.data.toList
  rw [decodeBEU_eq_fast]

@[csimp] theorem decodeLEBytes_eq_fast : @decodeLEBytes = @decodeLEBytesFast := by
  funext ba
  show decodeLEU ba.data.toList = decodeLEUFast ba.data.toList
  rw [decodeLEU_eq_fast]

/-! ## Windowed `ByteArray` reads

`decodeBEBytesFrom ba off len` is specified by slicing — `drop off`, then
`take len` — which is the wrong thing to run: the slice copies the buffer
into a boxed `Array UInt8` and then allocates a cons cell per byte, and a
caller decoding many fields out of one buffer pays that per field.

The implementation below never mentions the list.  It walks the window by
index with `ba[i]!`, eight bytes per bignum operation exactly as the
whole-buffer decoders do, and falls back to a byte loop for the last
fewer-than-eight.  What made the earlier index-based attempt slow (recorded
above) was going *unchunked*, not the indexing. -/

/-- One byte off the front of a window, as an indexed read. -/
theorem window_peel (ba : ByteArray) (i len : Nat) (h : i < ba.size) :
    (ba.data.toList.drop i).take (len + 1) =
      ba[i]! :: (ba.data.toList.drop (i + 1)).take len := by
  have hl : i < ba.data.toList.length := by
    rwa [← ByteArray.size_eq_toList_length]
  rw [List.drop_eq_getElem_cons hl, List.take_succ_cons, getElem!_pos ba i h]
  rfl

/-- The tail of a window: fewer than eight bytes, one bignum step each. -/
def decodeBEFromFast.byteLoop (ba : ByteArray) (acc : Nat) (i stop : Nat) : Nat :=
  if i < stop then byteLoop ba (acc * 256 + (ba[i]!).toNat) (i + 1) stop else acc
termination_by stop - i

/-- The window walked eight bytes at a time, then the short tail. -/
def decodeBEFromFast.loop (ba : ByteArray) (acc : Nat) (i stop : Nat) : Nat :=
  if i + 8 ≤ stop then
    loop ba ((acc <<< 64) +
        (beWord8 ba[i]! ba[i+1]! ba[i+2]! ba[i+3]!
                 ba[i+4]! ba[i+5]! ba[i+6]! ba[i+7]!).toNat)
      (i + 8) stop
  else byteLoop ba acc i stop
termination_by stop - i

/-- Big-endian windowed read with no slicing.  The window is clamped to the
buffer, which is what `take` does to the specification's slice.

`@[extern]` sends the compiled call to `c/binary_shim.c`, which imports the
clamped window in one `mpz_import` rather than accumulating `acc <<< 64` a
chunk at a time — each of those steps allocates a fresh bignum.  As above,
the body is the definition and the attribute only redirects code
generation. -/
@[extern "lean_binary_decode_be_from"]
def decodeBEBytesFromFast (ba : ByteArray) (off len : Nat) : Nat :=
  decodeBEFromFast.loop ba 0 off (min (off + len) ba.size)

/-- A window that ends inside the buffer has exactly the length it asks for. -/
theorem window_length (ba : ByteArray) (i stop : Nat) (hs : stop ≤ ba.size) :
    ((ba.data.toList.drop i).take (stop - i)).length = stop - i := by
  rw [List.length_take, List.length_drop, ← ByteArray.size_eq_toList_length]
  omega

/-- The byte loop is the specification's left fold over the window.  Stated
with a fuel bound so the induction is on a decreasing measure. -/
theorem decodeBEFromFast.byteLoop_eq_aux (ba : ByteArray) (hs : stop ≤ ba.size) :
    ∀ (fuel acc i : Nat), stop - i ≤ fuel →
      byteLoop ba acc i stop =
        ((ba.data.toList.drop i).take (stop - i)).foldl (fun acc b => acc * 256 + b.toNat) acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro acc i hf
      rw [byteLoop, if_neg (by omega), show stop - i = 0 by omega, List.take_zero, List.foldl_nil]
  | succ n ih =>
      intro acc i hf
      by_cases h : i < stop
      · rw [byteLoop, if_pos h, show stop - i = (stop - (i + 1)) + 1 by omega,
          window_peel ba i _ (by omega), List.foldl_cons, ih _ (i + 1) (by omega)]
      · rw [byteLoop, if_neg h, show stop - i = 0 by omega, List.take_zero, List.foldl_nil]

theorem decodeBEFromFast.byteLoop_eq (ba : ByteArray) (hs : stop ≤ ba.size) (acc i : Nat) :
    byteLoop ba acc i stop =
      ((ba.data.toList.drop i).take (stop - i)).foldl (fun acc b => acc * 256 + b.toNat) acc :=
  byteLoop_eq_aux ba hs (stop - i) acc i (Nat.le_refl _)

/-- Eight bytes of the window, split off the front. -/
theorem window_chunk8 (ba : ByteArray) (i stop : Nat) (h8 : i + 8 ≤ stop) (hs : stop ≤ ba.size) :
    (ba.data.toList.drop i).take (stop - i) =
      [ba[i]!, ba[i+1]!, ba[i+2]!, ba[i+3]!, ba[i+4]!, ba[i+5]!, ba[i+6]!, ba[i+7]!] ++
        (ba.data.toList.drop (i + 8)).take (stop - (i + 8)) := by
  have e : ∀ k, k < 8 → i + k < ba.size := fun k hk => by omega
  rw [show stop - i = (stop - (i + 8)) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [window_peel ba i _ (e 0 (by omega))]
  rw [window_peel ba (i + 1) _ (e 1 (by omega))]
  rw [window_peel ba (i + 1 + 1) _ (e 2 (by omega))]
  rw [window_peel ba (i + 1 + 1 + 1) _ (e 3 (by omega))]
  rw [window_peel ba (i + 1 + 1 + 1 + 1) _ (e 4 (by omega))]
  rw [window_peel ba (i + 1 + 1 + 1 + 1 + 1) _ (e 5 (by omega))]
  rw [window_peel ba (i + 1 + 1 + 1 + 1 + 1 + 1) _ (e 6 (by omega))]
  rw [window_peel ba (i + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ (e 7 (by omega))]
  rfl

theorem decodeBEFromFast.loop_eq_aux (ba : ByteArray) (hs : stop ≤ ba.size) :
    ∀ (fuel acc i : Nat), stop - i ≤ fuel →
      loop ba acc i stop =
        acc * 256 ^ (stop - i) + decodeBEU ((ba.data.toList.drop i).take (stop - i)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro acc i hf
      rw [loop, if_neg (by omega), byteLoop_eq ba hs, decodeBEU_foldl,
        window_length ba i stop hs]
  | succ n ih =>
      intro acc i hf
      by_cases h : i + 8 ≤ stop
      · have hlen : (ba.data.toList.drop (i + 8)).length = ba.size - (i + 8) := by
          rw [List.length_drop, ← ByteArray.size_eq_toList_length]
        rw [loop, if_pos h, ih _ (i + 8) (by omega), window_chunk8 ba i stop h hs,
          decodeBEU_append, toNat_beWord8, shiftLeft_64, List.length_take, hlen,
          show min (stop - (i + 8)) (ba.size - (i + 8)) = stop - (i + 8) by omega,
          show stop - i = 8 + (stop - (i + 8)) by omega, Nat.pow_add,
          Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
      · rw [loop, if_neg h, byteLoop_eq ba hs, decodeBEU_foldl, window_length ba i stop hs]

theorem decodeBEFromFast.loop_eq (ba : ByteArray) (hs : stop ≤ ba.size) (acc i : Nat) :
    loop ba acc i stop =
      acc * 256 ^ (stop - i) + decodeBEU ((ba.data.toList.drop i).take (stop - i)) :=
  loop_eq_aux ba hs (stop - i) acc i (Nat.le_refl _)

@[csimp] theorem decodeBEBytesFrom_eq_fast : @decodeBEBytesFrom = @decodeBEBytesFromFast := by
  funext ba off len
  rw [decodeBEBytesFromFast, decodeBEFromFast.loop_eq ba (Nat.min_le_right _ _),
    Nat.zero_mul, Nat.zero_add, decodeBEBytesFrom]
  congr 1
  have hlen : (ba.data.toList.drop off).length = ba.size - off := by
    rw [List.length_drop, ← ByteArray.size_eq_toList_length]
  rcases Nat.le_total (off + len) ba.size with h | h
  · rw [show min (off + len) ba.size = off + len by omega, show off + len - off = len by omega]
  · rw [show min (off + len) ba.size = ba.size by omega,
      List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

end Binary
