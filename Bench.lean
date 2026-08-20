import Binary

/-!
# Bench

Micro-benchmark for the `@[csimp]` implementations of `Binary.Fast`.  Build
and run with `lake build bench && ./.lake/build/bin/bench`.

`ref` is the pipeline the definitions describe, spelled out here so that
`@[csimp]` cannot rewrite it: `encodeBE` and `encodeLE` carry no `@[csimp]`
attribute, so `natsToUInt8 (encodeBE len n)` compiles to exactly what
`encodeBEU` used to.  `now` is what any module importing `Binary.Fast`
(directly or transitively) actually runs today — including the calls written
as `encodeBEU`, which is why measuring `encodeBEU` itself would show no
difference.

Inputs vary with the loop counter: on a constant argument the Lean compiler
caches the closed term and every row measures nothing.
-/

open Binary

def reps : Nat := 100000
def trials : Nat := 5

/-- One timed pass over `reps` iterations: elapsed nanoseconds and checksum. -/
def onePass (act : Nat → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut checksum := 0
  for i in [0:reps] do
    checksum := checksum + act i
  let t1 ← IO.monoNanosNow
  return (t1 - t0, checksum)

/-- Discard one warmup pass, then report the fastest of `trials`.  A single
unwarmed pass tracks machine state closely enough that whole tables drift 20%
between runs; the minimum is the pass least perturbed by the scheduler. -/
def timeIt (label : String) (act : Nat → Nat) : IO Unit := do
  let _ ← onePass act
  let mut best := 0
  let mut checksum := 0
  for _ in [0:trials] do
    let (ns, c) ← onePass act
    checksum := c
    if best == 0 || ns < best then best := ns
  IO.println s!"  {label}: {best / reps} ns/op  (checksum {checksum % 97})"

def w : Nat := 0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0

/-! The layered pipeline, written out so `@[csimp]` cannot rewrite it. -/

def encodeLEURef (len n : Nat) : List UInt8 := natsToUInt8 (encodeLE len n)
def encodeBEURef (len n : Nat) : List UInt8 := natsToUInt8 (encodeBE len n)
def encodeLEBytesRef (len n : Nat) : ByteArray := (natsToUInt8 (encodeLE len n)).toByteArray
def encodeBEBytesRef (len n : Nat) : ByteArray := (natsToUInt8 (encodeBE len n)).toByteArray
def decodeLEURef (bs : List UInt8) : Nat := decodeLE (uint8ToNats bs)
def decodeBEURef (bs : List UInt8) : Nat := decodeBE (uint8ToNats bs)
def decodeBEBytesRef (ba : ByteArray) : Nat := decodeBE (uint8ToNats ba.data.toList)
def decodeLEBytesRef (ba : ByteArray) : Nat := decodeLE (uint8ToNats ba.data.toList)

/-! The minimal and signed codecs, routed through the `List Nat` pipeline —
what a module that misses the `Binary.Fast` import scoping (or a signed layer
that delegated down to `encodeBE`) would actually compile. These rows guard
the regression the library docs warn about. -/

def encodeBEMinBytesRef (n : Nat) : ByteArray :=
  (natsToUInt8 (encodeBE (minBytes n) n)).toByteArray
def encodeTwosBEBytesRef (len : Nat) (v : Int) : ByteArray :=
  (natsToUInt8 (encodeBE len (twosRep len v))).toByteArray

/-- Time one full pass over every word of a buffer, reported per word. -/
def timeItWords (label : String) (words : Nat) (read : Nat → Nat) : IO Unit := do
  let pass : IO (Nat × Nat) := do
    let t0 ← IO.monoNanosNow
    let mut checksum := 0
    for i in [0:words] do
      checksum := checksum + read (i * 32) % 97
    let t1 ← IO.monoNanosNow
    return (t1 - t0, checksum)
  let _ ← pass
  let mut best := 0
  let mut checksum := 0
  for _ in [0:trials] do
    let (ns, c) ← pass
    checksum := c
    if best == 0 || ns < best then best := ns
  IO.println s!"  {label}: {best / words} ns/word  (checksum {checksum % 97})"

/-! ## word operations

`UInt256` stores limbs, but `add`/`and`/... are specified — and were computed —
as `ofBitVec (a.toBitVec ∘ b.toBitVec)`.  `BitVec 256` is a `Fin (2 ^ 256)` is a
`Nat`, so that route rebuilds a bignum from the limbs, operates on it, and takes
it apart again: about ten allocations where a handful of register ops would do.

Every operation below is `@[csimp]`-swapped for a limb-native version, and each
costs what its structure costs: the bitwise three are limbwise, `add` carries,
`sub` is two adds and a complement, `mul` is six full limb products and four
wrapping ones, accumulated branch-free.
Only the shifts are left on the `BitVec` route — see `Binary.UInt256`. -/

def opWords : Array UInt256 :=
  (List.range 256).toArray.map fun i =>
    ⟨0x1234567890abcdef, 0xfedcba0987654321, 0x0f1e2d3c4b5a6978, 0x1122334455667788 + i.toUInt64⟩

/-- `n` applications, returning a checksum so nothing is dead code.  `n` reaches
the loop, or Lean floats the whole call into a cached constant.

`f` is a parameter, so every row pays an indirect call the operation itself
would not — read these against each other, not as the cost of one `&&&`. -/
def opRun (f : UInt256 → UInt256 → UInt256) (n : Nat) : Nat := Id.run do
  let mut acc : UInt64 := 0
  for i in [0:n] do
    acc := acc ^^^ (f opWords[i % 256]! opWords[(i + 7) % 256]!).l3
  return acc.toNat

/-! ## filling a buffer with words

The three routes a caller has for putting `words` words into a buffer:
appending whole encodings (the `HAppend` route, already `@[csimp]`-fast
underneath), copying encodings into a pre-sized buffer (`copySlice`), and
the limb-direct in-place writer.  The target is uniquely referenced in all
three, so the rows are about the writes themselves, not buffer cloning. -/

/-- Append whole encodings to a growing buffer. -/
def fillAppend (words : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (words * 32)
  for i in [0:words] do
    b := b ++ UInt256.toBEByteArray opWords[i % 256]!
  return b

/-- Copy encodings into a pre-sized buffer, one `copySlice` per word. -/
def fillCopy (words : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.mk (Array.replicate (words * 32) 0)
  for i in [0:words] do
    b := ByteArray.copySlice (UInt256.toBEByteArray opWords[i % 256]!) 0 b (i * 32) 32
  return b

/-- Write the words straight into a pre-sized buffer, `writeBEAt` per word.
The recursive form carries the size invariant (`b.size = words * 32`) and the
`USize`-fits hypothesis explicitly; the `for` loop would not expose either. -/
def fillWriteAtAux (words : Nat) (hcap : words * 32 < USize.size)
    (i : Nat) (hi : i ≤ words) (b : ByteArray) (hb : b.size = words * 32) : ByteArray :=
  if h : i < words then
    fillWriteAtAux words hcap (i + 1) (by omega)
      (UInt256.writeBEAt opWords[i % 256]! b (USize.ofNat (i * 32))
        (by
          have hoff : (USize.ofNat (i * 32)).toNat = i * 32 :=
            USize.toNat_ofNat_of_lt' (by
              rw [USize.size_eq_two_pow] at hcap ⊢
              cases System.Platform.numBits_eq with
              | inl hb2 => simp [hb2] at hcap ⊢; omega
              | inr hb2 => simp [hb2] at hcap ⊢; omega)
          rw [hoff, hb]; omega))
      (by rw [UInt256.size_writeBEAt]; exact hb)
  else
    b
termination_by words - i

def fillWriteAt (words : Nat) (hcap : words * 32 < USize.size) : ByteArray :=
  fillWriteAtAux words hcap 0 (by omega) (ByteArray.mk (Array.replicate (words * 32) 0))
    (by simp [ByteArray.size])

def fillPushBE (words : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (words * 32)
  for i in [0:words] do
    b := UInt256.pushBE opWords[i % 256]! b
  return b

def benchOps : IO Unit := do
  IO.println "== word operations (2000 per call) =="
  timeItWords "and " 64 (fun i => opRun UInt256.and (2000 + i % 3))
  timeItWords "or  " 64 (fun i => opRun UInt256.or  (2000 + i % 3))
  timeItWords "xor " 64 (fun i => opRun UInt256.xor (2000 + i % 3))
  timeItWords "add " 64 (fun i => opRun UInt256.add (2000 + i % 3))
  timeItWords "sub " 64 (fun i => opRun UInt256.sub (2000 + i % 3))
  timeItWords "mul " 64 (fun i => opRun UInt256.mul (2000 + i % 3))

def main : IO Unit := do
  benchOps
  IO.println "== encode one 32-byte word =="
  timeIt "baseline: one bignum add" (fun i => (w + i) % 256)
  timeIt "encodeBEU        (ref) " (fun i => (encodeBEURef 32 (w + i)).length)
  timeIt "encodeBEU        (now) " (fun i => (encodeBEU 32 (w + i)).length)
  timeIt "encodeLEU        (ref) " (fun i => (encodeLEURef 32 (w + i)).length)
  timeIt "encodeLEU        (now) " (fun i => (encodeLEU 32 (w + i)).length)
  timeIt "encodeBEBytes    (ref) " (fun i => (encodeBEBytesRef 32 (w + i)).size)
  timeIt "encodeBEBytes    (now) " (fun i => (encodeBEBytes 32 (w + i)).size)
  timeIt "encodeLEBytes    (ref) " (fun i => (encodeLEBytesRef 32 (w + i)).size)
  timeIt "encodeLEBytes    (now) " (fun i => (encodeLEBytes 32 (w + i)).size)
  IO.println "== encode one 32-byte word, width computed / signed =="
  timeIt "encodeBEMinBytes (ref) " (fun i => (encodeBEMinBytesRef (w + i)).size)
  timeIt "encodeBEMinBytes (now) " (fun i => (encodeBEMinBytes (w + i)).size)
  timeIt "encodeTwosBEBytes(ref) " (fun i => (encodeTwosBEBytesRef 32 (-(w + i : Int))).size)
  timeIt "encodeTwosBEBytes(now) " (fun i => (encodeTwosBEBytes 32 (-(w + i : Int))).size)
  IO.println "== decode one 32-byte word =="
  let bs := encodeBEU 32 w
  let ba := encodeBEBytes 32 w
  timeIt "decodeBEU        (ref) " (fun i => decodeBEURef bs % 97 + i % 2)
  timeIt "decodeBEU        (now) " (fun i => decodeBEU bs % 97 + i % 2)
  timeIt "decodeLEU        (ref) " (fun i => decodeLEURef bs % 97 + i % 2)
  timeIt "decodeLEU        (now) " (fun i => decodeLEU bs % 97 + i % 2)
  timeIt "decodeBEBytes    (ref) " (fun i => decodeBEBytesRef ba % 97 + i % 2)
  timeIt "decodeBEBytes    (now) " (fun i => decodeBEBytes ba % 97 + i % 2)
  timeIt "decodeLEBytes    (ref) " (fun i => decodeLEBytesRef ba % 97 + i % 2)
  timeIt "decodeLEBytes    (now) " (fun i => decodeLEBytes ba % 97 + i % 2)
  IO.println "== read every 32-byte word out of one buffer =="
  -- What a field-at-a-time reader does: the slicing spelled out (`ref`) walks
  -- the buffer from the front for every window, so the pass is quadratic in
  -- the word count; the windowed read is O(32) per word.
  for words in [16, 128] do
    let buf := encodeBEBytes (words * 32) w
    IO.println s!"-- {words} words ({buf.size} bytes)"
    timeItWords "slice + decode      (ref) " words
      (fun off => decodeBEU ((buf.data.toList.drop off).take 32))
    timeItWords "decodeBEBytesFrom   (now) " words
      (fun off => decodeBEBytesFrom buf off 32)
  -- The buffer above is one value zero-padded to width, so all but its last
  -- word are zero — the cheap case, where the accumulator never leaves zero.
  -- This one is full width in every word, which is what an ABI `uint256[]` of
  -- amounts or hashes is, and it is what the `Nat` codec is slowest at.
  let wide : ByteArray := Id.run do
    let mut b := ByteArray.emptyWithCapacity (128 * 32)
    for i in [0:128] do
      b := b ++ encodeBEBytes 32 (w + i)
    return b
  IO.println s!"-- 128 words, every one full width ({wide.size} bytes)"
  timeItWords "decodeBEBytesFrom (as Nat) " 128
    (fun off => decodeBEBytesFrom wide off 32)
  -- the same word read straight into limbs: no `Nat` is built at all
  timeItWords "ofBEByteArrayAt  (as limbs)" 128
    (fun off => if h : off + 32 ≤ wide.size then
        let v := UInt256.ofBEByteArrayAt wide off h
        (v.l0 ^^^ v.l1 ^^^ v.l2 ^^^ v.l3).toNat
      else 0)
  IO.println "== write one word into a shared buffer =="
  -- The target is shared with the closure, so every route pays the same
  -- one copy of it; the rows isolate the write itself.  `ref` is the list
  -- splice `writeBEAt_eq` states, `ref2` the practical copy route a caller
  -- had before: encode to a fresh array, `copySlice` it in.
  let buf64 := encodeBEBytes (64 * 32) w
  have hbuf : buf64.size = 64 * 32 := by
    change (encodeBEBytes (64 * 32) w).size = 64 * 32
    simp only [size_encodeBEBytes]
  timeIt "splice take++enc++drop (ref) " (fun i =>
    let off := i % 64 * 32
    let x := opWords[i % 256]!
    ((buf64.data.toList.take off ++ UInt256.toBEBytes x
      ++ buf64.data.toList.drop (off + 32)).toByteArray).size)
  timeIt "copySlice of encode    (ref2)" (fun i =>
    (ByteArray.copySlice (UInt256.toBEByteArray opWords[i % 256]!) 0
      buf64 (i % 64 * 32) 32).size)
  timeIt "writeBEAt              (now) " (fun i =>
    let off := i % 64 * 32
    have hsize : off < USize.size := by
      rw [USize.size_eq_two_pow]
      cases System.Platform.numBits_eq with
      | inl h => simp [h]; omega
      | inr h => simp [h]; omega
    have hoff : (USize.ofNat off).toNat = off := USize.toNat_ofNat_of_lt' hsize
    (UInt256.writeBEAt opWords[i % 256]! buf64 (USize.ofNat off)
      (by rw [hoff]; omega)).size)
  timeIt "writeLEAt              (now) " (fun i =>
    let off := i % 64 * 32
    have hsize : off < USize.size := by
      rw [USize.size_eq_two_pow]
      cases System.Platform.numBits_eq with
      | inl h => simp [h]; omega
      | inr h => simp [h]; omega
    have hoff : (USize.ofNat off).toNat = off := USize.toNat_ofNat_of_lt' hsize
    (UInt256.writeLEAt opWords[i % 256]! buf64 (USize.ofNat off)
      (by rw [hoff]; omega)).size)
  IO.println "== fill a fresh 64-word buffer (unique target) =="
  timeIt "++ toBEByteArray    (ref) " (fun i => (fillAppend (64 + i % 3)).size)
  timeIt "copySlice loop      (ref2)" (fun i => (fillCopy (64 + i % 3)).size)
  timeIt "writeBEAt loop     (now) " (fun i =>
    let words := 64 + i % 3
    (fillWriteAt words (by
      rw [USize.size_eq_two_pow]
      cases System.Platform.numBits_eq with
      | inl h => simp [h]; omega
      | inr h => simp [h]; omega)).size)
  IO.println "== append one word (push) =="
  timeIt "pushBE             (now) " (fun i => (fillPushBE (64 + i % 3)).size)
  IO.println "== agreement (this is what the @[csimp] theorems assert) =="
  IO.println s!"  encodeBEU     {encodeBEU 32 w == encodeBEURef 32 w}   \
encodeLEU     {encodeLEU 32 w == encodeLEURef 32 w}"
  IO.println s!"  encodeBEBytes {encodeBEBytes 32 w == encodeBEBytesRef 32 w}   \
encodeLEBytes {encodeLEBytes 32 w == encodeLEBytesRef 32 w}"
  IO.println s!"  decodeBEU     {decodeBEU bs == decodeBEURef bs}   \
decodeLEU     {decodeLEU bs == decodeLEURef bs}"
  IO.println s!"  decodeBEBytes {decodeBEBytes ba == decodeBEBytesRef ba}   \
decodeLEBytes {decodeLEBytes ba == decodeLEBytesRef ba}"
  IO.println s!"  encodeBEMinBytes {encodeBEMinBytes w == encodeBEMinBytesRef w}   \
encodeTwosBEBytes {encodeTwosBEBytes 32 (-(w : Int)) == encodeTwosBEBytesRef 32 (-(w : Int))}"
