import Binary

/-!
# Difftest

`encodeBEBytesFast` and `decodeBEBytesFromFast` carry `@[extern]`, so the
bytes a compiled program moves come from `c/binary_shim.c` rather than from
the Lean bodies the theorems are about.  That is a trusted step, and this is
what keeps it honest: every case below runs the native codec against the
*specification* — `encodeBE`/`decodeBE` in `Binary.Core`, which carry neither
`@[csimp]` nor `@[extern]`, so they compile to exactly what they say.

Run with `lake build difftest && ./.lake/build/bin/difftest`; it exits
non-zero on the first disagreement.
-/

open Binary

/-- The specification's encoder, reachable at run time. -/
def refEncode (len n : Nat) : ByteArray := (natsToUInt8 (encodeBE len n)).toByteArray

/-- The specification's windowed decoder: clamp, then fold. -/
def refDecodeFrom (ba : ByteArray) (off len : Nat) : Nat :=
  decodeBE (uint8ToNats ((ba.data.toList.drop off).take len))

/-- Widths that straddle every chunk boundary the codec has. -/
def widths : List Nat := [0, 1, 2, 7, 8, 9, 15, 16, 17, 20, 23, 24, 25, 31, 32, 33, 40, 64]

/-- Values that straddle every representation boundary `Nat` has: unboxed,
one limb, several limbs, and past the width so truncation is exercised. -/
def values : List Nat :=
  [ 0, 1, 2, 255, 256, 65535,
    2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32,
    2 ^ 62, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1,          -- LEAN_MAX_SMALL_NAT
    2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 127, 2 ^ 128 - 1, 2 ^ 128,
    2 ^ 191, 2 ^ 192 - 1, 2 ^ 192,
    2 ^ 255, 2 ^ 256 - 1,
    2 ^ 256,                                          -- truncates at len 32
    2 ^ 300, 2 ^ 512 - 1,
    0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0,
    0xff00000000000000000000000000000000000000000000000000000000000001 ]

def main : IO UInt32 := do
  let mut fails := 0
  let mut cases := 0

  -- encode: the native buffer must be the specification's, byte for byte
  for len in widths do
    for n in values do
      cases := cases + 1
      let got := encodeBEBytesFast len n
      let want := refEncode len n
      if got != want then
        fails := fails + 1
        if fails ≤ 10 then
          IO.println s!"ENCODE len={len} n={n}\n  native {got.data.toList}\n  spec   {want.data.toList}"

  -- decode: over buffers the encoder produced, at every offset and width,
  -- including windows that start at or past the end and ones that overrun
  for len in widths do
    for n in values do
      let ba := refEncode len n
      for off in [0, 1, 7, 8, 31, 32, 33] do
        for w in [0, 1, 7, 8, 9, 31, 32, 33, 64] do
          cases := cases + 1
          let got := decodeBEBytesFromFast ba off w
          let want := refDecodeFrom ba off w
          if got != want then
            fails := fails + 1
            if fails ≤ 10 then
              IO.println s!"DECODE size={ba.size} off={off} w={w}\n  native {got}\n  spec   {want}"

  -- roundtrip at the ABI's width, which is the case the shim exists for
  for n in values do
    cases := cases + 1
    let ba := encodeBEBytesFast 32 n
    let back := decodeBEBytesFromFast ba 0 32
    if back != n % 2 ^ 256 then
      fails := fails + 1
      if fails ≤ 10 then
        IO.println s!"ROUNDTRIP n={n}\n  back {back}\n  want {n % 2 ^ 256}"

  IO.println s!"{cases} cases, {fails} disagreements"
  return (if fails == 0 then 0 else 1)
