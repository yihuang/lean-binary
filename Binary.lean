import Binary.Core
import Binary.UInt8
import Binary.ByteArray
import Binary.Fast
import Binary.Fixed
import Binary.Minimal
import Binary.Signed
import Binary.UInt256
import Binary.Examples

/-!
# Binary

A big-endian / little-endian byte-order codec library with machine-checked
proofs, written against the Lean 4 core library only (no mathlib dependency).

* `Binary.Core` — codecs over `List Nat` byte strings and all core proofs
* `Binary.UInt8` — the practical `List UInt8` interface with roundtrips
* `Binary.ByteArray` — the `ByteArray` runtime interface with roundtrips
* `Binary.Fast` — efficient compiled implementations of every codec above,
  each proved equal to its definition and registered with `@[csimp]`
* `Binary.Fixed` — fixed-width `UInt16` / `UInt32` / `UInt64` codecs
* `Binary.Minimal` — minimal-length big-endian codec (the EVM/ABI convention)
* `Binary.Signed` — two's-complement big-endian codec (signed EVM/ABI integers)
* `Binary.UInt256` — a 256-bit unsigned integer (EVM word) with codecs
* `Binary.Examples` — usage examples and computation-checked instances
-/
