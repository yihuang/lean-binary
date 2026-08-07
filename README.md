# Binary — a Lean 4 big-endian / little-endian byte-order codec library

Endianness encoding/decoding with **machine-checked proofs** of all core
properties — fixed-width, minimal-length, and two's-complement signed. Written
against the Lean 4 core library only — **no mathlib dependency**.

- Toolchain: `leanprover/lean4:v4.32.0`
- Build: `lake build` (zero `sorry`; includes examples and computation-checked instances)

## Project layout

```
binary/
├── lakefile.toml
├── lean-toolchain
├── Binary.lean            # root module (re-exports everything)
└── Binary/
    ├── Core.lean              # List Nat byte strings: codecs + all core proofs
    ├── UInt8.lean             # List UInt8 interface + roundtrips
    ├── ByteArray.lean         # ByteArray runtime interface + roundtrips
    ├── Fast.lean              # efficient compiled implementations (@[csimp])
    ├── Fixed.lean             # UInt16/32/64 fixed-width codecs + roundtrips
    ├── Minimal.lean           # minimal-length BE codec (EVM/ABI convention)
    ├── Signed.lean            # two's-complement BE codec (signed EVM/ABI ints)
    ├── UInt256.lean           # 256-bit unsigned integer (EVM word) + codecs
    ├── Examples.lean          # usage examples and computation-checked instances
    └── ../Bench.lean          # `lake build bench` — measures Fast against the definitions
```

## Layered design

| Layer | Byte-string representation | Role |
|---|---|---|
| `Core` | `List Nat` with `IsBytes bs := ∀ b ∈ bs, b < 256` | the mathematical core; every proof happens here |
| `UInt8` | `List UInt8` | practical interface; properties lifted from Core |
| `ByteArray` | `ByteArray` | runtime I/O interface |
| `Fast` | — | efficient implementations of all of the above, proved equal and registered `@[csimp]` |
| `Fixed` | `UInt16/32/64 ↔ List UInt8` | fixed-width codecs |
| `Minimal` | all three | shortest BE encoding of a `Nat`; width computed, not given |
| `Signed` | all three | two's-complement BE codec for `Int` |
| `UInt256` | `UInt256 ↔ List UInt8` / `ByteArray` | 256-bit word (EVM), wraps `BitVec 256` |

Encoding semantics: `encodeBE len n` / `encodeLE len n` produce exactly `len`
bytes; when `n ≥ 256^len` the value is truncated (i.e. `n mod 256^len` is
encoded), so roundtrip theorems take `n < 256^len` as their hypothesis.

## Performance (`Binary.Fast`)

The definitions above are layered for the proofs: `encodeBEU` is `encodeBE`
mapped into `UInt8`, `encodeBE` is `encodeLE` reversed, `encodeBEBytes` is
`encodeBEU` packed into a `ByteArray`.  That is the right shape for reasoning
and the wrong shape for running.

The dominant cost is not the intermediate lists — it is `encodeLE`'s digit
recursion, `(n % 256) :: encodeLE len (n / 256)`.  For a full-width 32-byte
word, each `/` and `%` is a GMP call that allocates, so one word costs 32 of
them.  Decoding mirrors it: one bignum multiply-and-add per byte.

`Binary.Fast` peels **eight bytes at a time** instead.  `UInt64.ofNat n` takes
the low 64 bits into a machine word (no allocation), those eight bytes are
produced or consumed with `UInt64` shifts and multiplies (free), and a single
`n >>> 64` advances to the next chunk — 4 bignum operations per 32-byte word
instead of 32.

Every fast implementation is registered with `@[csimp]` on the strength of an
ordinary theorem (`encodeBEU_eq_fast : @encodeBEU = @encodeBEUFast` and so on),
so **the definitions and all their theorems are untouched** and callers need no
code changes. Nothing is added to the trusted base: deleting the `@[csimp]`
attributes would change performance and nothing else.

Measured by `lake build bench && ./.lake/build/bin/bench` in a foreground
shell, one full-width 32-byte word, Apple M4 Max, compiled (`ref` is the
layered pipeline written out so `@[csimp]` cannot rewrite it).  Each row
discards a warmup pass and reports the fastest of five:

| codec | ref | now | speedup |
|---|---|---|---|
| `encodeBEU` | 3732 ns | 655 ns | 5.7× |
| `encodeLEU` | 3706 ns | 673 ns | 5.5× |
| `encodeBEBytes` | 3728 ns | 502 ns | 7.4× |
| `encodeLEBytes` | 3734 ns | 472 ns | 7.9× |
| `decodeBEU` | 5639 ns | 723 ns | 7.8× |
| `decodeLEU` | 5748 ns | 1031 ns | 5.6× |
| `decodeBEBytes` | 5715 ns | 970 ns | 5.9× |
| `decodeLEBytes` | 5802 ns | 1138 ns | 5.1× |

The absolute figures are scheduling-context dependent: run under a QoS clamp
of `utility` — CI runners, background agents — every row including the
baseline reads 15–20% slower, uniformly, so compare only within one context.
The speedup column is unaffected.

Roughly 225 ns of every row is the benchmark's own loop (one bignum add per
iteration, to defeat the compiler's closed-term caching); net of it the codecs
are 6–14× faster, the `ByteArray` encoders gaining most and the little-endian
decoders least.  Values below `2 ^ 63` are unboxed and never took the bignum
path, so short widths and small values see little change — the gain is exactly
where real EVM data lives: hashes, addresses and token amounts.

Two facts carry the whole chunking argument.  They are ordinary statements
about the specification, so they live in `Binary.Core` (with `Binary.UInt8`
liftings) rather than in `Fast`:

```lean4
theorem encodeLE_add (a b n : Nat) :
    encodeLE (a + b) n = encodeLE a n ++ encodeLE b (n / 256 ^ a)

theorem encodeLE_mod_of_dvd {len m n : Nat} (h : 256 ^ len ∣ m) :
    encodeLE len (n % m) = encodeLE len n
```

The first says a fixed-width encoding may be computed in pieces; the second
says the low `len` bytes only depend on `n` modulo anything `256 ^ len`
divides — which is what makes it sound to read a chunk out of a truncating
`UInt64`.

`@[csimp]` rewrites calls in modules compiled *after* the attribute is in
scope, so `Binary.Fast` is imported by `Binary.Fixed`, `Binary.UInt256`,
`Binary.Minimal` and `Binary.Signed` rather than the other way round;
anything downstream of those gets the fast code too.

This is load-bearing, not tidiness: a module that builds on the codecs but
imports only `Binary.ByteArray` compiles against the *reference* pipeline
and silently forfeits the whole speedup — `encodeBEMinBytes` on a full-width
word measured 5162 ns/op that way against 953 ns/op with `Binary.Fast` in
scope, for identical work.  The bench measures exactly this pair of
regressions (`encodeBEMinBytes` and `encodeTwosBEBytes`, `ref` against
`now`), so the ratio is reproducible with `lake build bench`.

### Remaining

`decodeLEBytes`/`decodeBEBytes` reach the chunked decoders through
`ByteArray.data`, an `@[extern]` conversion that copies the packed bytes into
a boxed `Array UInt8`.  Chunking the `ByteArray` index loop directly would
save the copy.  (An index loop that saved the copy but decoded byte-at-a-time
was tried and was six times *slower* — the copy is cheap next to the bignum
arithmetic.)

## Theorem index

### Core layer (`Binary.Core`)

| Theorem | Statement |
|---|---|
| `decodeLE_encodeLE` / `decodeBE_encodeBE` | `n < 256^len → decode (encode len n) = n` (**roundtrip**) |
| `encodeLE_decodeLE` / `encodeBE_decodeBE` | `IsBytes bs → encode bs.length (decode bs) = bs` (**roundtrip**) |
| `decodeLE_lt` / `decodeBE_lt` | `IsBytes bs → decode bs < 256^bs.length` (upper bound) |
| `length_encodeLE` / `length_encodeBE` | `(encode len n).length = len` (`@[simp]`) |
| `isBytes_encodeLE` / `isBytes_encodeBE` | encodings are always valid byte strings |
| `encodeLE_injective` / `encodeBE_injective` | fixed-length encoding is injective below `256^len` |
| `decodeLE_injective` / `decodeBE_injective` | decoding is injective on valid strings of equal length |
| `decodeLE_append` | `decodeLE (xs ++ ys) = decodeLE xs + 256^xs.length * decodeLE ys` |
| `decodeBE_append` | `decodeBE (xs ++ ys) = decodeBE xs * 256^ys.length + decodeBE ys` |
| `encodeBE_succ` | `encodeBE (len+1) n = encodeBE len (n/256) ++ [n%256]` |
| `encodeBE_cons` | `encodeBE (len+1) n = n/256^len % 256 :: encodeBE len n` (from the front; `encodeBE_one` is the base) |
| `decodeBE_snoc` | `decodeBE (bs ++ [b]) = decodeBE bs * 256 + b` |
| `encodeLE_add` / `encodeBE_add` | `encodeLE (a+b) n = encodeLE a n ++ encodeLE b (n/256^a)` (**splitting**) |
| `encodeLE_mod` | `encodeLE len (n % 256^len) = encodeLE len n` (**truncation**) |
| `encodeLE_mod_of_dvd` / `encodeBE_mod_of_dvd` | `256^len ∣ m → encode len (n % m) = encode len n` |

### UInt8 layer (`Binary.UInt8`)

`encodeLEU/encodeBEU : Nat → Nat → List UInt8`, `decodeLEU/decodeBEU : List UInt8 → Nat`.
Roundtrips: `decodeLEU_encodeLEU`, `decodeBEU_encodeBEU`, `encodeLEU_decodeLEU`,
`encodeBEU_decodeBEU`; unconditional bounds `decodeLEU_lt`, `decodeBEU_lt`;
length lemmas (`@[simp]`). Bridging: `UInt8.ofNat_toNat`,
`uint8ToNats_natsToUInt8`, `natsToUInt8_uint8ToNats`.

The Core splitting/truncation/concatenation laws lifted: `encodeLEU_add` /
`encodeBEU_add`, `encodeLEU_mod_of_dvd` / `encodeBEU_mod_of_dvd`,
`encodeLEU_succ` / `encodeBEU_succ`, `decodeBEU_append` / `decodeLEU_append`,
`decodeBEU_cons`, `decodeBEU_reverse`, and the fold characterisations
`decodeBEU_foldl` / `decodeLEU_foldr`.

### ByteArray layer (`Binary.ByteArray`)

`encodeLEBytes/encodeBEBytes : Nat → Nat → ByteArray`, `decodeLEBytes/decodeBEBytes : ByteArray → Nat`.
Roundtrips: `decodeLEBytes_encodeLEBytes`, `decodeBEBytes_encodeBEBytes`,
`encodeLEBytes_decodeLEBytes_size`, `encodeBEBytes_decodeBEBytes_size`;
unconditional bounds `decodeLEBytes_lt` / `decodeBEBytes_lt`;
`size_encodeLEBytes` / `size_encodeBEBytes` (`@[simp]`).

Windowed reads for decoding a field out of a larger buffer:
`decodeBEBytesFrom / decodeLEBytesFrom : ByteArray → Nat → Nat → Nat` give
the value of the `len` bytes at offset `off`, specified by `drop`/`take` so
they compose with the list theory, and clamped to the buffer exactly as
`take` clamps.  `decodeBEBytesFrom_zero` / `decodeLEBytesFrom_zero` recover
the whole-buffer decoders.  `Binary.Fast` implements the big-endian one by
index, so a reader that walks many fields of one buffer never slices it.

### Fast layer (`Binary.Fast`)

The general splitting and truncation laws live in `Core`/`UInt8` above; this
layer adds only what is specific to the 64-bit window.

The window: `two_pow_64_eq`, `shiftRight_64`, `shiftLeft_64`,
`pow256_dvd_two_pow_64`, `encodeLEU_window` / `encodeBEU_window`,
`encodeLEU_chunk` / `encodeBEU_chunk`.
Machine-word chunks: `leChunk_eq`, `beChunk_eq`, `pushLEChunk_eq`,
`pushBEChunk_eq`, `toNat_foldl_beWordStep`, `toNat_beWord8`.
Windowed reads: `window_peel`, `window_length`, `window_chunk8`,
`decodeBEFromFast.byteLoop_eq`, `decodeBEFromFast.loop_eq`.
The `@[csimp]` bridges: `encodeLEU_eq_fast`, `encodeBEU_eq_fast`,
`encodeLEBytes_eq_fast`, `encodeBEBytes_eq_fast`, `decodeLEU_eq_fast`,
`decodeBEU_eq_fast`, `decodeLEBytes_eq_fast`, `decodeBEBytes_eq_fast`,
`decodeBEBytesFrom_eq_fast`.

Reading every 32-byte word out of one buffer, compiled (`ref` spells the
slicing out so `@[csimp]` cannot rewrite it):

    16 words  (512B)    3833 -> 80 ns/word
    128 words (4096B)  29727 -> 32 ns/word

The `ref` column grows with the buffer because each window re-walks it from
the front; the windowed read does not.

### Fixed layer (`Binary.Fixed`)

For each `T ∈ {UInt16, UInt32, UInt64}` (width `k ∈ {2, 4, 8}`):

- `T.toBEBytes / T.toLEBytes : T → List UInt8`, `T.ofBEBytes / T.ofLEBytes : List UInt8 → T`
- `T.ofBEBytes_toBEBytes` / `T.ofLEBytes_toLEBytes`: decode after encode
- `T.toBEBytes_ofBEBytes` / `T.toLEBytes_ofLEBytes`: encode after decode, given `bs.length = k`
- `T.length_toBEBytes` / `T.length_toLEBytes` (`@[simp]`)

### Minimal layer (`Binary.Minimal`)

The shortest byte string that decodes back to `n`, as opposed to the fixed-width
codecs above where you supply the width. `0` encodes as a single `0x00`, matching the
EVM convention rather than the empty string.

| Theorem | Statement |
|---|---|
| `minBytes` | the width: `Nat.log2 n / 8 + 1` (and `1` at `n = 0`) |
| `minBytes_spec` | `0 < len → (n < 256^len ↔ minBytes n ≤ len)` (**minimality**: the LEAST width that fits) |
| `lt_pow_minBytes` | `n < 256 ^ minBytes n` (the width works) |
| `minBytes_le_of_lt` | `n < 256^len → 0 < len → minBytes n ≤ len` |
| `lt_minBytes_of_le` | `256^len ≤ n → len < minBytes n` (the dual; the lower-bound half of both exact-width lemmas) |
| `minBytes_eq_of_byte_range` | `256^(k-1) ≤ n < 256^k → minBytes n = k` (**exact width**, the natural byte-range form) |
| `minBytes_eq_of_range` | `2^(8k-1) ≤ n < 2^(8k) → minBytes n = k` (bit-length form; narrower — only values whose top byte has its high bit set) |
| `minBytes_div` | `256 ≤ n → minBytes n = minBytes (n/256) + 1` (base-256 recursion, derived from the spec — no `log2` reasoning) |
| `minBytes_eq_one` | `n < 256 → minBytes n = 1` (base case) |
| `pow_minBytes_pred_le` | `n ≠ 0 → 256^(minBytes n − 1) ≤ n` (the top byte's weight fits) |
| `decodeBE_encodeBEMin` (+ `U`/`Bytes`) | roundtrip — **no side condition**, the width is chosen to fit |
| `encodeBEMin_injective` | the minimal encoding is injective |
| `head_encodeBEMin_ne_zero` | `n ≠ 0 → (encodeBEMin n).head! ≠ 0` (**no leading zero** — false at `0`, which encodes as `[0x00]`) |
| `minBytes_le_length` (+ `U`/`size`) | a nonempty string decoding to `n` has at least `minBytes n` bytes (**shortest preimage**) |
| `length_encodeBEMin` / `size_encodeBEMinBytes` | `= minBytes n` (`@[simp]`) |

`minBytes_div` + `minBytes_eq_one` are what let a caller identify its own recursive
width function with `minBytes` by plain induction.  `head_encodeBEMin_ne_zero` and
`minBytes_le_length` are the width facts restated about the strings themselves:
the encoding wastes no leading zero byte, and nothing shorter decodes back.

### Signed layer (`Binary.Signed`)

Two's-complement big-endian, the convention signed EVM/ABI integers use. Each layer
is `ofTwosNat ∘ (the unsigned codec of that same layer) ∘ twosRep`, so the unsigned
theory carries over and every layer keeps its `Binary.Fast` implementation.

| Theorem | Statement |
|---|---|
| `twosRep len v` | the unsigned representative: `v.toNat`, or `(256^len + v).toNat` when negative |
| `InTwosRange len v` | `-256^len ≤ 2v < 256^len` — the usual `[-2^(8len-1), 2^(8len-1))`, stated without a truncating exponent (`Decidable`, so `by decide` discharges it) |
| `ofTwosNat len u` | the sign correction: `u` read back signed, testing the leading bit as `2u < 256^len` |
| `twosRep_lt` | in range, the representative fits in `len` bytes |
| `ofTwosNat_twosRep` | `InTwosRange len v → ofTwosNat len (twosRep len v) = v` (**the one fact behind all three roundtrips**) |
| `twosRep_ofTwosNat` | `u < 256^len → twosRep len (ofTwosNat len u) = u` (the dual inversion, behind the encode-after-decode direction) |
| `inTwosRange_ofTwosNat` | `u < 256^len → InTwosRange len (ofTwosNat len u)` (the sign correction lands in range) |
| `decodeTwosBE_encodeTwosBE` (+ `U`/`Bytes`) | **roundtrip**, given `InTwosRange` |
| `encodeTwosBE_decodeTwosBE` (+ `U`/`Bytes`) | **roundtrip, encode after decode** — `IsBytes` at the `List Nat` layer, no side condition above |
| `inTwosRange_decodeTwosBE` (+ `U`/`Bytes`) | decoded values are always representable — with the roundtrips, the codec is a **bijection** between `len`-byte strings and `InTwosRange len` |
| `encodeTwosBE_injective` | injective on representable values |
| `encodeTwosBEU_eq` / `encodeTwosBEBytes_eq` | `= encodeBEU/encodeBEBytes len (twosRep len v)` (bridge to the unsigned theory, by `rfl`) |
| `decodeTwosBEU_eq` / `decodeTwosBEBytes_eq` | the layers agree: each decoder is the one below it on the same bytes |
| `length_encodeTwosBE` / `size_encodeTwosBEBytes` | `= len` (`@[simp]`) |

`InTwosRange` is required, not decoration: out of range the encoding wraps —
`decodeTwosBE (encodeTwosBE 1 129) = -127`.

Each layer names its *own* unsigned codec rather than delegating down to the
`List Nat` one. That is deliberate: `encodeBE`/`decodeBE` carry no `@[csimp]`
attribute, so layers routed through them compile to the reference pipeline —
`encodeTwosBEBytes` measured 4879 ns/op that way against 672 ns/op now, for one
full-width word.

### UInt256 (`Binary.UInt256`)

A 256-bit unsigned integer (EVM word size) wrapping `BitVec 256`, in the same
style as core's `UInt8` … `UInt64`.

- Basics: `UInt256.ofNat`, `UInt256.toNat`, `UInt256.size = 2^256`;
  instances `OfNat` (numerals), `DecidableEq`, `BEq`, `Inhabited`, `Repr`, `ToString`
- Bridge lemmas: `toNat_lt`, `toNat_ofNat`, `toNat_inj`, `ofNat_toNat`, `toNat_lt_256`
- Wrap-around arithmetic/bitwise ops via instances: `Add`, `Sub`, `Mul`,
  `AndOp`, `OrOp`, `XorOp`, `Complement`, `HShiftLeft`, `HShiftRight`,
  with `toNat_add` / `toNat_mul` / `toNat_sub`
- Byte codec (32 bytes): `toBEBytes`, `toLEBytes`, `ofBEBytes`, `ofLEBytes`
- Roundtrips: `ofBEBytes_toBEBytes`, `ofLEBytes_toLEBytes`,
  `toBEBytes_ofBEBytes` / `toLEBytes_ofLEBytes` (given `bs.length = 32`)
- `ByteArray` codec (32 bytes): `toBEByteArray`, `toLEByteArray`,
  `ofBEByteArray`, `ofLEByteArray`
- Refinement lemmas: `toList_toBEByteArray` / `toList_toLEByteArray` and
  `ofBEByteArray_eq_ofBEBytes` / `ofLEByteArray_eq_ofLEBytes` (the `ByteArray`
  codec agrees with the `List UInt8` codec)
- `ByteArray` roundtrips: `ofBEByteArray_toBEByteArray`,
  `ofLEByteArray_toLEByteArray`, `toBEByteArray_ofBEByteArray` /
  `toLEByteArray_ofLEByteArray` (given `ba.size = 32`),
  `size_toBEByteArray` / `size_toLEByteArray` (`@[simp]`),
  `toNat_ofBEByteArray_of_size` / `toNat_ofLEByteArray_of_size`

## Usage examples

```lean
import Binary

-- Big-endian encoding: 0xDEADBEEF → [222, 173, 190, 239]
#eval Binary.encodeBE 4 0xDEADBEEF

-- Little-endian encoding: → [239, 190, 173, 222]
#eval Binary.encodeLE 4 0xDEADBEEF

-- Big-endian decoding → 3735928559
#eval Binary.decodeBE [222, 173, 190, 239]

-- Proving a concrete instance via the library theorem (no computation)
example : Binary.decodeBE (Binary.encodeBE 4 0xDEADBEEF) = 0xDEADBEEF :=
  Binary.decodeBE_encodeBE (by decide)

-- Minimal-length: the width is computed, not supplied. 0xDEADBEEF → [222,173,190,239]
#eval Binary.encodeBEMin 0xDEADBEEF
#eval (Binary.minBytes 255, Binary.minBytes 256)   -- → (1, 2)

-- Minimal roundtrip needs NO hypothesis
example : Binary.decodeBE (Binary.encodeBEMin 0xDEADBEEF) = 0xDEADBEEF :=
  Binary.decodeBE_encodeBEMin _

-- Signed: two's complement. -1 in one byte → [255]; -2 in four → [255,255,255,254]
#eval Binary.encodeTwosBE 1 (-1)
#eval Binary.decodeTwosBE [128]   -- → -128

-- Signed roundtrip, given representability
example : Binary.decodeTwosBE (Binary.encodeTwosBE 4 (-2)) = -2 :=
  Binary.decodeTwosBE_encodeTwosBE (by decide)

-- UInt256: 32-byte big-endian, roundtrip by theorem
example : Binary.UInt256.ofBEBytes (Binary.UInt256.toBEBytes (42 : Binary.UInt256)) = 42 :=
  Binary.UInt256.ofBEBytes_toBEBytes 42
```

## Using it as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "binary"
path = "../binary"
```

then `import Binary`.

## Building and verifying

```bash
elan toolchain install leanprover/lean4:v4.32.0   # if not already installed
lake build
```

`Binary/Examples.lean` prints real codec outputs via `#eval`, and several
`example`s verify concrete instances fully computationally with `decide` /
`native_decide`.
