import Binary.Fast

/-!
# Binary.Signed

Two's-complement big-endian codecs — the signed counterpart to `Binary.Core`'s
unsigned fixed-width ones, and the convention EVM/ABI signed integers use.

* `twosRep len v` — the unsigned representative of `v` in `len`-byte two's complement
* `InTwosRange len v` — representability: `-256^len ≤ 2v < 256^len`, i.e. the usual
  `[-2^(8len-1), 2^(8len-1))` stated without a truncating `- 1` in the exponent
* `ofTwosNat len u` — the sign correction: `u` read back as a signed value
* `encodeTwosBE` / `encodeTwosBEU` / `encodeTwosBEBytes` — the three layers
* `decodeTwosBE` / `decodeTwosBEU` / `decodeTwosBEBytes` — likewise
* `decodeTwosBE_encodeTwosBE` and friends — roundtrips, given `InTwosRange`

Each layer is the *unsigned* codec of that same layer, pre-composed with `twosRep`
and post-composed with `ofTwosNat`.  That is what makes the unsigned theory carry
over — and it is also why each layer names its own unsigned codec rather than
delegating down to the `List Nat` one: `encodeBE`/`decodeBE` carry no `@[csimp]`
attribute, so a layer routed through them would compile to the reference pipeline
and forfeit `Binary.Fast` entirely.

`InTwosRange` is genuinely required: out of range the encoding wraps
(`decodeTwosBE (encodeTwosBE 1 129) = -127`), so it is not a decorative
hypothesis.

Core library only — no mathlib. The `Int` arithmetic is discharged by `omega` over
`Int.toNat_of_nonneg`.
-/

namespace Binary

/-! ## Representative and range -/

/-- The unsigned representative of `v` in `len`-byte two's complement:
    non-negative values as themselves, negative ones offset by `256^len`. -/
def twosRep (len : Nat) (v : Int) : Nat :=
  if 0 ≤ v then v.toNat else ((256 ^ len : Nat) + v).toNat

/-- `v` is representable in `len`-byte two's complement. Equivalent to the usual
    `-2^(8len-1) ≤ v < 2^(8len-1)`, but stated as `-256^len ≤ 2v < 256^len` so that
    no truncating subtraction appears in an exponent. -/
def InTwosRange (len : Nat) (v : Int) : Prop :=
  -((256 ^ len : Nat) : Int) ≤ 2 * v ∧ 2 * v < ((256 ^ len : Nat) : Int)

/-- Representability is decidable, so callers can discharge the roundtrips'
    hypothesis with `by decide` on concrete values rather than building the
    conjunction by hand. -/
instance (len : Nat) (v : Int) : Decidable (InTwosRange len v) := by
  unfold InTwosRange; infer_instance

/-- In range, the representative fits in `len` bytes — what makes the unsigned
    encoder applicable. -/
theorem twosRep_lt (len : Nat) (v : Int) (h : InTwosRange len v) :
    twosRep len v < 256 ^ len := by
  obtain ⟨hlo, hhi⟩ := h
  unfold twosRep
  split
  · rename_i hv
    have : ((v.toNat : Nat) : Int) = v := Int.toNat_of_nonneg hv
    omega
  · rename_i hv
    have hnn : (0 : Int) ≤ ((256 ^ len : Nat) : Int) + v := by omega
    have : ((((256 ^ len : Nat) : Int) + v).toNat : Int) = ((256 ^ len : Nat) : Int) + v :=
      Int.toNat_of_nonneg hnn
    omega

/-- The sign correction: the `len`-byte unsigned value `u`, read back as a signed
    one.  The leading bit is tested as `2 * u < 256 ^ len`, matching `InTwosRange`'s
    doubled form so that no truncating exponent appears here either. -/
def ofTwosNat (len u : Nat) : Int :=
  if 2 * u < 256 ^ len then (u : Int) else (u : Int) - ((256 ^ len : Nat) : Int)

/-- **The one fact behind all three roundtrips**: the sign correction inverts the
    representative, for representable `v`.  Each layer's roundtrip is then its own
    unsigned roundtrip followed by this. -/
theorem ofTwosNat_twosRep {len : Nat} {v : Int} (h : InTwosRange len v) :
    ofTwosNat len (twosRep len v) = v := by
  obtain ⟨hlo, hhi⟩ := h
  unfold ofTwosNat twosRep
  split
  · rename_i hv
    have hcast : ((v.toNat : Nat) : Int) = v := Int.toNat_of_nonneg hv
    have hlt : 2 * v.toNat < 256 ^ len := by omega
    simp only [if_pos hlt]; omega
  · rename_i hv
    have hnn : (0 : Int) ≤ ((256 ^ len : Nat) : Int) + v := by omega
    have hcast : ((((256 ^ len : Nat) : Int) + v).toNat : Int) = ((256 ^ len : Nat) : Int) + v :=
      Int.toNat_of_nonneg hnn
    have hnot : ¬ (2 * (((256 ^ len : Nat) : Int) + v).toNat < 256 ^ len) := by omega
    simp only [if_neg hnot]; omega

/-- The dual inversion: the representative undoes the sign correction, for
    `u < 256 ^ len` — behind the encode-after-decode roundtrips the way
    `ofTwosNat_twosRep` is behind the decode-after-encode ones. -/
theorem twosRep_ofTwosNat {len u : Nat} (h : u < 256 ^ len) :
    twosRep len (ofTwosNat len u) = u := by
  unfold ofTwosNat
  split <;> (unfold twosRep; split <;> omega)

/-- The sign correction lands in range, for `u < 256 ^ len`.  Together with
    the two inversions this makes `twosRep len` and `ofTwosNat len` mutually
    inverse between the representable values and `[0, 256 ^ len)`. -/
theorem inTwosRange_ofTwosNat {len u : Nat} (h : u < 256 ^ len) :
    InTwosRange len (ofTwosNat len u) := by
  unfold InTwosRange ofTwosNat
  split <;> omega

/-! ## The codecs

Three layers, each `ofTwosNat ∘ (unsigned codec of that layer) ∘ twosRep`. -/

/-- Two's-complement big-endian encoding in `len` bytes, over `List Nat`. -/
def encodeTwosBE (len : Nat) (v : Int) : List Nat := encodeBE len (twosRep len v)

/-- Two's-complement big-endian decoding: the leading bit selects the sign. -/
def decodeTwosBE (bs : List Nat) : Int := ofTwosNat bs.length (decodeBE bs)

/-- `List UInt8` layer. -/
def encodeTwosBEU (len : Nat) (v : Int) : List UInt8 := encodeBEU len (twosRep len v)

/-- `List UInt8` layer. -/
def decodeTwosBEU (bs : List UInt8) : Int := ofTwosNat bs.length (decodeBEU bs)

/-- `ByteArray` layer. -/
def encodeTwosBEBytes (len : Nat) (v : Int) : ByteArray := encodeBEBytes len (twosRep len v)

/-- `ByteArray` layer. -/
def decodeTwosBEBytes (ba : ByteArray) : Int := ofTwosNat ba.size (decodeBEBytes ba)

/-! ## Bridges

Each signed codec is the unsigned one at the representative — definitionally, on
the encoding side — and the three layers agree with each other. -/

/-- The two's-complement encoding is the unsigned encoding of the representative. -/
theorem encodeTwosBEU_eq (len : Nat) (v : Int) :
    encodeTwosBEU len v = encodeBEU len (twosRep len v) := rfl

/-- The two's-complement encoding is the unsigned encoding of the representative. -/
theorem encodeTwosBEBytes_eq (len : Nat) (v : Int) :
    encodeTwosBEBytes len v = encodeBEBytes len (twosRep len v) := rfl

/-- The `UInt8` decoder is the `List Nat` one on the same bytes. -/
theorem decodeTwosBEU_eq (bs : List UInt8) : decodeTwosBEU bs = decodeTwosBE (uint8ToNats bs) := by
  rw [decodeTwosBEU, decodeTwosBE, decodeBEU, uint8ToNats, List.length_map]

/-- The `ByteArray` decoder is the `UInt8` one on the same bytes. -/
theorem decodeTwosBEBytes_eq (ba : ByteArray) :
    decodeTwosBEBytes ba = decodeTwosBEU ba.data.toList := by
  rw [decodeTwosBEBytes, decodeTwosBEU, decodeBEBytes, ByteArray.size_eq_toList_length]

/-! ## Lengths -/

@[simp] theorem length_encodeTwosBE (len : Nat) (v : Int) :
    (encodeTwosBE len v).length = len := by simp [encodeTwosBE]

@[simp] theorem length_encodeTwosBEU (len : Nat) (v : Int) :
    (encodeTwosBEU len v).length = len := by simp [encodeTwosBEU]

@[simp] theorem size_encodeTwosBEBytes (len : Nat) (v : Int) :
    (encodeTwosBEBytes len v).size = len := by simp [encodeTwosBEBytes]

/-! ## Roundtrips

Each is its own layer's unsigned roundtrip at `twosRep len v` — available because
`twosRep_lt` supplies the bound — followed by `ofTwosNat_twosRep`. -/

/-- **Roundtrip (`List Nat`)**: two's-complement decode after encode is the identity,
    for representable `v`. -/
theorem decodeTwosBE_encodeTwosBE {len : Nat} {v : Int} (h : InTwosRange len v) :
    decodeTwosBE (encodeTwosBE len v) = v := by
  rw [decodeTwosBE, length_encodeTwosBE, encodeTwosBE, decodeBE_encodeBE (twosRep_lt len v h)]
  exact ofTwosNat_twosRep h

/-- **Roundtrip (`List UInt8`)**. -/
theorem decodeTwosBEU_encodeTwosBEU {len : Nat} {v : Int} (h : InTwosRange len v) :
    decodeTwosBEU (encodeTwosBEU len v) = v := by
  rw [decodeTwosBEU, length_encodeTwosBEU, encodeTwosBEU, decodeBEU_encodeBEU (twosRep_lt len v h)]
  exact ofTwosNat_twosRep h

/-- **Roundtrip (`ByteArray`)**. -/
theorem decodeTwosBEBytes_encodeTwosBEBytes {len : Nat} {v : Int} (h : InTwosRange len v) :
    decodeTwosBEBytes (encodeTwosBEBytes len v) = v := by
  rw [decodeTwosBEBytes, size_encodeTwosBEBytes, encodeTwosBEBytes,
    decodeBEBytes_encodeBEBytes (twosRep_lt len v h)]
  exact ofTwosNat_twosRep h

/-- The signed encoding is injective on representable values. -/
theorem encodeTwosBE_injective {len : Nat} {m n : Int}
    (hm : InTwosRange len m) (hn : InTwosRange len n)
    (h : encodeTwosBE len m = encodeTwosBE len n) : m = n := by
  have := congrArg decodeTwosBE h
  rwa [decodeTwosBE_encodeTwosBE hm, decodeTwosBE_encodeTwosBE hn] at this

/-! ## Roundtrips: encode after decode

The other direction of the bijection — its unsigned counterpart at
`twosRep_ofTwosNat` — and the fact that decoding only ever produces
representable values.  Together with the roundtrips above, the signed codec
is a bijection between `len`-byte strings and `InTwosRange len`. -/

/-- **Roundtrip (`List Nat`), encode after decode**: for valid byte strings. -/
theorem encodeTwosBE_decodeTwosBE {bs : List Nat} (h : IsBytes bs) :
    encodeTwosBE bs.length (decodeTwosBE bs) = bs := by
  rw [encodeTwosBE, decodeTwosBE, twosRep_ofTwosNat (decodeBE_lt h), encodeBE_decodeBE h]

/-- **Roundtrip (`List UInt8`), encode after decode** — no side condition. -/
theorem encodeTwosBEU_decodeTwosBEU (bs : List UInt8) :
    encodeTwosBEU bs.length (decodeTwosBEU bs) = bs := by
  rw [encodeTwosBEU, decodeTwosBEU, twosRep_ofTwosNat (decodeBEU_lt bs),
    encodeBEU_decodeBEU]

/-- **Roundtrip (`ByteArray`), encode after decode** — no side condition. -/
theorem encodeTwosBEBytes_decodeTwosBEBytes (ba : ByteArray) :
    encodeTwosBEBytes ba.size (decodeTwosBEBytes ba) = ba := by
  rw [encodeTwosBEBytes, decodeTwosBEBytes, twosRep_ofTwosNat (decodeBEBytes_lt ba),
    encodeBEBytes_decodeBEBytes_size]

/-- Decoded values are always representable (`List Nat` layer). -/
theorem inTwosRange_decodeTwosBE {bs : List Nat} (h : IsBytes bs) :
    InTwosRange bs.length (decodeTwosBE bs) :=
  inTwosRange_ofTwosNat (decodeBE_lt h)

/-- Decoded values are always representable (`List UInt8` layer). -/
theorem inTwosRange_decodeTwosBEU (bs : List UInt8) :
    InTwosRange bs.length (decodeTwosBEU bs) :=
  inTwosRange_ofTwosNat (decodeBEU_lt bs)

/-- Decoded values are always representable (`ByteArray` layer). -/
theorem inTwosRange_decodeTwosBEBytes (ba : ByteArray) :
    InTwosRange ba.size (decodeTwosBEBytes ba) :=
  inTwosRange_ofTwosNat (decodeBEBytes_lt ba)

end Binary
