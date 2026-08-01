import Binary.Core

/-!
# Binary.UInt8

The `List UInt8` layer: lifts every roundtrip property of `Binary.Core`
to the practical `List UInt8` interface.

The key bridging fact is that `UInt8.ofNat` and `UInt8.toNat` are mutually
inverse on valid bytes.
-/

namespace Binary

/-- `UInt8.ofNat` is a left inverse of `UInt8.toNat`
    (not provided in this form by the core library). -/
theorem UInt8.ofNat_toNat (x : UInt8) : UInt8.ofNat x.toNat = x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt x.toNat_lt]

/-- Convert a valid (`Nat`) byte string to a `UInt8` list. -/
def natsToUInt8 (bs : List Nat) : List UInt8 := bs.map UInt8.ofNat

/-- Convert a `UInt8` list to a `Nat` byte string. -/
def uint8ToNats (bs : List UInt8) : List Nat := bs.map UInt8.toNat

/-- Byte-wise fact: `toNat ∘ ofNat` is the identity on valid bytes. -/
theorem map_uint8ToNat_ofNat {bs : List Nat} (h : IsBytes bs) :
    bs.map (UInt8.toNat ∘ UInt8.ofNat) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b < 256 := h b (by simp)
      have hbs : IsBytes bs := fun x hx => h x (List.mem_cons_of_mem b hx)
      simp only [List.map_cons, ih hbs]
      congr 1
      show (UInt8.ofNat b).toNat = b
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hb]

/-- Byte-wise fact: `ofNat ∘ toNat` is the identity. -/
theorem map_uint8OfNat_toNat (bs : List UInt8) :
    bs.map (UInt8.ofNat ∘ UInt8.toNat) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, ih]
      congr 1
      exact UInt8.ofNat_toNat x

/-- The two byte-string representations are inverse on valid inputs (1/2). -/
theorem uint8ToNats_natsToUInt8 {bs : List Nat} (h : IsBytes bs) :
    uint8ToNats (natsToUInt8 bs) = bs := by
  simp only [uint8ToNats, natsToUInt8, List.map_map, map_uint8ToNat_ofNat h]

/-- The two byte-string representations are inverse (2/2). -/
theorem natsToUInt8_uint8ToNats (bs : List UInt8) :
    natsToUInt8 (uint8ToNats bs) = bs := by
  simp only [natsToUInt8, uint8ToNats, List.map_map, map_uint8OfNat_toNat]

/-- A `UInt8` list viewed as naturals is a valid byte string
    (every `toNat < 2^8 = 256`). -/
theorem isBytes_uint8ToNats (bs : List UInt8) : IsBytes (uint8ToNats bs) := by
  intro b hb
  simp only [uint8ToNats, List.mem_map] at hb
  obtain ⟨x, _, rfl⟩ := hb
  exact UInt8.toNat_lt x

/-! ## `List UInt8` codec interface -/

/-- Little-endian encoding to a `UInt8` list, least significant byte first. -/
def encodeLEU (len n : Nat) : List UInt8 := natsToUInt8 (encodeLE len n)

/-- Big-endian encoding to a `UInt8` list, most significant byte first. -/
def encodeBEU (len n : Nat) : List UInt8 := natsToUInt8 (encodeBE len n)

/-- Little-endian decoding of a `UInt8` list. -/
def decodeLEU (bs : List UInt8) : Nat := decodeLE (uint8ToNats bs)

/-- Big-endian decoding of a `UInt8` list. -/
def decodeBEU (bs : List UInt8) : Nat := decodeBE (uint8ToNats bs)

@[simp] theorem length_encodeLEU (len n : Nat) : (encodeLEU len n).length = len := by
  simp [encodeLEU, natsToUInt8]

@[simp] theorem length_encodeBEU (len n : Nat) : (encodeBEU len n).length = len := by
  simp [encodeBEU, natsToUInt8]

/-- **Roundtrip (UInt8 layer)**: decode after encode is the identity
    for `n < 256 ^ len`. -/
theorem decodeLEU_encodeLEU {len n : Nat} (h : n < 256 ^ len) :
    decodeLEU (encodeLEU len n) = n := by
  simp only [decodeLEU, encodeLEU, uint8ToNats_natsToUInt8 (isBytes_encodeLE len n),
    decodeLE_encodeLE h]

/-- **Roundtrip (UInt8 layer)**: decode after encode is the identity
    for `n < 256 ^ len` (big-endian). -/
theorem decodeBEU_encodeBEU {len n : Nat} (h : n < 256 ^ len) :
    decodeBEU (encodeBEU len n) = n := by
  simp only [decodeBEU, encodeBEU, uint8ToNats_natsToUInt8 isBytes_encodeBE,
    decodeBE_encodeBE h]

/-- **Roundtrip (UInt8 layer)**: encode after decode is the identity. -/
theorem encodeLEU_decodeLEU (bs : List UInt8) :
    encodeLEU bs.length (decodeLEU bs) = bs := by
  have hlen : (uint8ToNats bs).length = bs.length := by simp [uint8ToNats]
  have e := encodeLE_decodeLE (isBytes_uint8ToNats bs)
  simp only [encodeLEU, decodeLEU]
  rw [← hlen, e, natsToUInt8_uint8ToNats]

/-- **Roundtrip (UInt8 layer)**: encode after decode is the identity (big-endian). -/
theorem encodeBEU_decodeBEU (bs : List UInt8) :
    encodeBEU bs.length (decodeBEU bs) = bs := by
  have hlen : (uint8ToNats bs).length = bs.length := by simp [uint8ToNats]
  have e := encodeBE_decodeBE (isBytes_uint8ToNats bs)
  simp only [encodeBEU, decodeBEU]
  rw [← hlen, e, natsToUInt8_uint8ToNats]

/-- Upper bound of decoded values (UInt8 layer, no side condition needed). -/
theorem decodeLEU_lt (bs : List UInt8) : decodeLEU bs < 256 ^ bs.length := by
  have h := decodeLE_lt (isBytes_uint8ToNats bs)
  have hlen : (uint8ToNats bs).length = bs.length := by simp [uint8ToNats]
  simpa [decodeLEU, hlen] using h

theorem decodeBEU_lt (bs : List UInt8) : decodeBEU bs < 256 ^ bs.length := by
  have h := decodeBE_lt (isBytes_uint8ToNats bs)
  have hlen : (uint8ToNats bs).length = bs.length := by simp [uint8ToNats]
  simpa [decodeBEU, hlen] using h

/-! ## Concatenation, splitting and truncation

The `Binary.Core` laws lifted to `List UInt8`.  A caller that wants to encode
or decode in pieces — a wider machine word at a time, say — works from these. -/

/-- Splitting law: the low `a` bytes, then the next `b` bytes of what remains. -/
theorem encodeLEU_add (a b n : Nat) :
    encodeLEU (a + b) n = encodeLEU a n ++ encodeLEU b (n / 256 ^ a) := by
  simp [encodeLEU, natsToUInt8, encodeLE_add]

/-- Splitting law, big-endian: the *more* significant piece comes first. -/
theorem encodeBEU_add (a b n : Nat) :
    encodeBEU (a + b) n = encodeBEU b (n / 256 ^ a) ++ encodeBEU a n := by
  simp [encodeBEU, natsToUInt8, encodeBE_add]

/-- Truncation against any modulus that `256 ^ len` divides. -/
theorem encodeLEU_mod_of_dvd {len m n : Nat} (h : 256 ^ len ∣ m) :
    encodeLEU len (n % m) = encodeLEU len n := by
  simp [encodeLEU, natsToUInt8, encodeLE_mod_of_dvd h]

/-- Truncation against a divisible modulus, big-endian. -/
theorem encodeBEU_mod_of_dvd {len m n : Nat} (h : 256 ^ len ∣ m) :
    encodeBEU len (n % m) = encodeBEU len n := by
  simp [encodeBEU, natsToUInt8, encodeBE_mod_of_dvd h]

/-- One more byte, little-endian: the least significant one comes first. -/
theorem encodeLEU_succ (len n : Nat) :
    encodeLEU (len + 1) n = UInt8.ofNat (n % 256) :: encodeLEU len (n / 256) := by
  simp [encodeLEU, natsToUInt8, encodeLE]

/-- One more byte, big-endian: the least significant one comes last. -/
theorem encodeBEU_succ (len n : Nat) :
    encodeBEU (len + 1) n = encodeBEU len (n / 256) ++ [UInt8.ofNat (n % 256)] := by
  simp [encodeBEU, natsToUInt8, encodeBE_succ]

/-- Concatenation law for big-endian decoding. -/
theorem decodeBEU_append (xs ys : List UInt8) :
    decodeBEU (xs ++ ys) = decodeBEU xs * 256 ^ ys.length + decodeBEU ys := by
  simp only [decodeBEU, uint8ToNats, List.map_append, decodeBE_append, List.length_map]

/-- Concatenation law for little-endian decoding. -/
theorem decodeLEU_append (xs ys : List UInt8) :
    decodeLEU (xs ++ ys) = decodeLEU xs + 256 ^ xs.length * decodeLEU ys := by
  simp only [decodeLEU, uint8ToNats, List.map_append, decodeLE_append, List.length_map]

/-- The leading byte of a big-endian string carries the weight of all the rest. -/
theorem decodeBEU_cons (b : UInt8) (bs : List UInt8) :
    decodeBEU (b :: bs) = b.toNat * 256 ^ bs.length + decodeBEU bs := by
  rw [show (b :: bs) = [b] ++ bs from rfl, decodeBEU_append]
  simp [decodeBEU, uint8ToNats, decodeBE, decodeLE]

/-- Reading big-endian is reading little-endian backwards. -/
theorem decodeBEU_reverse (bs : List UInt8) : decodeBEU bs.reverse = decodeLEU bs := by
  simp only [decodeBEU, decodeLEU, uint8ToNats, decodeBE, List.map_reverse, List.reverse_reverse]

/-- Big-endian decoding as a left fold: folding into `acc` shifts it left by one
    byte per element consumed. -/
theorem decodeBEU_foldl (acc : Nat) (bs : List UInt8) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ bs.length + decodeBEU bs := by
  induction bs generalizing acc with
  | nil => simp [decodeBEU, decodeBE, decodeLE, uint8ToNats]
  | cons b bs ih =>
      rw [List.foldl_cons, ih, decodeBEU_cons, List.length_cons, Nat.pow_add_one, Nat.add_mul,
        Nat.mul_assoc, Nat.mul_comm 256 (256 ^ bs.length), Nat.add_assoc]

/-- Little-endian decoding as a right fold. -/
theorem decodeLEU_foldr (bs : List UInt8) :
    decodeLEU bs = bs.foldr (fun b acc => b.toNat + 256 * acc) 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.foldr_cons, ← ih]; rfl

end Binary
