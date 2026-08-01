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

/-- Little-endian encoding to a `UInt8` list, least significant byte first.

Direct single-pass construction: the old implementation went through a
`List Nat` intermediate (`encodeLE`, then `natsToUInt8`), allocating
three lists per word; this builds the `UInt8` list in one pass (plus one
`reverse` for the big-endian form). -/
def encodeLEU : Nat → Nat → List UInt8
  | 0, _ => []
  | len + 1, n => UInt8.ofNat (n % 256) :: encodeLEU len (n / 256)

/-- Big-endian encoding to a `UInt8` list, most significant byte first. -/
def encodeBEU (len n : Nat) : List UInt8 := (encodeLEU len n).reverse

/-- Little-endian decoding of a `UInt8` list (first byte least
significant).  A single `foldr`, no intermediate representation. -/
def decodeLEU (bs : List UInt8) : Nat :=
  bs.foldr (fun x acc => x.toNat + 256 * acc) 0

/-- Big-endian decoding of a `UInt8` list (first byte most significant).
A single tail-recursive `foldl`, no intermediate representation. -/
def decodeBEU (bs : List UInt8) : Nat :=
  bs.foldl (fun acc x => acc * 256 + x.toNat) 0

@[simp] theorem length_encodeLEU (len n : Nat) : (encodeLEU len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [encodeLEU, ih]

@[simp] theorem length_encodeBEU (len n : Nat) : (encodeBEU len n).length = len := by
  simp [encodeBEU]

/- The two fold forms below are the workhorses of the big-endian
decoder: a left fold with `acc * 256 + b` and a right fold with
`b + 256 * acc` both accumulate `256 ^ n`-weighted sums, and the
following identities isolate the leading term.  They are what lets
`decodeBEU` run as a single allocation-free `foldl` instead of
reverse-then-fold. -/

private theorem foldl_mul_pow (bs : List UInt8) (a : Nat) :
    bs.foldl (fun acc x => acc * 256 + x.toNat) a =
      a * 256 ^ bs.length + bs.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  induction bs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, List.length_cons, Nat.pow_succ]
      rw [ih (a * 256 + x.toNat), ih x.toNat]
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length)]
      ac_rfl

private theorem foldr_mul_pow (bs : List UInt8) (a : Nat) :
    bs.foldr (fun x acc => x.toNat + 256 * acc) a =
      a * 256 ^ bs.length + bs.foldr (fun x acc => x.toNat + 256 * acc) 0 := by
  induction bs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldr_cons, List.length_cons, Nat.pow_succ]
      rw [ih a]
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 a, Nat.mul_assoc,
        Nat.mul_comm 256 (256 ^ xs.length)]
      ac_rfl

/-- Big-endian decoding equals little-endian decoding of the reversed
list — the identity behind the single-pass `decodeBEU`. -/
theorem decodeBEU_eq_decodeLEU_reverse (bs : List UInt8) :
    decodeBEU bs = decodeLEU bs.reverse := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
      unfold decodeBEU decodeLEU
      simp only [List.foldl_cons, List.reverse_cons, List.foldr_append, List.foldr_cons,
        List.foldr_nil, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero]
      rw [foldl_mul_pow xs x.toNat, foldr_mul_pow xs.reverse x.toNat]
      rw [List.length_reverse]
      exact congrArg (fun t => x.toNat * 256 ^ xs.length + t)
        (by simpa [decodeBEU, decodeLEU] using ih)

/-- **Roundtrip (UInt8 layer)**: decode after encode is the identity
    for `n < 256 ^ len`. -/
theorem decodeLEU_encodeLEU {len n : Nat} (h : n < 256 ^ len) :
    decodeLEU (encodeLEU len n) = n := by
  induction len generalizing n with
  | zero =>
      have hn : n = 0 := by
        have h' : n < 1 := by simpa using h
        omega
      simp [encodeLEU, decodeLEU, hn]
  | succ len ih =>
      have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
        rw [UInt8.toNat_ofNat']
        exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide : 0 < 256))
      have hdiv : n / 256 < 256 ^ len := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
        simpa [Nat.pow_succ] using h
      simp only [encodeLEU]
      change (UInt8.ofNat (n % 256)).toNat + 256 * decodeLEU (encodeLEU len (n / 256)) = n
      rw [hmod, ih hdiv, Nat.mod_add_div]

/-- **Roundtrip (UInt8 layer)**: decode after encode is the identity
    for `n < 256 ^ len` (big-endian). -/
theorem decodeBEU_encodeBEU {len n : Nat} (h : n < 256 ^ len) :
    decodeBEU (encodeBEU len n) = n := by
  unfold encodeBEU
  rw [decodeBEU_eq_decodeLEU_reverse, List.reverse_reverse]
  exact decodeLEU_encodeLEU h

/-- **Roundtrip (UInt8 layer)**: encode after decode is the identity. -/
theorem encodeLEU_decodeLEU (bs : List UInt8) :
    encodeLEU bs.length (decodeLEU bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
      have hmod : (x.toNat + 256 * decodeLEU xs) % 256 = x.toNat := by
        rw [Nat.mul_comm 256 (decodeLEU xs)]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.toNat_lt]
      have hdiv : (x.toNat + 256 * decodeLEU xs) / 256 = decodeLEU xs := by
        rw [Nat.add_comm]
        rw [Nat.mul_add_div (by decide : 0 < 256)]
        rw [Nat.div_eq_of_lt x.toNat_lt, Nat.add_zero]
      simp only [encodeLEU, List.length_cons]
      change UInt8.ofNat ((x.toNat + 256 * decodeLEU xs) % 256) ::
          encodeLEU xs.length ((x.toNat + 256 * decodeLEU xs) / 256) = x :: xs
      rw [hmod, hdiv, ih]
      simp

/-- **Roundtrip (UInt8 layer)**: encode after decode is the identity (big-endian). -/
theorem encodeBEU_decodeBEU (bs : List UInt8) :
    encodeBEU bs.length (decodeBEU bs) = bs := by
  unfold encodeBEU
  rw [decodeBEU_eq_decodeLEU_reverse]
  have h := encodeLEU_decodeLEU bs.reverse
  rw [← List.length_reverse]
  rw [h]
  rw [List.reverse_reverse]

/-- Upper bound of decoded values (UInt8 layer, no side condition needed). -/
theorem decodeLEU_lt (bs : List UInt8) : decodeLEU bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [decodeLEU]
  | cons x xs ih =>
      simp only [decodeLEU, List.foldr_cons, List.length_cons] at ih ⊢
      have hx : x.toNat < 256 := x.toNat_lt
      have hd1 : xs.foldr (fun x acc => x.toNat + 256 * acc) 0 + 1 ≤ 256 ^ xs.length :=
        Nat.succ_le_of_lt ih
      have hle : 256 * (xs.foldr (fun x acc => x.toNat + 256 * acc) 0 + 1) ≤
          256 ^ xs.length * 256 := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left 256 hd1
      have hlt : x.toNat + 256 * xs.foldr (fun x acc => x.toNat + 256 * acc) 0 <
          256 * (xs.foldr (fun x acc => x.toNat + 256 * acc) 0 + 1) := by omega
      have hgoal : x.toNat + 256 * xs.foldr (fun x acc => x.toNat + 256 * acc) 0 <
          256 ^ xs.length * 256 := Nat.lt_of_lt_of_le hlt hle
      simpa [Nat.pow_succ, Nat.mul_comm] using hgoal

theorem decodeBEU_lt (bs : List UInt8) : decodeBEU bs < 256 ^ bs.length := by
  rw [decodeBEU_eq_decodeLEU_reverse]
  have h := decodeLEU_lt bs.reverse
  simpa [List.length_reverse] using h

end Binary
