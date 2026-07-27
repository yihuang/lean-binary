/-!
# Binary.Core

The **core layer** of the fixed-width endianness codec: byte strings are
represented as `List Nat` with the side condition `IsBytes` (every element
`< 256`). Big-endian and little-endian fixed-length encoding/decoding are
defined here, together with proofs of all key properties:

* `decodeLE_encodeLE` / `decodeBE_encodeBE` — decode-after-encode roundtrip
* `encodeLE_decodeLE` / `encodeBE_decodeBE` — encode-after-decode roundtrip
* `decodeLE_lt` / `decodeBE_lt` — upper bound of decoded values
* `length_encodeLE` / `length_encodeBE` — encodings have exactly `len` bytes
* `isBytes_encodeLE` / `isBytes_encodeBE` — encodings are valid byte strings
* `encodeLE_injective` / `encodeBE_injective` — encoding is injective on range
* `decodeLE_append` / `decodeBE_append` — concatenation laws

This file depends only on the Lean 4 core library — **no mathlib required**.
-/

namespace Binary

/-- A list of naturals is a valid byte string when every element is `< 256`. -/
def IsBytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

/-- Little-endian encoding of `n` into exactly `len` bytes, least significant
    byte first. Bits that do not fit are truncated (i.e. this encodes
    `n mod 256 ^ len`). -/
def encodeLE : Nat → Nat → List Nat
  | 0,     _ => []
  | len+1, n => (n % 256) :: encodeLE len (n / 256)

/-- Big-endian encoding of `n` into exactly `len` bytes, most significant
    byte first. -/
def encodeBE (len n : Nat) : List Nat := (encodeLE len n).reverse

/-- Little-endian decoding; the first byte is the least significant one. -/
def decodeLE : List Nat → Nat
  | []      => 0
  | b :: bs => b + 256 * decodeLE bs

/-- Big-endian decoding; the first byte is the most significant one. -/
def decodeBE (bs : List Nat) : Nat := decodeLE bs.reverse

/-! ## Length properties -/

@[simp] theorem length_encodeLE (len n : Nat) : (encodeLE len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [encodeLE, ih]

@[simp] theorem length_encodeBE (len n : Nat) : (encodeBE len n).length = len := by
  simp [encodeBE]

/-! ## Validity of encodings -/

theorem isBytes_encodeLE (len n : Nat) : IsBytes (encodeLE len n) := by
  induction len generalizing n with
  | zero => intro b h; simp [encodeLE] at h
  | succ len ih =>
      intro b hb
      simp only [encodeLE, List.mem_cons] at hb
      cases hb with
      | inl h => omega
      | inr h => exact ih _ b h

theorem isBytes_encodeBE {len n : Nat} : IsBytes (encodeBE len n) := by
  intro b hb
  simp only [encodeBE, List.mem_reverse] at hb
  exact isBytes_encodeLE len n b hb

/-! ## Upper bound of decoded values -/

/-- The value of a valid byte string is strictly below `256 ^ length`. -/
theorem decodeLE_lt {bs : List Nat} (h : IsBytes bs) : decodeLE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp only [decodeLE, List.length_nil, Nat.pow_zero]; omega
  | cons b bs ih =>
      have hb : b < 256 := h b (by simp)
      have hbs : IsBytes bs := fun x hx => h x (List.mem_cons_of_mem b hx)
      have ih' := ih hbs
      simp only [decodeLE, List.length_cons, Nat.pow_add_one]
      omega

theorem decodeBE_lt {bs : List Nat} (h : IsBytes bs) : decodeBE bs < 256 ^ bs.length := by
  have hb : IsBytes bs.reverse := fun x hx => h x (List.mem_reverse.mp hx)
  have := decodeLE_lt hb
  simpa [decodeBE] using this

/-! ## Roundtrip: decode after encode -/

/-- Core roundtrip: for `n < 256 ^ len`, `decodeLE (encodeLE len n) = n`. -/
theorem decodeLE_encodeLE {len n : Nat} (h : n < 256 ^ len) : decodeLE (encodeLE len n) = n := by
  induction len generalizing n with
  | zero =>
      simp only [Nat.pow_zero] at h
      have hn : n = 0 := by omega
      simp [hn, encodeLE, decodeLE]
  | succ len ih =>
      have hlt : n / 256 < 256 ^ len := by
        rw [Nat.pow_add_one] at h
        omega
      simp only [encodeLE, decodeLE, ih hlt]
      omega

/-- Big-endian roundtrip: for `n < 256 ^ len`, `decodeBE (encodeBE len n) = n`. -/
theorem decodeBE_encodeBE {len n : Nat} (h : n < 256 ^ len) : decodeBE (encodeBE len n) = n := by
  simp only [decodeBE, encodeBE, List.reverse_reverse, decodeLE_encodeLE h]

/-! ## Roundtrip: encode after decode -/

/-- For valid byte strings, `encodeLE bs.length (decodeLE bs) = bs`. -/
theorem encodeLE_decodeLE {bs : List Nat} (h : IsBytes bs) :
    encodeLE bs.length (decodeLE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b < 256 := h b (by simp)
      have hbs : IsBytes bs := fun x hx => h x (List.mem_cons_of_mem b hx)
      have hmod : (b + 256 * decodeLE bs) % 256 = b := by omega
      have hdiv : (b + 256 * decodeLE bs) / 256 = decodeLE bs := by omega
      simp only [List.length_cons, decodeLE, encodeLE, hmod, hdiv, ih hbs]

/-- For valid byte strings, `encodeBE bs.length (decodeBE bs) = bs`. -/
theorem encodeBE_decodeBE {bs : List Nat} (h : IsBytes bs) :
    encodeBE bs.length (decodeBE bs) = bs := by
  have hb : IsBytes bs.reverse := fun x hx => h x (List.mem_reverse.mp hx)
  unfold encodeBE decodeBE
  rw [show bs.length = bs.reverse.length from List.length_reverse.symm,
    encodeLE_decodeLE hb, List.reverse_reverse]

/-! ## Injectivity -/

/-- Fixed-length little-endian encoding is injective below `256 ^ len`. -/
theorem encodeLE_injective {len m n : Nat} (hm : m < 256 ^ len) (hn : n < 256 ^ len)
    (h : encodeLE len m = encodeLE len n) : m = n := by
  rw [← decodeLE_encodeLE hm, ← decodeLE_encodeLE hn, h]

/-- Fixed-length big-endian encoding is injective below `256 ^ len`. -/
theorem encodeBE_injective {len m n : Nat} (hm : m < 256 ^ len) (hn : n < 256 ^ len)
    (h : encodeBE len m = encodeBE len n) : m = n := by
  rw [← decodeBE_encodeBE hm, ← decodeBE_encodeBE hn, h]

/-- Little-endian decoding is injective on valid byte strings of equal length. -/
theorem decodeLE_injective {xs ys : List Nat} (hx : IsBytes xs) (hy : IsBytes ys)
    (hlen : xs.length = ys.length) (h : decodeLE xs = decodeLE ys) : xs = ys := by
  have e1 := encodeLE_decodeLE hx
  have e2 := encodeLE_decodeLE hy
  rw [hlen, h] at e1
  rw [e2] at e1
  exact e1.symm

/-- Big-endian decoding is injective on valid byte strings of equal length. -/
theorem decodeBE_injective {xs ys : List Nat} (hx : IsBytes xs) (hy : IsBytes ys)
    (hlen : xs.length = ys.length) (h : decodeBE xs = decodeBE ys) : xs = ys := by
  have e1 := encodeBE_decodeBE hx
  have e2 := encodeBE_decodeBE hy
  rw [hlen, h] at e1
  rw [e2] at e1
  exact e1.symm

/-! ## Concatenation laws and byte-wise characterizations -/

/-- Concatenation law for little-endian decoding. -/
theorem decodeLE_append (xs ys : List Nat) :
    decodeLE (xs ++ ys) = decodeLE xs + 256 ^ xs.length * decodeLE ys := by
  induction xs with
  | nil => simp [decodeLE]
  | cons x xs ih =>
      simp only [List.cons_append, List.length_cons, decodeLE, ih, Nat.pow_add_one]
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length),
        Nat.add_assoc]

/-- Concatenation law for big-endian decoding. -/
theorem decodeBE_append (xs ys : List Nat) :
    decodeBE (xs ++ ys) = decodeBE xs * 256 ^ ys.length + decodeBE ys := by
  simp only [decodeBE, List.reverse_append, List.length_reverse, decodeLE_append]
  ac_rfl

/-- Recursive characterization of big-endian encoding: the most significant
    part comes first, the last byte is `n % 256`. -/
theorem encodeBE_succ (len n : Nat) :
    encodeBE (len + 1) n = encodeBE len (n / 256) ++ [n % 256] := by
  simp [encodeBE, encodeLE]

/-- Big-endian decoding of a byte appended at the end:
    `decodeBE (bs ++ [b]) = decodeBE bs * 256 + b`. -/
theorem decodeBE_snoc (bs : List Nat) (b : Nat) :
    decodeBE (bs ++ [b]) = decodeBE bs * 256 + b := by
  simp only [decodeBE, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append, decodeLE]
  omega

/-! ## Splitting and truncating a fixed-width encoding

Together these say when a `len`-byte encoding may be computed in pieces, and
how much of `n` each piece is allowed to see. -/

/-- **Splitting law**: the low `a` bytes, then the next `b` bytes of what
    remains. -/
theorem encodeLE_add (a b n : Nat) :
    encodeLE (a + b) n = encodeLE a n ++ encodeLE b (n / 256 ^ a) := by
  induction a generalizing n with
  | zero => simp [encodeLE]
  | succ a ih =>
      have hdiv : n / 256 / 256 ^ a = n / 256 ^ (a + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_add_one, Nat.mul_comm]
      rw [show a + 1 + b = (a + b) + 1 by omega, encodeLE, ih, encodeLE, hdiv]
      rfl

/-- Splitting law, big-endian: the *more* significant piece comes first. -/
theorem encodeBE_add (a b n : Nat) :
    encodeBE (a + b) n = encodeBE b (n / 256 ^ a) ++ encodeBE a n := by
  simp [encodeBE, encodeLE_add]

/-- **Truncation law**: a `len`-byte encoding only sees `n` modulo `256 ^ len`
    — the truncation the encoding semantics promise, stated as an equation. -/
theorem encodeLE_mod (len n : Nat) : encodeLE len (n % 256 ^ len) = encodeLE len n := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
      have hpow : (256 : Nat) ^ (len + 1) = 256 * 256 ^ len := by
        rw [Nat.pow_add_one, Nat.mul_comm]
      have hmod : n % 256 ^ (len + 1) % 256 = n % 256 := by
        rw [hpow]; exact Nat.mod_mod_of_dvd n ⟨256 ^ len, rfl⟩
      have hdiv : n % 256 ^ (len + 1) / 256 = n / 256 % 256 ^ len := by
        rw [hpow]; exact Nat.mod_mul_right_div_self n 256 (256 ^ len)
      rw [encodeLE, encodeLE, hmod, hdiv, ih]

/-- Truncation against any modulus that `256 ^ len` divides — the form a caller
    needs when `n` reaches it through a wider fixed-width window. -/
theorem encodeLE_mod_of_dvd {len m n : Nat} (h : 256 ^ len ∣ m) :
    encodeLE len (n % m) = encodeLE len n := by
  rw [← encodeLE_mod len (n % m), Nat.mod_mod_of_dvd n h, encodeLE_mod]

/-- Truncation against a divisible modulus, big-endian. -/
theorem encodeBE_mod_of_dvd {len m n : Nat} (h : 256 ^ len ∣ m) :
    encodeBE len (n % m) = encodeBE len n := by
  simp [encodeBE, encodeLE_mod_of_dvd h]

end Binary
