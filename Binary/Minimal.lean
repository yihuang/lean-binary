import Binary.Fast

/-!
# Binary.Minimal

Minimal-length big-endian encoding: the shortest byte string that decodes back
to `n`, as opposed to the fixed-width codecs of `Binary.Core`.

This is the convention used for EVM/ABI integer encoding, where `0` is
represented by a single zero byte rather than the empty string.

* `minBytes n` — the width, `Nat.log2 n / 8 + 1` (and `1` at `n = 0`)
* `encodeBEMin` / `encodeBEMinU` / `encodeBEMinBytes` — the three layers
* `minBytes_spec` — minimality: `minBytes n` is the LEAST positive width
  that fits `n`
* `decodeBE_encodeBEMin` and friends — roundtrips at each layer

Everything is built on the fixed-width codecs at width `minBytes n`, so the
fixed-width theory applies verbatim. Core library only — no mathlib.
-/

namespace Binary

/-! ## The minimal width -/

/-- Bytes needed for the minimal big-endian encoding of `n`.

    `0` takes one byte, matching the EVM convention that the zero word encodes
    as a single `0x00` rather than the empty byte string.  (The zero case is
    spelled out for the reader; `Nat.log2 0 / 8 + 1` is `1` anyway.) -/
def minBytes : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1).log2 / 8 + 1

theorem minBytes_pos (n : Nat) : 0 < minBytes n := by
  cases n with
  | zero => decide
  | succ k => simp [minBytes]

/-- Powers of 256 are powers of two, eight bits at a time — the one arithmetic
    fact every width bound below runs through. -/
theorem pow_256_eq (j : Nat) : (256 : Nat) ^ j = 2 ^ (j * 8) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, Nat.mul_comm]

/-- `n` fits in `minBytes n` bytes — the defining upper bound. -/
theorem lt_pow_minBytes (n : Nat) : n < 256 ^ minBytes n := by
  cases n with
  | zero => decide
  | succ k =>
    have hne : k + 1 ≠ 0 := by omega
    have hlt2 : k + 1 < 2 ^ ((k + 1).log2 + 1) := (Nat.log2_lt hne).mp (by omega)
    have hmono : (2 : Nat) ^ ((k + 1).log2 + 1) ≤ 2 ^ (((k + 1).log2 / 8 + 1) * 8) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    show k + 1 < 256 ^ ((k + 1).log2 / 8 + 1)
    rw [pow_256_eq]; omega

/-- `minBytes n` is at most any positive width that fits `n`. -/
theorem minBytes_le_of_lt {n len : Nat} (h : n < 256 ^ len) (hlen : 0 < len) :
    minBytes n ≤ len := by
  cases n with
  | zero => show 1 ≤ len; omega
  | succ k =>
    have hne : k + 1 ≠ 0 := by omega
    have h2 : k + 1 < 2 ^ (len * 8) := by rwa [pow_256_eq] at h
    have hlog : (k + 1).log2 < len * 8 := (Nat.log2_lt hne).mpr h2
    have : (k + 1).log2 / 8 < len := Nat.div_lt_of_lt_mul (by omega)
    show (k + 1).log2 / 8 + 1 ≤ len
    omega

/-- **Minimality**: `minBytes n` is the LEAST positive width that fits `n`.

    Together with `lt_pow_minBytes` (the width works) this pins `minBytes`
    down completely: it is exactly the least `len > 0` with `n < 256 ^ len`. -/
theorem minBytes_spec {n len : Nat} (hlen : 0 < len) : n < 256 ^ len ↔ minBytes n ≤ len := by
  constructor
  · intro h; exact minBytes_le_of_lt h hlen
  · intro h
    exact Nat.lt_of_lt_of_le (lt_pow_minBytes n) (Nat.pow_le_pow_right (by omega) h)

/-- A width that does *not* fit `n` is below `minBytes n` — the contrapositive of
    `minBytes_le_of_lt`, and the lower-bound half of every exact-width lemma below. -/
theorem lt_minBytes_of_le {n len : Nat} (h : 256 ^ len ≤ n) : len < minBytes n := by
  rcases Nat.lt_or_ge len (minBytes n) with hlt | hge
  · exact hlt
  · exact absurd (lt_pow_minBytes n)
      (Nat.not_lt.mpr (Nat.le_trans (Nat.pow_le_pow_right (by omega) hge) h))

/-- For `n ≠ 0`, the weight of the top byte's position is at most `n` — the
    lower-bound face of minimality, and the bound the no-leading-zero fact
    below rests on. -/
theorem pow_minBytes_pred_le {n : Nat} (h : n ≠ 0) : 256 ^ (minBytes n - 1) ≤ n := by
  rcases Nat.lt_or_ge n (256 ^ (minBytes n - 1)) with hlt | hge
  · exfalso
    have hpos := minBytes_pos n
    rcases Nat.lt_or_ge (minBytes n) 2 with h1 | h2
    · have h0 : minBytes n - 1 = 0 := by omega
      rw [h0, Nat.pow_zero] at hlt
      omega
    · have := minBytes_le_of_lt hlt (by omega)
      omega
  · exact hge

/-- The exact width of `n` from a two-sided BYTE-length bound — the natural
    characterisation: `n` takes `k` bytes exactly when `256^(k-1) <= n < 256^k`.

    Prefer this to `minBytes_eq_of_range`, whose bit-length lower bound `2^(8k-1) <= n`
    only covers values whose top byte has its high bit set (it cannot, for instance,
    show `minBytes 256 = 2`). -/
theorem minBytes_eq_of_byte_range {n k : Nat} (hk : 0 < k)
    (hlo : 256 ^ (k - 1) ≤ n) (hhi : n < 256 ^ k) : minBytes n = k :=
  Nat.le_antisymm (minBytes_le_of_lt hhi hk) (by have := lt_minBytes_of_le hlo; omega)

/-- The exact width of `n` from a two-sided bit-length bound.  The lower bound is
    the stronger one — `2^(8k-1) ≤ n` forces the top byte's high bit — so this is
    `minBytes_eq_of_byte_range` with the exponents converted. -/
theorem minBytes_eq_of_range {n k : Nat} (hk : 0 < k)
    (hlo : 2 ^ (k * 8 - 1) ≤ n) (hhi : n < 2 ^ (k * 8)) : minBytes n = k :=
  minBytes_eq_of_byte_range hk
    (by rw [pow_256_eq]; exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hlo)
    (by rw [pow_256_eq]; exact hhi)

/-- `minBytes` obeys the base-256 recursion — derived from the minimality spec above,
    with no `log2` reasoning. This is the shape a caller's own recursive width function
    will have, so it is what lets such a function be identified with `minBytes`. -/
theorem minBytes_div {n : Nat} (h : 256 ≤ n) : minBytes n = minBytes (n / 256) + 1 := by
  have hdpos : 0 < minBytes (n / 256) := minBytes_pos _
  apply Nat.le_antisymm
  · have h1 : n / 256 < 256 ^ minBytes (n / 256) := lt_pow_minBytes _
    have hp : (256 : Nat) ^ (minBytes (n / 256) + 1) = 256 * 256 ^ minBytes (n / 256) := by
      rw [Nat.pow_succ]; omega
    have hgoal : n < 256 ^ (minBytes (n / 256) + 1) := by omega
    exact minBytes_le_of_lt hgoal (by omega)
  · have hlt : n < 256 ^ minBytes n := lt_pow_minBytes n
    have hpos := minBytes_pos n
    have hk : 2 ≤ minBytes n := by
      rcases Nat.lt_or_ge (minBytes n) 2 with hc | hc
      · exfalso
        have h1 : minBytes n = 1 := by omega
        rw [h1, Nat.pow_one] at hlt
        omega
      · exact hc
    obtain ⟨j, hj⟩ : ∃ j, minBytes n = j + 1 := ⟨minBytes n - 1, by omega⟩
    rw [hj] at hlt
    have hp : (256 : Nat) ^ (j + 1) = 256 * 256 ^ j := by rw [Nat.pow_succ]; omega
    have hdiv : n / 256 < 256 ^ j := by omega
    have hle := minBytes_le_of_lt hdiv (by omega)
    omega

/-- Below 256, one byte suffices — the recursion's base case. -/
theorem minBytes_eq_one {n : Nat} (h : n < 256) : minBytes n = 1 :=
  Nat.le_antisymm (minBytes_le_of_lt (by rwa [Nat.pow_one]) Nat.one_pos) (minBytes_pos n)

/-! ## The codecs -/

/-- Minimal-length big-endian encoding over `List Nat`. -/
def encodeBEMin (n : Nat) : List Nat := encodeBE (minBytes n) n

/-- Minimal-length big-endian encoding over `List UInt8`. -/
def encodeBEMinU (n : Nat) : List UInt8 := encodeBEU (minBytes n) n

/-- Minimal-length big-endian encoding over `ByteArray`. -/
def encodeBEMinBytes (n : Nat) : ByteArray := encodeBEBytes (minBytes n) n

/-! ## Lengths -/

@[simp] theorem length_encodeBEMin (n : Nat) : (encodeBEMin n).length = minBytes n := by
  simp [encodeBEMin]

@[simp] theorem length_encodeBEMinU (n : Nat) : (encodeBEMinU n).length = minBytes n := by
  simp [encodeBEMinU]

@[simp] theorem size_encodeBEMinBytes (n : Nat) : (encodeBEMinBytes n).size = minBytes n := by
  simp [encodeBEMinBytes]

/-- The minimal encoding is a valid byte string. -/
theorem isBytes_encodeBEMin (n : Nat) : IsBytes (encodeBEMin n) := isBytes_encodeBE

/-! ## Roundtrips -/

/-- **Roundtrip (`List Nat`)**: the minimal encoding decodes back — no side
    condition, unlike the fixed-width codec, since the width is chosen to fit. -/
theorem decodeBE_encodeBEMin (n : Nat) : decodeBE (encodeBEMin n) = n :=
  decodeBE_encodeBE (lt_pow_minBytes n)

/-- **Roundtrip (`List UInt8`)**. -/
theorem decodeBEU_encodeBEMinU (n : Nat) : decodeBEU (encodeBEMinU n) = n :=
  decodeBEU_encodeBEU (lt_pow_minBytes n)

/-- **Roundtrip (`ByteArray`)**. -/
theorem decodeBEBytes_encodeBEMinBytes (n : Nat) : decodeBEBytes (encodeBEMinBytes n) = n :=
  decodeBEBytes_encodeBEBytes (lt_pow_minBytes n)

/-- The minimal encoding is injective. -/
theorem encodeBEMin_injective {m n : Nat} (h : encodeBEMin m = encodeBEMin n) : m = n := by
  have := congrArg decodeBE h
  rwa [decodeBE_encodeBEMin, decodeBE_encodeBEMin] at this

/-! ## Minimality, string-level

The width facts above restated about the byte strings themselves: the minimal
encoding wastes no leading zero byte, and no shorter nonempty string decodes
to the same value. -/

/-- **No leading zero** (`n ≠ 0`): the minimal encoding's first byte is
    nonzero.  The hypothesis is genuinely needed — `0` encodes as `[0x00]`
    by convention. -/
theorem head_encodeBEMin_ne_zero {n : Nat} (h : n ≠ 0) : (encodeBEMin n).head! ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, minBytes n = k + 1 :=
    ⟨minBytes n - 1, by have := minBytes_pos n; omega⟩
  have hlo : 256 ^ k ≤ n := by
    have := pow_minBytes_pred_le h
    rwa [hk, Nat.add_sub_cancel] at this
  have hhi : n < 256 ^ k * 256 := by
    have := lt_pow_minBytes n
    rwa [hk, Nat.pow_succ] at this
  have hq : 0 < n / 256 ^ k := Nat.div_pos hlo (Nat.pow_pos (by omega))
  have hqlt : n / 256 ^ k < 256 := Nat.div_lt_of_lt_mul hhi
  rw [encodeBEMin, hk, encodeBE_cons]
  show n / 256 ^ k % 256 ≠ 0
  omega

/-- **Minimality over byte strings**: no nonempty string that decodes to `n`
    is shorter than `minBytes n`.  With `decodeBE_encodeBEMin` this makes
    `encodeBEMin n` literally the shortest nonempty preimage of `n`. -/
theorem minBytes_le_length {bs : List Nat} (hb : IsBytes bs) (hne : bs ≠ []) :
    minBytes (decodeBE bs) ≤ bs.length := by
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b bs => simp
  exact minBytes_le_of_lt (decodeBE_lt hb) hpos

/-- Minimality over `UInt8` strings — no `IsBytes` needed. -/
theorem minBytes_le_lengthU (bs : List UInt8) (hne : bs ≠ []) :
    minBytes (decodeBEU bs) ≤ bs.length := by
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b bs => simp
  exact minBytes_le_of_lt (decodeBEU_lt bs) hpos

/-- Minimality over `ByteArray`s. -/
theorem minBytes_le_size {ba : ByteArray} (hne : 0 < ba.size) :
    minBytes (decodeBEBytes ba) ≤ ba.size :=
  minBytes_le_of_lt (decodeBEBytes_lt ba) hne

end Binary
