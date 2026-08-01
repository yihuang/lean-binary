import Binary.UInt8

/-!
# Binary.ByteArray

The `ByteArray` layer: codec interface over the runtime byte-string type
used for actual I/O. Roundtrip properties are lifted directly from the
`Binary.UInt8` layer.

Conventions: encoding goes through `List.toByteArray`, decoding reads
`ByteArray.data.toList`.
-/

namespace Binary

/-- Two `ByteArray`s with equal underlying data are equal. -/
theorem ByteArray.data_inj {x y : ByteArray} (h : x.data = y.data) : x = y := by
  cases x; cases y; simp_all

/-- `ba.size` equals the length of the underlying byte list. -/
theorem ByteArray.size_eq_toList_length (ba : ByteArray) :
    ba.size = ba.data.toList.length := by
  cases ba
  exact Array.length_toList.symm

/-- Little-endian encoding to a `ByteArray`, least significant byte first. -/
def encodeLEBytes (len n : Nat) : ByteArray := (encodeLEU len n).toByteArray

/-- Big-endian encoding to a `ByteArray`, most significant byte first. -/
def encodeBEBytes (len n : Nat) : ByteArray := (encodeBEU len n).toByteArray

/-- Little-endian decoding of a `ByteArray`. -/
def decodeLEBytes (ba : ByteArray) : Nat := decodeLEU ba.data.toList

/-- Big-endian decoding of a `ByteArray`. -/
def decodeBEBytes (ba : ByteArray) : Nat := decodeBEU ba.data.toList

@[simp] theorem size_encodeLEBytes (len n : Nat) : (encodeLEBytes len n).size = len := by
  rw [ByteArray.size_eq_toList_length]
  simp [encodeLEBytes, List.data_toByteArray]

@[simp] theorem size_encodeBEBytes (len n : Nat) : (encodeBEBytes len n).size = len := by
  rw [ByteArray.size_eq_toList_length]
  simp [encodeBEBytes, List.data_toByteArray]

/-- **Roundtrip (ByteArray layer)**: decode after encode is the identity
    for `n < 256 ^ len`. -/
theorem decodeLEBytes_encodeLEBytes {len n : Nat} (h : n < 256 ^ len) :
    decodeLEBytes (encodeLEBytes len n) = n := by
  simp only [decodeLEBytes, encodeLEBytes, List.data_toByteArray, List.toList_toArray,
    decodeLEU_encodeLEU h]

/-- **Roundtrip (ByteArray layer)**: decode after encode is the identity
    for `n < 256 ^ len` (big-endian). -/
theorem decodeBEBytes_encodeBEBytes {len n : Nat} (h : n < 256 ^ len) :
    decodeBEBytes (encodeBEBytes len n) = n := by
  simp only [decodeBEBytes, encodeBEBytes, List.data_toByteArray, List.toList_toArray,
    decodeBEU_encodeBEU h]

/-- **Roundtrip (ByteArray layer)**: encode after decode is the identity. -/
theorem encodeLEBytes_decodeLEBytes (ba : ByteArray) :
    encodeLEBytes ba.data.toList.length (decodeLEBytes ba) = ba := by
  apply ByteArray.data_inj
  show ((encodeLEU ba.data.toList.length (decodeLEU ba.data.toList)).toByteArray).data = ba.data
  rw [List.data_toByteArray, encodeLEU_decodeLEU, Array.toArray_toList]

/-- **Roundtrip (ByteArray layer)**: encode after decode is the identity (big-endian). -/
theorem encodeBEBytes_decodeBEBytes (ba : ByteArray) :
    encodeBEBytes ba.data.toList.length (decodeBEBytes ba) = ba := by
  apply ByteArray.data_inj
  show ((encodeBEU ba.data.toList.length (decodeBEU ba.data.toList)).toByteArray).data = ba.data
  rw [List.data_toByteArray, encodeBEU_decodeBEU, Array.toArray_toList]

/-- Encode-after-decode roundtrip stated via `ba.size` (more convenient). -/
theorem encodeLEBytes_decodeLEBytes_size (ba : ByteArray) :
    encodeLEBytes ba.size (decodeLEBytes ba) = ba := by
  rw [ByteArray.size_eq_toList_length]
  exact encodeLEBytes_decodeLEBytes ba

/-- Encode-after-decode roundtrip stated via `ba.size` (big-endian). -/
theorem encodeBEBytes_decodeBEBytes_size (ba : ByteArray) :
    encodeBEBytes ba.size (decodeBEBytes ba) = ba := by
  rw [ByteArray.size_eq_toList_length]
  exact encodeBEBytes_decodeBEBytes ba

/-! ## Windowed reads

Decoding a field out of a larger buffer — a word at an offset in EVM call
data, say — wants the value of `len` bytes starting at `off` without
slicing anything.  The specification is stated with `drop`/`take` so it
composes with the list theory above; `Binary.Fast` supplies an
implementation that reads the buffer by index and never builds a list. -/

/-- The big-endian value of the `len` bytes at offset `off`.  Reads short
if the window runs past the end, exactly as `take` does. -/
def decodeBEBytesFrom (ba : ByteArray) (off len : Nat) : Nat :=
  decodeBEU ((ba.data.toList.drop off).take len)

/-- The little-endian value of the `len` bytes at offset `off`. -/
def decodeLEBytesFrom (ba : ByteArray) (off len : Nat) : Nat :=
  decodeLEU ((ba.data.toList.drop off).take len)

/-- A whole-buffer read is the window starting at `0`. -/
theorem decodeBEBytesFrom_zero (ba : ByteArray) :
    decodeBEBytesFrom ba 0 ba.size = decodeBEBytes ba := by
  rw [decodeBEBytesFrom, decodeBEBytes, List.drop_zero, ByteArray.size_eq_toList_length,
    List.take_length]

theorem decodeLEBytesFrom_zero (ba : ByteArray) :
    decodeLEBytesFrom ba 0 ba.size = decodeLEBytes ba := by
  rw [decodeLEBytesFrom, decodeLEBytes, List.drop_zero, ByteArray.size_eq_toList_length,
    List.take_length]

end Binary
