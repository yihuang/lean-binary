/*
Native implementations of the two byte-codec entry points in `Binary.Fast`.

The Lean definitions stay exactly as they are and remain the reference
semantics every theorem is stated over; `@[extern]` only redirects code
generation, the way `ByteArray.push` already is. What these buy is the
bignum: the Lean bodies walk a `Nat` eight bytes at a time, and every
`n >>> 64` on the way out and every `acc <<< 64` on the way back in
allocates a fresh GMP integer. Here the whole 32-byte word is one
`mpz_export` / `mpz_import`.

`lean_gmp.h` declares its two functions under `LEAN_USE_GMP`, which the
shipped `config.h` does not define even though the runtime is built with GMP
(`lean_alloc_mpz` and `lean_extract_mpz_value` are both in `libleanrt.a`).
Defining it here is what makes the declarations visible. If a toolchain ever
ships without GMP this fails at link time, loudly, which is the failure mode
to want.

Semantics being matched, from `Binary.Core`:

  encodeLE len n  -- exactly `len` bytes, truncating: encodes `n % 256 ^ len`
  encodeBE len n  = (encodeLE len n).reverse

  decodeBEBytesFromFast ba off len
                  = big-endian value of ba[off ..< min (off+len) ba.size],
                    and 0 when that range is empty.
*/
#define LEAN_USE_GMP
#include <lean/lean_gmp.h>
#include <string.h>

/* A `Nat` that Lean will accept: values up to `LEAN_MAX_SMALL_NAT` must be
   boxed scalars, never mpz objects, or comparisons against scalars break.
   `lean_uint64_to_nat` makes that choice the same way Lean does. */
static inline lean_object *binary_mpz_to_nat(mpz_t m) {
  if (mpz_fits_ulong_p(m))
    return lean_uint64_to_nat((uint64_t)mpz_get_ui(m));
  return lean_alloc_mpz(m);
}

/** `Binary.encodeBEBytesFast len n` */
LEAN_EXPORT lean_object *lean_binary_encode_be_bytes(b_lean_obj_arg len_o,
                                                     b_lean_obj_arg n_o) {
  /* A non-scalar length is astronomically larger than any allocation. */
  if (!lean_is_scalar(len_o))
    lean_internal_panic_out_of_memory();
  size_t len = lean_unbox(len_o);

  lean_object *res = lean_alloc_sarray(1, len, len);
  uint8_t *dst = lean_sarray_cptr(res);
  memset(dst, 0, len);
  if (len == 0)
    return res;

  if (lean_is_scalar(n_o)) {
    size_t v = lean_unbox(n_o);
    for (size_t i = 0; i < len && v != 0; i++) {
      dst[len - 1 - i] = (uint8_t)(v & 0xff);
      v >>= 8;
    }
    return res;
  }

  mpz_t v;
  mpz_init(v);
  lean_extract_mpz_value(n_o, v);

  /* `mpz_export` writes the value's own byte width, right-aligned in `dst`;
     anything wider than `len` has to be truncated first, which is what the
     specification's `% 256 ^ len` does. */
  size_t nbytes = (mpz_sizeinbase(v, 2) + 7) / 8;
  if (nbytes > len) {
    mpz_fdiv_r_2exp(v, v, (mp_bitcnt_t)len * 8);
    nbytes = (mpz_sizeinbase(v, 2) + 7) / 8;
  }
  if (mpz_sgn(v) != 0) {
    size_t written = 0;
    mpz_export(dst + (len - nbytes), &written, 1, 1, 1, 0, v);
  }
  mpz_clear(v);
  return res;
}

/** `Binary.decodeBEBytesFromFast ba off len` */
LEAN_EXPORT lean_object *lean_binary_decode_be_from(b_lean_obj_arg ba,
                                                    b_lean_obj_arg off_o,
                                                    b_lean_obj_arg len_o) {
  size_t size = lean_sarray_size(ba);

  /* A non-scalar offset is past the end of any buffer, so the window is
     empty; a non-scalar length cannot shorten one, so it clamps to the end. */
  if (!lean_is_scalar(off_o))
    return lean_box(0);
  size_t off = lean_unbox(off_o);
  if (off >= size)
    return lean_box(0);

  size_t avail = size - off;
  size_t n = avail;
  if (lean_is_scalar(len_o)) {
    size_t len = lean_unbox(len_o);
    if (len < avail)
      n = len;
  }
  if (n == 0)
    return lean_box(0);

  const uint8_t *src = lean_sarray_cptr((lean_object *)ba) + off;

  /* Leading zeros carry no value, and skipping them is what keeps the common
     case off GMP entirely: an ABI buffer is mostly lengths, offsets, array
     counts and bools, all of which fit a machine word inside a 32-byte
     window.  Paying `mpz_init`/`mpz_import`/`mpz_clear` for those measured
     slower than the Lean body it replaces. */
  while (n > 0 && *src == 0) {
    src++;
    n--;
  }
  if (n == 0)
    return lean_box(0);

  /* Up to eight significant bytes is a machine word — no GMP at all. */
  if (n <= 8) {
    uint64_t acc = 0;
    for (size_t i = 0; i < n; i++)
      acc = (acc << 8) | (uint64_t)src[i];
    return lean_uint64_to_nat(acc);
  }

  mpz_t m;
  mpz_init(m);
  mpz_import(m, n, 1, 1, 1, 0, src);
  lean_object *r = binary_mpz_to_nat(m);
  mpz_clear(m);
  return r;
}
