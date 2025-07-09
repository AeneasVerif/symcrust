#include "symcrust_mlkem.h"

bool
symcrust_key__core__cmp__PartialEq_symcrust__key__Params__for_symcrust__key__Params__ne(
  symcrust_key_Params *x0,
  symcrust_key_Params *x1
) {
  return *x0 != *x1;
}

void symcrust_ntt_slice_to_sub_array_(size_t N, Eurydice_slice src, size_t i, uint8_t *dst) {
  if (i + N >= src.len) {
    fprintf(stderr, "slice_to_sub_array_: invalid indices");
    exit(255);
  }
  memcpy(dst, src.ptr + i, N);
}
