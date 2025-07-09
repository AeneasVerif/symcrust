/* This file is hand-written and implements the "extern" stubs found in
 * c/internal/symcrust_common.h. It includes c/internal/symcrust_common.h to make
 * sure the declarations are consistent with the expected signatures.  */

#include <stdlib.h>
#include <symcrypt.h>

#include "internal/symcrust_common.h"

// FIXME: put these in a separate Rust module, then no-prefix for that module, and then reconcile
// everything at link time without having to write little adapters like this.
void symcrust_common_SymCryptModuleInit(uint32_t api, uint32_t minor) {
  SymCryptModuleInit(api, minor);
}

void symcrust_common_SymCryptRandom(uint8_t *pbRandom, size_t cbRandom) {
  SymCryptRandom(pbRandom, cbRandom);
}

void symcrust_common_SymCryptWipe(uint8_t *pbData, size_t cbData) {
  SymCryptWipe((void*)pbData, cbData);
}

bool symcrust_common__core__cmp__PartialEq_symcrust__common__Error__for_symcrust__common__Error__ne(
    symcrust_common_Error *e1, symcrust_common_Error *e2) {
  return *e1 != *e2;
}

core_result_Result_10
core_fmt__core__fmt__Formatter__a___write_str(core_fmt_Formatter *x0, Eurydice_str x1) {
  fprintf(stderr, "TODO: formatter\n");
  exit(255);
}
