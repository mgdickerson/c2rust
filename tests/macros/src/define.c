//! translate_const_macros

#include <stddef.h>
#include <stdint.h>
typedef  uint64_t U64;
typedef  uint32_t U32;

#define TEST_CONST1 1
#define TEST_NESTED 2
#define TEST_CONST2 TEST_NESTED
#define TEST_PARENS (TEST_CONST2 + 1) * 3

int reference_define() {
  int x = TEST_CONST1;
  x += TEST_CONST2;
  if (3 < TEST_PARENS)
    x += TEST_PARENS;
  return x;
}

// Exercise an edge case where a struct initializer needs to be in an unsafe
// block
struct fn_ptrs {
  void *v;
  int (*fn1)(void);
  int (*fn2)(int);
};

typedef int (*fn_ptr_ty)(char);

struct fn_ptrs const fns = {NULL, NULL, NULL};


// Make sure we can't refer to globals in a const macro
#define GLOBAL_REF &fns
struct fn_ptrs* p = GLOBAL_REF;

#define ZSTD_STATIC_ASSERT(c) (void)sizeof(char[(c) ? 1 : -1])
#define ZSTD_WINDOWLOG_MAX_32    30
#define ZSTD_WINDOWLOG_MAX_64    31
#define ZSTD_WINDOWLOG_MAX     ((int)(sizeof(size_t) == 4 ? ZSTD_WINDOWLOG_MAX_32 : ZSTD_WINDOWLOG_MAX_64))
U64 test_zstd() {
  // This static assert was causing us trouble by somehow giving a valid
  // expression for ZSTD_WINDOWLOG_MAX which shouldn't be possible to translate
  // to a const.
  ZSTD_STATIC_ASSERT(ZSTD_WINDOWLOG_MAX <= 31);
  return ZSTD_WINDOWLOG_MAX;
}
