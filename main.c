#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int our_code_starts_here(int *HEAP) asm("our_code_starts_here");
extern void error(int err_code) asm("error");
extern int print(int val) asm("print");
extern int printRaw(int val) asm("print_raw");
extern int printStack(int val, int* esp, int* ebp, int args) asm("print_stack");
extern int equal(int val1, int val2);

const int NUM_TAG_MASK   = 0x00000001;
const int TUPLE_TAG_MASK = 0x00000007;
const int BOOL_TRUE      = 0xFFFFFFFF;
const int BOOL_FALSE     = 0x7FFFFFFF;

const int ERR_COMP_NOT_NUM   =  1;
const int ERR_ARITH_NOT_NUM  =  2;
const int ERR_LOGIC_NOT_BOOL =  3;
const int ERR_IF_NOT_BOOL    =  4;
const int ERR_OVERFLOW       =  5;
const int ERR_GET_NOT_TUPLE  =  6;
const int ERR_GET_LOW_INDEX  =  7;
const int ERR_GET_HIGH_INDEX =  8;
const int ERR_INDEX_NOT_NUM  =  9;
const int ERR_NOT_LAMBDA     = 10;
const int ERR_WRONG_ARITY    = 11;


int printRaw(int val) {
  printf("%#010x ==> %d\n", val, val);
  return val;
}

int equal(int a, int b)
{
    if (a == b)
        return BOOL_TRUE;

    if (((a & TUPLE_TAG_MASK) != 0x1) || ((b & TUPLE_TAG_MASK) != 0x1))
        return BOOL_FALSE;

    const int* tup_a = (int*)(a - 1);
    const int* tup_b = (int*)(b - 1);

    for (size_t i = 0; i <= tup_a[0]; ++i)
        if (equal(tup_a[i], tup_b[i]) == BOOL_FALSE)
            return BOOL_FALSE;

    return BOOL_TRUE;
}

void printHelp(FILE *out, int val) {
  if((val & NUM_TAG_MASK) == 0) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & TUPLE_TAG_MASK) != 0) {
    int* addr = (int*)(val - 1);
    fprintf(out, "(");
    int len = addr[0];
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    fprintf(out, ")");
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}

int print(int val) {
  printHelp(stdout, val);
  printf("\n");
  return val;
}

int printStack(int val, int* esp, int* ebp, int args) {
  printf("ESP: %#010x\t==>  ", (uint)esp);
  print(*esp);
  printf("EBP: %#010x\t==>  ", (uint)ebp);
  print(*ebp);
  printf("(difference: %d)\n", esp - ebp);
  printf("Requested return val: %#010x ==> ", val);
  print(val);

  if (esp > ebp) {
    printf("Error: ESP and EBP are not properly oriented\n");
  } else {
    for (int* cur = esp + 1; cur < ebp + args + 2; cur++) {
      if (cur == ebp) {
        printf("EBP %#010x: %#010x\t ==>  old ebp\n", (uint)cur, *cur);
      } else if (cur == ebp + 1) {
        printf("    %#010x: %#010x\t ==>  saved ret\n", (uint)cur, *cur);
      } else {
        printf("    %#010x: %#010x\t ==>  ", (uint)cur, *cur);
        print(*cur);
      }
    }
  }
  return val;
}

void error(int i) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number\n");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number\n");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error: logic expected a boolean\n");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean\n");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: integer overflow\n");
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple\n");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get\n");
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get\n");
    break;
  case ERR_INDEX_NOT_NUM:
    fprintf(stderr, "Error: get expected numer for index\n");
    break;
  case ERR_NOT_LAMBDA:
    fprintf(stderr, "Error: application expected a lambda/function\n");
    break;
  case ERR_WRONG_ARITY:
    fprintf(stderr, "Error: wrong arity for lambda/function\n");
    break;
  default:
    fprintf(stderr, "Error: unknown error code: %d\n", i);
  }
  exit(i);
}

int main(int argc, char** argv) {
  int* HEAP = calloc(100000, sizeof (int));

  int result = our_code_starts_here(HEAP);
  print(result);
  free(HEAP);
  return 0;
}
