#include <stdio.h>
#include "karprabin.h"

int nondet_int();
unsigned int nondet_uint();

int main() {
  int i;  
  unsigned int v;

  char itext[TSIZE];
  char ipat[PSIZE];

  unsigned int itext_s = nondet_uint();
  __CPROVER_assume(itext_s < TSIZE && itext_s > 0);
  unsigned int ipat_s = nondet_uint();
  __CPROVER_assume(ipat_s < PSIZE && ipat_s > 0);

  printf ("LOG: text size = %u, pattern size = %u\n", itext_s, ipat_s);

  for (i = 0; i < itext_s; i++) {
    v = nondet_unit();
    __CPROVER_assume((long)v < (long)ALPHABETH && (long)v > (long)ALPHABETL);
    itext[i] = v;
    __CPROVER_assume(itext[i] < ALPHABETH && itext[i] > ALPHABETL);
    printf ("LOG: text[%d] = %u\n", i, itext[i]);    
  }

  for (i = 0; i < ipat_s; i++) {
    v = nondet_uint();
    __CPROVER_assume((long)v < (long)ALPHABETH && (long)v > (long)ALPHABETL);
    ipat[i] = v;
    __CPROVER_assume(ipat[i] < ALPHABETH && ipat[i] > ALPHABETL);
    printf ("LOG: pat[%d] = %u\n", i, ipat[i]);    
  }

  int index = KarpRabinMatch(itext, ipat, 10, PRIME, itext_s, ipat_s);
  printf ("LOG: return = %d\n", index);  
  
  if (index >= 0) {
    int pos = index;
    int ppos = 0;
    while (ppos < ipat_s) {
      assert (itext[pos] == ipat[ppos]);
      pos++;
      ppos++;
    }
    v = nondet_uint();
    __CPROVER_assume(v < index && v >= 0);
    printf ("LOG: looking at %u\n", v);
    int pos = v;
    int ppos = 0;
    int found = 1;
    while (ppos < ipat_s) {
      if (pos >= itext_s) {
        found = 0;
        break;
      }
      if (itext[pos] != ipat[ppos]) {
        found = 0;
        break;
      }
      pos++;
      ppos++;
    }
    assert(found);    
  } else {
    v = nondet_uint();
    __CPROVER_assume(v < itext_s && v >= 0);
    printf ("LOG: looking at %u\n", v);    
    int pos = v;
    int ppos = 0;
    int found = 1;
    while (ppos < ipat_s) {
      if (pos >= itext_s) {
       found = 0;
       break;
      }
      if (itext[pos] != ipat[ppos]) {
       found = 0;
       break;
      }
      pos++;
      ppos++;
    }
    assert (!found);
  }
}