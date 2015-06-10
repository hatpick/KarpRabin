#ifndef KARPRABIN_H
#define KARPRABIN_H

#define KR_PATLEN_MAX PSIZE
#define ALPHABETL 33
#define ALPHABETH 127
#define PRIME 13

int RabinKarpMatch(char *T, char *P, int d, int q, int n, int m);

#endif