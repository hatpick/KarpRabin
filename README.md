<h1>Verifying Karp-Rabin Algorithm</h1>

<h2>Karp-Rabin Algorithm</h2>
Karp-Rabin is a string searching algorithm. This algorithm uses hashing to speed up the “stupid” algorithm <strong>(O(mn))</strong> for string searching.

```C
public int stupidSearch(String text, String pattern, int m, int n) {
   if(n*m == 0 || m > n) return -1;
   for (int i = 0; i < n - m + 1; i++) {
       String candidate = text.substring(i, i + m);
       if(candidate.compareTo(pattern) == 0) return i;
   }
   return -1;
}
```

Hashing provides a simple method to avoid a quadratic number of character comparisons in most practical situations. Instead of checking at each position of the text if the pattern occurs, it seems to be more efficient to check only if the contents of the window “looks like” the pattern. In order to check the resemblance between these two words an hashing function is used.
Algorithm runs in <strong>O(m+n)</strong> where m is the length of the text and n is the length of the pattern. If it finds a match, it returns the start index of the pattern in the given text.

```C
#define tonum(c)(c >= 'A' && c <= 'Z' ? c - 'A' : c - 'a' + 26)
int mod(int a, int p, int m) {
   int sqr;
   if (p == 0)
       return 1;
   sqr = mod(a, p / 2, m) % m;
   sqr = (sqr * sqr) % m;
   if (p & 1)
       return ((a % m) * sqr) % m;
   else
       return sqr;
}
int KarpRabinMatch(char * T, char * P, int d, int q, int n, int m) {
   int i, j, p, t, h, found;
   h = mod(d, m - 1, q);
   p = t = 0;
   for (i = 0; i < m; i++) {
       p = (d * p + tonum(P[i])) % q;
       t = (d * t + tonum(T[i])) % q;
   }
   for (i = 0; i <= n - m; i++) {
       if (p == t) {
           found = 1;
           for (j = 0; j < m; j++)
               if (P[j] != T[i + j]) {
                   found = 0;
                   break;
               }
           if (found) return i;
       } else {
           t = (d * (t - ((tonum(T[i]) * h) % q)) + tonum(T[i + m])) % q;
       }
   }
   return -1;
}
```



<h2>Harness</h2>
To verify a C implementation of this algorithm, I wrote the following harness. There are two major cases that I need to take care of:
<ol>
<li>
Algorithm finds a match.
<ol type="a">
<li>Must verify that match</li>
<li>Must verify there is no match before that.</li>
</ol>
</li>
<li>
Algorithm doesn’t find a match.
<ol type="a">
<li>Must verify that there is no match.</li>
</ol>
</li>
<li>For simplicity, I asked CBMC to assume only values in the following range for text and pattern strings: <strong>!</strong> (33 ASCII) to <strong>~</strong> (126 ASCII) http://www.asciitable.com/ </li>
</ol>

The following code is annotated with the major cases:
```C
int nondet_int();
unsigned int nondet_uint();

int main() {
   int i;
   unsigned int v;

   char itext[TSIZE];
   char ipat[PSIZE];

   /* Assign text size, assign pattern size */
   unsigned int itext_s = nondet_uint();
   __CPROVER_assume(itext_s < TSIZE && itext_s > 0);
   unsigned int ipat_s = nondet_uint();
   __CPROVER_assume(ipat_s < PSIZE && ipat_s > 0);
   /* Assign text size, assign pattern size */

   printf ("LOG: text size = %u, pattern size = %u\n", itext_s, ipat_s);

   /* Assign value to text in the given range (in 3) */
   for (i = 0; i < itext_s; i++) {
       v = nondet_unit();
       __CPROVER_assume((long)v < (long)ALPHABETH && (long)v > (long)ALPHABETL);
       itext[i] = v;
       __CPROVER_assume(itext[i] < ALPHABETH && itext[i] > ALPHABETL);
       printf ("LOG: text[%d] = %u\n", i, itext[i]);
   }
   /* Assign value to text in the given range (in 3) */

   /* Assign value to pattern in the given range (in 3) */
   for (i = 0; i < ipat_s; i++) {
       v = nondet_uint();
       __CPROVER_assume((long)v < (long)ALPHABETH && (long)v > (long)ALPHABETL);
       ipat[i] = v;
       __CPROVER_assume(ipat[i] < ALPHABETH && ipat[i] > ALPHABETL);
       printf ("LOG: pat[%d] = %u\n", i, ipat[i]);
   }
   /* Assign value to text in the given range (in 3) */

   /* Call KarpRabin function to find the matching index */
   int index = KarpRabinMatch(itext, ipat, 10, PRIME, itext_s, ipat_s);
   printf ("LOG: return = %d\n", index);
   /* Call KarpRabin function to find the matching index */

   /* Case 1 */
   if (index > 0) {
       int pos = index;
       int ppos = 0;
       /* Case 1-a*/
       while (ppos < ipat_s) {
           assert (itext[pos] == ipat[ppos]);
           pos++;
           ppos++;
       }
       /* Case 1-a*/

       /* Case 1-b*/
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
       assert (found);
       /* Case 1-b*/
   /* Case 1 */
   /* Case 2 */
   } else {
       /* Case 2-a */
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
       /* Case 2-a */
   }
   /* Case 2 */
}
```

<h2>Results</h2>
I was able to verify this implementation using cbmc and the following command:
```bash
cbmc harness.c karprabin.c -DTSIZE=8 -DPSIZE=2 --bounds-check --pointer-check --unwind 10
```
Which means that text size upper bound set at 10 and pattern size upper bound set at 3, my harness code is able to verify my implementation of KarpRabin algorithm.

To make sure that my harness code is good enough at verifying this algorithm, I used mutation analysis. First I had to generate enough mutations (200+) for my implementation of algorithm. Then after refining the mutations (i.e dropping those non-compilable mutations) using the same harness, I tried to verify mutations one by one. My harness code was able to eliminate more than 90% of the mutations and the remaining survivors were the equivalent mutations:
```C
Original: for (i = 0; i <= n - m; i++) {    =>   Mutation: for (i = 0; i != n - m; i++) {
Original: for (j = 0; j < m; j++)    =>   Mutation: for (j = 0; j != m; j++)
etc.
```

Mutation analysis shows that my harness code is good enough in verifying the Karp-Rabin algorithm.

p.s: I also tried to run my harness on a buggy version of the algorithm in which I intentionally planted a bug in the code and the harness was able to catch it successfully. I manually tried this multiple times before I did my thorough mutation analysis.
