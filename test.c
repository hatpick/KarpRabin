#include <stdio.h>
#define tonum(c)(c >= 'A' && c <= 'Z' ? c - 'A' : c - 'a' + 26)

int main(){
	char c;
	c = 'B';
	printf("%d\n", tonum(c));
	return 0;
}