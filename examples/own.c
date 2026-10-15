/* examples/own.c -- C of the program's own (examples/own.body): plain C, numbers in, a number out. */
long collatz_steps(long n) { long k = 0; while (n > 1) { n = n % 2 ? 3 * n + 1 : n / 2; k++; } return k; }
