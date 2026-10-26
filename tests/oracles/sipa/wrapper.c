/*
  The C reference oracle for tests/run_tests.py: bech32_encode and
  bech32_decode of segwit_addr.c (sipa/bech32, ref/c, unchanged),
  driven line by line.

  Each line of standard input is one request, with fields in hex as
  for `bech32 serve` (`-` for an empty field):

    d STRING               bech32_decode
    e VARIANT HRP VALUES   bech32_encode, VARIANT bech32 or bech32m

  Each answer is "OK VARIANT HRP VALUES" for a decoding, "OK STRING"
  for an encoding, "FAIL", or "error" for a line this program cannot
  read.

  The library takes C strings, so the string to decode and the HRP to
  encode end at their first NUL byte, if they hold one. The buffers
  are the sizes segwit_addr.h asks for, and more.
*/

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "segwit_addr.h"

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

/* The bytes of a field, NUL-terminated, in a new buffer; their number
   goes in *len. NULL for a field that is not `-` or hex in pairs. */
static unsigned char *field(const char *f, size_t *len) {
  size_t n = strlen(f);
  unsigned char *out;
  if (strcmp(f, "-") == 0) {
    out = calloc(1, 1);
    *len = 0;
    return out;
  }
  if (n == 0 || n % 2 != 0) return NULL;
  out = calloc(n / 2 + 1, 1);
  for (size_t j = 0; j < n / 2; ++j) {
    int hi = hexval(f[2 * j]), lo = hexval(f[2 * j + 1]);
    if (hi < 0 || lo < 0) {
      free(out);
      return NULL;
    }
    out[j] = (unsigned char) (hi * 16 + lo);
  }
  *len = n / 2;
  return out;
}

static void put_field(const unsigned char *b, size_t n) {
  if (n == 0) {
    fputs("-", stdout);
    return;
  }
  for (size_t j = 0; j < n; ++j) printf("%02x", b[j]);
}

static void decode(const char *f) {
  size_t len;
  unsigned char *s = field(f, &len);
  if (s == NULL) {
    puts("error");
    return;
  }
  /* bech32_decode asks for strlen(input) - 6 bytes of HRP and
     strlen(input) - 8 of data. */
  size_t cap = strlen((const char *) s) + 8;
  char *hrp = calloc(cap, 1);
  uint8_t *data = calloc(cap, 1);
  size_t data_len = 0;
  bech32_encoding enc = bech32_decode(hrp, data, &data_len, (const char *) s);
  if (enc == BECH32_ENCODING_NONE) {
    puts("FAIL");
  } else {
    printf("OK %s ", enc == BECH32_ENCODING_BECH32 ? "bech32" : "bech32m");
    put_field((const unsigned char *) hrp, strlen(hrp));
    putchar(' ');
    put_field(data, data_len);
    putchar('\n');
  }
  free(s);
  free(hrp);
  free(data);
}

static void encode(const char *variant, const char *h, const char *v) {
  size_t hrp_len, data_len;
  bech32_encoding enc;
  if (strcmp(variant, "bech32") == 0) enc = BECH32_ENCODING_BECH32;
  else if (strcmp(variant, "bech32m") == 0) enc = BECH32_ENCODING_BECH32M;
  else {
    puts("error");
    return;
  }
  unsigned char *hrp = field(h, &hrp_len);
  unsigned char *data = field(v, &data_len);
  if (hrp == NULL || data == NULL) {
    puts("error");
  } else {
    /* bech32_encode asks for strlen(hrp) + data_len + 8 bytes. */
    char *out = calloc(strlen((const char *) hrp) + data_len + 8, 1);
    if (bech32_encode(out, (const char *) hrp, data, data_len, enc)) {
      fputs("OK ", stdout);
      put_field((const unsigned char *) out, strlen(out));
      putchar('\n');
    } else {
      puts("FAIL");
    }
    free(out);
  }
  free(hrp);
  free(data);
}

int main(void) {
  static char line[1 << 20];
  while (fgets(line, sizeof line, stdin)) {
    size_t n = strlen(line);
    while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
    char *parts[5];
    int k = 0;
    char *p = line;
    while (k < 5) {
      parts[k++] = p;
      p = strchr(p, ' ');
      if (p == NULL) break;
      *p++ = 0;
    }
    if (k == 2 && strcmp(parts[0], "d") == 0) decode(parts[1]);
    else if (k == 4 && strcmp(parts[0], "e") == 0) encode(parts[1], parts[2], parts[3]);
    else puts("error");
  }
  return 0;
}
