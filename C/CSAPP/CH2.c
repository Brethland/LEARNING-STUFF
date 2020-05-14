#include <stdio.h>
#include <memory.h>
#include <stdlib.h>
#include <assert.h>

typedef unsigned char *byte_pointer;

void show_bytes(byte_pointer x, size_t length) {
    size_t i;
    for(i = 0; i < length; i++) {
        printf("%.2x ", *(x + i));
    }
    putchar('\n');
}

void show_int(int d) {
    show_bytes((byte_pointer)&d, sizeof(int));
}

void show_float(float f) {
    show_bytes((byte_pointer)&f, sizeof(float));
}

void show_pointer(void *x) {
    show_bytes((byte_pointer)&x, sizeof(void *));
}

void show_short(short s) {
    show_bytes((byte_pointer)&s, sizeof(short));
}

void show_double(double lf) {
    show_bytes((byte_pointer)&lf, sizeof(double));
}

void show_long(long l) {
    show_bytes((byte_pointer)&l, sizeof(long));
}

int is_little_endian() {
    int x;
    return (x & 0xFF) == (int)*((byte_pointer) &x);
}

int e259(unsigned x, unsigned y) {
    return (x & 0xFF) | (y ^ (y & 0xFF));
}

unsigned replace_byte(unsigned x, int i, unsigned char b) {
    return (x ^ (x & (0xFF << (i << 3)))) | (b << (i << 3));
}

int e261(int x) {
    return !(x ^ -1) || !x || !((x & 0xFF) ^ 0xFF) || !((x >> ((sizeof(int) - 1) << 3)) & 0xFF);
}

int int_shifts_are_arithmetic() {
    return (-1 >> ((sizeof(int) - 1) << 3)) == -1;
}

unsigned srl(unsigned x, int k) {
    unsigned xsra = (int) x >> k;
    return xsra & ~(-1 << ((sizeof(int) << 3) - k));
}

int sra(int x, int k) {
    int xsrl = (unsigned) x >> k;
    int is_negative = !(x & (1 << ((sizeof(int) << 3) - 1))) - 1;
    return xsrl | ((-1 << ((sizeof(int) << 3) - k)) & is_negative);
}

int any_odd_one(unsigned x) {
    return x == 0x55555555;
}

int odd_ones(unsigned x) {
    x ^= x >> 16, x ^= x >> 8, x ^= x >> 4, x ^= x >> 2, x ^= x >> 1;
    return x & 0x1;
}

int leftmost_ones(unsigned x) {
    x |= x >> 16, x |= x >> 8, x |= x >> 4, x |= x >> 2, x |= x >> 1;
    return (x >> 1) + (x && 1); // In case x = 0
}

int int_size_is_32() {
    int set_msb = 1 << 31;
    int beyond_msb = set_msb << 1; // In case overflow
    return set_msb && !beyond_msb;
}

int lower_one_mask(int n) {
    int w = sizeof(int) << 3;
    return (unsigned) -1 >> (w - n); 
}

unsigned rotate_left(unsigned x, int n) {
    int w = sizeof(int) << 3;
    return (x << n) | (x >> (w - n));
}

int fits_bits(int x, int n) {
    int w = sizeof(int) << 3;
    return (x << (w - n) >> (w - n)) == x;
}

typedef unsigned packed_t;

int xbyte(packed_t word, int bytenum) {
    return (word << ((3 - bytenum) << 3)) >> 24;
}

void copy_int(int val, void *but, size_t maxbytes) {
    if(maxbytes >= sizeof(val)) {
        memcpy(buf, (void *) &val, sizeof(val));
    }
}

int saturating_add(int x, int y) {
    int sum = x + y;
    ((!(x & INT_MIN) && !(y & INT_MIN) && (sum & INT_MIN)) && sum = INT_MAX) ||
    (((x & INT_MIN) && (y & INT_MIN) && !(sum & INT_MIN)) && sum = INT_MIN);
    return sum;
}

int tsub_ok(int x, int y) {
    if(y == INT_MIN) return 0;
    int sub = x - y;
    return !((x > 0 && y < 0 && sub < 0) || (x < 0 && y > 0 && sub > 0));
    // Or using tadd_ok except INT_MIN...
}

void *calloc_(size_t memb, size_t size) {
    if(!memb || !size) return NULL;
    size_t block_size = memb * size;
    if(block / size == memb) {
        void *ptr = malloc(block_size);
        assert(ptr != NULL);
        memset(ptr, 0, sizeof(block_size));
        return ptr;
    }
    return NULL;
}

typedef unsigned float_bits;
#ifndef sig
#define sig f >> 31
#endif

#ifndef exp
#define exp (f >> 23) & 0xFF
#endif

#ifndef frac
#define frac f & 0x7FFFFF
#endif

float_bits float_negate(float_bits f) {
    if((exp == 0xFF) && (frac != 0)) return f;
    return ~sig << 31 | exp << 23 | frac;
}

float_bits float_absval(float_bits f) {
    if((exp == 0xFF) && (frac != 0)) return f;
    if(sig == 1) return float_negate(f);
    else return f;
}

float_bits float_twice(float_bits f) {
    if(exp == 0xFF) return f;
    return sig << 31 | (exp ? exp + 1 : 0u) << 23 | (exp == 0 ? frac << 1 : (exp == 0xFF - 1 ? 0u : frac));
}

int float_f2i(float_bits f) {
    // 2.96
}

float_bits float_i2f(int i) {
    // 2.97
}

int main() {
    
}