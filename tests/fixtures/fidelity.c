/* Each `t_*` function is one fidelity case: it is run as compiled C and as
 * the Lean that Achates emits for it, and the two results are compared.
 * Cases whose behaviour C leaves undefined are run in Lean only. */
#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

typedef long long ll;

/* Integer promotion and wraparound. */
static int add_chars(char a, char b) { return a + b; }
ll t_char_promotion(void) { return add_chars(100, 100); }
static unsigned char wrap8(unsigned char a, unsigned char b) { return a + b; }
ll t_wrap_u8(void) { return wrap8(200, 100); }
static unsigned short wrap16(unsigned short a, unsigned short b) { return a + b; }
ll t_wrap_u16(void) { return wrap16(65535, 2); }
static unsigned wrap32(unsigned a, unsigned b) { return a + b; }
ll t_wrap_u32(void) { return wrap32(4000000000u, 500000000u); }
static unsigned long wrap64(unsigned long a, unsigned long b) { return a * b; }
ll t_wrap_u64(void) { return (ll)(wrap64(~0ul, 5) >> 60); }
static int mul16(unsigned short a, unsigned short b) { return a * b; }
ll t_u16_mul_small(void) { return mul16(300, 300); }
ll t_u16_mul_overflows_int(void) { return mul16(65535, 65535); }
ll t_char_inc(void) { signed char c = 127; c++; return c; }
ll t_uchar_compound(void) { unsigned char c = 250; c += 10; return c; }
ll t_plain_char_is_signed(void) { char c = (char)200; return c; }
ll t_negate_unsigned(void) { unsigned u = 1; return -u; }
ll t_bitops(void) { int a = -8; unsigned b = 0xf0f0u; return (a & 0xff) + (b ^ 0xffu) + (~a) + (b | 1); }

/* Signed overflow and division. */
static int add_int(int a, int b) { return a + b; }
ll t_signed_overflow(void) { return add_int(2147483647, 1); }
static int div_int(int a, int b) { return a / b; }
static int rem_int(int a, int b) { return a % b; }
ll t_div_truncates(void) { return div_int(-7, 2) * 10 + rem_int(-7, 2); }
ll t_div_zero(void) { return div_int(1, 0); }
ll t_int_min_div(void) { return div_int(-2147483647 - 1, -1); }
ll t_int_min_rem(void) { return rem_int(-2147483647 - 1, -1); }
ll t_negate_int_min(void) { int m = -2147483647 - 1; return -m; }

/* Comparison across signedness. */
ll t_cmp_signed_unsigned(void) { int a = -1; unsigned b = 1; return a < b; }
ll t_cmp_long_unsigned(void) { long a = -1; unsigned b = 1; return a < b; }

/* Shifts. */
static unsigned shl(unsigned x, int n) { return x << n; }
static int sshl(int x, int n) { return x << n; }
static int sshr(int x, int n) { return x >> n; }
ll t_shift_31(void) { return shl(1, 31); }
ll t_shift_32(void) { return shl(1, 32); }
ll t_shift_negative_count(void) { return shl(1, -1); }
ll t_shift_into_sign(void) { return sshl(1, 31); }
ll t_shift_right_negative(void) { return sshr(-8, 1); }
ll t_shift_count_is_long(void) { unsigned char c = 1; long n = 20; return c << n; }

/* Short-circuit evaluation with side effects. */
static int counter;
static int bump(int r) { counter++; return r; }
ll t_short_circuit(void) {
    counter = 0;
    int a = bump(0) && bump(1);
    int b = bump(1) || bump(1);
    int c = bump(1) && bump(0);
    return counter * 100 + a * 10 + b + c * 1000;
}
ll t_conditional_side_effects(void) { int i = 0; int r = (i++ > 0) ? i++ : i + 10; return r * 10 + i; }
ll t_comma(void) { int i = 1; int r = (i += 2, i * 5); return r; }

/* Loops. */
ll t_for_break_continue(void) {
    int sum = 0;
    for (int i = 0; i < 100; i++) {
        if (i % 2)
            continue;
        if (i > 10)
            break;
        sum += i;
    }
    return sum;
}
ll t_do_while_continue(void) {
    int i = 0, n = 0;
    do {
        i++;
        if (i == 2)
            continue;
        n += i;
    } while (i < 5);
    return n;
}
ll t_nested_loops(void) {
    int n = 0;
    for (int i = 0; i < 5; i++) {
        int j = 0;
        while (1) {
            if (j > i)
                break;
            j++;
            if (j == 2)
                continue;
            n += j;
        }
        if (i == 3)
            break;
    }
    return n;
}
ll t_infinite_loop(void) { int x = 0; while (1) x ^= 1; return x; }

/* switch. */
static int sw(int x) {
    int r = 0;
    switch (x) {
    case 1:
        r += 1;
    case 2:
        r += 2;
        break;
    default:
        r += 100;
    case 3:
        r += 3;
        break;
    case 4:
        return -1;
    }
    return r;
}
ll t_switch(void) { return sw(1) + 10 * sw(2) + 100 * sw(7) + 100000 * sw(3) + 10000000 * sw(4); }
ll t_switch_in_loop(void) {
    int n = 0;
    for (int i = 0; i < 6; i++) {
        switch (i) {
        case 1:
            continue;
        case 4:
            break;
        case 5:
            n += 1000;
        default:
            n += i;
        }
        n += 10;
    }
    return n;
}

/* goto to a cleanup label. */
static int cleanup(int x) {
    int r = 0;
    char *p = malloc(4);
    if (!p)
        return -1;
    if (x < 0) {
        r = -2;
        goto done;
    }
    for (int i = 0; i < x; i++) {
        if (i == 3) {
            r = 3;
            goto done;
        }
        r += 1;
    }
    r += 10;
done:
    free(p);
    return r;
}
ll t_goto_cleanup(void) {
    int a = cleanup(-1);
    int b = cleanup(2);
    int c = cleanup(9);
    return a + 10 * b + 1000 * c;
}

/* Structs. */
struct pt {
    int x;
    char tag;
    long y;
};
static void move(struct pt *p, int d) {
    p->x += d;
    p->y -= d;
    p->tag = 'k';
}
ll t_struct_through_pointer(void) {
    struct pt p = {1, 'a', 2};
    move(&p, 5);
    return p.x * 100 + p.y + p.tag;
}
static struct pt swap(struct pt p) {
    struct pt q = {(int)p.y, p.tag, p.x};
    return q;
}
ll t_struct_by_value(void) {
    struct pt a = {7, 'c', 9};
    struct pt b = swap(a);
    a = b;
    return a.x * 10 + a.y + swap(b).x * 100;
}
ll t_compound_literal(void) {
    struct pt *p = &(struct pt){3, 'z', 4};
    return p->x + p->y + p->tag;
}
union bits {
    unsigned u;
    unsigned char b[4];
};
ll t_union(void) {
    union bits v;
    v.u = 0x11223344;
    return v.b[0] * 256 + v.b[3];
}
enum colour { RED, GREEN = 5, BLUE };
ll t_enum(void) { enum colour c = BLUE; return c + GREEN + sizeof(struct pt); }

/* Arrays and pointers. */
static int sum(const int *a, int n) {
    int s = 0;
    for (const int *p = a; p < a + n; p++)
        s += *p;
    return s;
}
ll t_array_sum(void) { int a[5] = {1, 2, 3, 4, 5}; return sum(a, 5); }
ll t_2d_array(void) { int m[2][3] = {{1, 2, 3}, {4, 5}}; return m[1][2] + m[0][1] * 10 + m[1][1] * 100; }
ll t_pointer_difference(void) { long a[8]; long *p = &a[6], *q = &a[1]; return (p - q) * 10 + (q < p); }
static void set(int *out, int v) { *out = v; }
ll t_out_parameter(void) { int x; set(&x, 42); return x; }
static int slen(const char *p) {
    int n = 0;
    while (*p) {
        n++;
        p++;
    }
    return n;
}
ll t_string_walk(void) { return slen("hello, world"); }
ll t_reinterpret_bytes(void) {
    unsigned v = 0x11223344;
    unsigned char *b = (unsigned char *)&v;
    return b[0] * 1000 + b[3];
}
ll t_reinterpret_struct(void) {
    struct pt p = {0x01020304, 'q', -1};
    const char *raw = (const char *)&p;
    return raw[0] + raw[4] * 256 + raw[8];
}
ll t_read_past_array(void) { int a[3] = {1, 2, 3}; volatile int i = 3; return a[i]; }
ll t_pointer_past_array(void) { int a[3] = {1, 2, 3}; volatile int i = 5; int *p = a + i; return p != 0; }
ll t_uninitialised_local(void) { int x; return x + 1; }
ll t_use_after_free(void) { char *p = malloc(1); *p = 1; free(p); return *p; }
ll t_double_free(void) { char *p = malloc(1); free(p); free(p); return 0; }
ll t_null_dereference(void) { int *volatile p = 0; return *p; }
ll t_write_string_literal(void) { char *s = (char *)"abc"; s[0] = 'x'; return s[0]; }

/* Recursion. */
static int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
ll t_recursion(void) { return fact(10); }
static int is_odd(int n);
static int is_even(int n) { return n == 0 ? 1 : is_odd(n - 1); }
static int is_odd(int n) { return n == 0 ? 0 : is_even(n - 1); }
ll t_mutual_recursion(void) { return is_even(10) * 10 + is_odd(7); }

/* Function pointers. */
static int twice(int x) { return 2 * x; }
static int negate(int x) { return -x; }
static int apply(int (*f)(int), int x) { return f(x); }
ll t_function_pointer(void) {
    int a = apply(twice, 21);
    int b = apply(negate, 1);
    return a + b * 1000;
}
static int (*const table[2])(int) = {twice, negate};
ll t_function_pointer_table(void) {
    int a = table[1](5);
    return a + table[0](1);
}
ll t_null_function_pointer(void) { int (*volatile f)(int) = 0; return f(1); }

/* Objects with static storage. */
static int g_count = 5;
static int next(void) { return ++g_count; }
ll t_global_updated(void) { next(); next(); return g_count; }
static const unsigned short tab[4] = {10, 20, 30, 40};
ll t_global_table(void) { int s = 0; for (unsigned i = 0; i < 4; i++) s += tab[i]; return s; }
static int tick(void) { static int n = 100; return n++; }
ll t_static_local(void) { tick(); tick(); return tick(); }
static const char *const names[2] = {"ab", "cde"};
ll t_global_string_pointers(void) { return slen(names[0]) * 10 + slen(names[1]); }

/* Library functions. */
ll t_memcpy(void) {
    char a[8] = "abcdefg", b[8];
    memcpy(b, a, 8);
    return b[0] + b[6] * 256 + (b[7] == 0);
}
ll t_memmove_overlapping(void) {
    char b[8] = "abcdefg";
    memmove(b + 2, b, 5);
    return b[2] + b[6] * 256 + b[1] * 65536;
}
ll t_memcpy_overlapping(void) { char b[8] = "abcdefg"; memcpy(b + 2, b, 5); return b[2]; }
static int sign(int x) { return (x > 0) - (x < 0); }
ll t_compare_functions(void) {
    return sign(memcmp("abc", "abe", 3)) + 10 * sign(strcmp("b", "abc")) + 100 * sign(strncmp("abcx", "abcy", 3)) +
           1000 * sign(strcmp("ab", "ab\0c"));
}
ll t_search_functions(void) {
    const char *s = "hello";
    return (strchr(s, 'l') - s) + 10 * (strchr(s, 0) - s) + 100 * (strchr(s, 'z') == 0) +
           1000 * ((const char *)memchr(s, 'o', 5) - s) + 10000 * strlen(s);
}
ll t_memset(void) { unsigned v[2]; memset(v, 0x101, sizeof v); return v[1]; }
ll t_assert_fails(void) { int x = 1; assert(x == 2); return x; }
ll t_abort(void) { abort(); }

/* Floating point. */
static ll bits_of(double d) { ll b; memcpy(&b, &d, sizeof b); return b; }
ll t_float_to_int(void) { double d = 3.99, e = -3.99; return (int)d * 10 + (int)e; }
ll t_float_to_int_out_of_range(void) { double d = 1e10; return (int)d; }
ll t_int_to_float(void) { int i = 16777217; float f = i; return (ll)f; }
ll t_u64_to_double(void) { unsigned long x = ~0ul; double d = x; return d == 18446744073709551616.0; }
ll t_double_arithmetic(void) {
    double a = 0.1, b = 0.2;
    ll x = bits_of(a + b);
    return x ^ bits_of(a * b / 3.0);
}
ll t_single_precision(void) {
    float a = 0.1f, b = 0.2f;
    float c = a + b;
    ll x = bits_of(c);
    return x ^ bits_of(c * 3.0f);
}
ll t_float_compare(void) { double z = 0.0, n = z / z; return (n != n) + 10 * (n < 1.0) + 100 * (1.5 > z); }

/* More of the type system. */
struct inner {
    short a;
    char b[3];
};
struct outer {
    char c;
    struct inner in;
    union {
        int i;
        float f;
    };
    struct {
        long l;
    } s;
    int arr[4];
};
ll t_nested_members(void) {
    struct outer o = {1, {2, "xy"}, {.i = 7}, {9}, {1, 2, 3, 4}};
    o.arr[2] += o.in.a;
    o.s.l *= 3;
    return o.c + o.in.b[1] + o.i * 100 + o.s.l * 1000 + o.arr[2] * 100000 + sizeof o;
}
ll t_bool(void) {
    _Bool b = 5;
    _Bool c = 0.5;
    int *p = 0;
    _Bool d = p;
    return b + c * 10 + d * 100 + (b + b) * 1000;
}
ll t_pointer_compound(void) {
    int a[6] = {1, 2, 3, 4, 5, 6};
    int *p = a;
    p += 2;
    p -= 1;
    int **pp = &p;
    (*pp)++;
    return *p + **pp * 10 + p[-1] * 100;
}
ll t_char_literals(void) { char s[4] = "\xff\x80"; return s[0] + s[1] * 256 + '\xff' * 65536 + s[3]; }
static const struct pt origin = {1, 'o', 2};
static const struct pt *const where = &origin;
ll t_global_struct(void) { return where->x + where->y + origin.tag; }
ll t_unsigned_division(void) { unsigned a = 4000000000u; int b = -2; return a / 3 + (unsigned)b / 2 + a % 7; }
ll t_long_overflow(void) { long a = 9223372036854775807L; volatile long b = 1; return a + b; }
ll t_integer_pointer_round_trip(void) { void *p = (void *)(long)1234; return (long)p; }
ll t_do_while_zero(void) {
    int n = 0;
    do {
        n++;
        if (n)
            break;
        n += 100;
    } while (0);
    return n;
}
ll t_conditional_pointer(void) { int a = 1, b = 2; int *p = a > b ? &a : &b; *p += 5; return a * 10 + b; }
ll t_sizeof(void) { int a[7]; return sizeof a / sizeof a[0] + sizeof(long) * 10 + _Alignof(struct pt) * 100; }
ll t_uninitialised_char(void) { unsigned char c; return c; }
ll t_partly_initialised_struct_copy(void) { struct pt a; a.x = 1; struct pt b = a; return b.x; }
ll t_misaligned_access(void) { char buf[8] = {0}; int *p = (int *)(buf + 1); return *p; }
ll t_address_as_integer(void) { int x = 0; return (long)&x != 0; }

/* Variadic functions: `...` arguments after the default argument
 * promotions, va_start, va_arg, va_copy, va_end, and a va_list passed on. */
static ll va_sum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    ll s = 0;
    for (int i = 0; i < n; i++)
        s = s * 10 + va_arg(ap, int);
    va_end(ap);
    return s;
}
ll t_va_sum(void) { return va_sum(4, 1, 2, 3, 4) + va_sum(0); }
static ll va_mixed(const char *kinds, ...) {
    va_list ap;
    va_start(ap, kinds);
    ll s = 0;
    for (const char *k = kinds; *k; k++) {
        switch (*k) {
        case 'i': s = s * 3 + va_arg(ap, int); break;
        case 'u': s = s * 3 + va_arg(ap, unsigned); break;
        case 'l': s = s * 3 + va_arg(ap, long); break;
        case 'q': s = s * 3 + (ll)va_arg(ap, unsigned long long); break;
        case 'd': s = s * 3 + (ll)(va_arg(ap, double) * 4); break;
        case 's': s = s * 3 + strlen(va_arg(ap, char *)); break;
        case 'c': s = s * 3 + strlen(va_arg(ap, const char *)); break;
        case 'p': s = s * 3 + *va_arg(ap, int *); break;
        }
    }
    va_end(ap);
    return s;
}
ll t_va_mixed(void) {
    int x = 7;
    return va_mixed("iuldqsp", -5, 4000000000u, -3000000000L, 2.75, 1ull << 40, "four", &x);
}
/* char, short and _Bool arrive as int, float as double. */
ll t_va_promotions(void) {
    char c = 'a';
    short h = -300;
    float f = 1.5f;
    _Bool b = 1;
    return va_mixed("iiid", c, h, b, f);
}
/* A signed argument read as its unsigned type when the value fits both,
 * and char * read as void *. */
static ll va_corresponding(int n, ...) {
    va_list ap;
    va_start(ap, n);
    unsigned u = va_arg(ap, unsigned);
    int i = va_arg(ap, int);
    void *p = va_arg(ap, void *);
    va_end(ap);
    return u + i + (p != 0);
}
ll t_va_corresponding(void) { return va_corresponding(3, 5, 6u, "x"); }
static ll va_twice(int n, ...) {
    va_list ap, again;
    va_start(ap, n);
    int first = va_arg(ap, int);
    va_copy(again, ap);
    int a = va_arg(ap, int);
    int b = va_arg(again, int);
    va_end(again);
    va_end(ap);
    va_start(ap, n);
    int restarted = va_arg(ap, int);
    va_end(ap);
    return first * 1000 + a * 100 + b * 10 + restarted;
}
ll t_va_copy(void) { return va_twice(2, 3, 4); }
static ll va_vsum(int n, va_list ap) {
    ll s = 0;
    while (n--)
        s = s * 10 + va_arg(ap, int);
    return s;
}
static ll va_through(int n, ...) {
    va_list ap;
    va_start(ap, n);
    ll s = va_vsum(n, ap);
    va_end(ap);
    return s;
}
ll t_va_list_passed_on(void) { return va_through(3, 7, 8, 9); }
struct va_pair { int a, b; };
static ll va_count(int n, ...) { return n; }
ll t_va_struct_argument(void) { struct va_pair p = {1, 2}; return va_count(2, p, 3.0); }
ll t_va_past_end(void) { return va_sum(3, 1, 2); }
ll t_va_wrong_type(void) { return va_sum(1, 2.0); }
ll t_va_long_as_long_long(void) { return va_mixed("q", 5L); }
ll t_va_negative_as_unsigned(void) { return va_corresponding(3, -5, 6, "x"); }
ll t_va_int_as_pointer(void) { return va_mixed("p", 0); }
static ll va_float(int n, ...) {
    va_list ap;
    va_start(ap, n);
    float f = va_arg(ap, float);
    va_end(ap);
    return (ll)f;
}
ll t_va_float(void) { return va_float(1, 1.0f); }
static ll va_no_end(int n, ...) {
    va_list ap;
    va_start(ap, n);
    return va_arg(ap, int);
}
ll t_va_missing_end(void) { return va_no_end(1, 5); }
static ll va_reuse(int n, ...) {
    va_list ap;
    va_start(ap, n);
    ll s = va_vsum(1, ap);
    s += va_arg(ap, int);
    va_end(ap);
    return s;
}
ll t_va_used_after_passing(void) { return va_reuse(2, 1, 2); }
static ll va_restart(int n, ...) {
    va_list ap;
    va_start(ap, n);
    va_start(ap, n);
    va_end(ap);
    return n;
}
ll t_va_start_twice(void) { return va_restart(0); }
static ll va_end_twice(int n, ...) {
    va_list ap;
    va_start(ap, n);
    va_end(ap);
    va_end(ap);
    return n;
}
ll t_va_end_twice(void) { return va_end_twice(0); }
/* C11 makes this undefined and C23 defines it; the model does not choose. */
ll t_va_qualified_pointer(void) { return va_mixed("c", "x"); }

/* Operands C leaves unordered whose effects cannot meet: different members
 * reached from one pointer, an allocation beside reads, two allocations,
 * calls through a pointer whose possible targets only read. */
struct order_list { int *values; int num; void **keys; };
static int *order_push(struct order_list *l) { return &l->values[l->num++]; }
ll t_order_disjoint_members(void) {
    int v[4] = {0};
    struct order_list l = {v, 1, 0};
    int *p = order_push(&l);
    *p = 7;
    return l.num * 100 + v[1] * 10 + (p - v);
}
static int order_add_key(struct order_list *l) {
    l->keys[l->num] = malloc(8);
    int ok = l->keys[l->num] != 0;
    free(l->keys[l->num]);
    return ok;
}
ll t_order_allocation_beside_reads(void) {
    void *keys[2] = {0, 0};
    struct order_list l = {0, 1, keys};
    int r = order_add_key(&l);
    return r * 10 + (keys[0] == 0);
}
static int order_pair(char *a, char *b) {
    int r = a != b;
    free(a);
    free(b);
    return r;
}
ll t_order_two_allocations(void) { return order_pair(malloc(1), malloc(2)); }
static int order_inc(const int *x, int y, int z) { return *x + y + z; }
static int order_dbl(const int *x, int y, int z) { return *x * y - z; }
static int (*const order_fns[2])(const int *, int, int) = {order_inc, order_dbl};
ll t_order_indirect_readers(void) {
    int x = 5;
    return order_fns[0](&x, 1, 2) * 100 + order_fns[1](&x, 3, 4);
}
/* The model keeps no NaN payload or sign, so it cannot give a NaN's bytes. */
ll t_nan_bytes(void) {
    volatile double zero = 0.0;
    double d = zero / zero;
    unsigned char b[8];
    memcpy(b, &d, 8);
    return b[7];
}
