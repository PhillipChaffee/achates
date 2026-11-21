/* Fixtures for `achates check`: see src/check/tests.rs. */
#include <assert.h>
#include <stddef.h>

struct pair {
    int lo;
    int hi;
};

union u {
    int i;
    float f;
};

int clamp_add(int a, int b)
{
    long long s = (long long)a + b;
    if (s > 1000)
        return 1000;
    if (s < -1000)
        return -1000;
    return (int)s;
}

int twice(int x)
{
    return x / 2 * 4;
}

size_t count_a(const char *s)
{
    size_t n = 0;
    for (; *s; s++) {
        if (*s == 'a')
            n++;
    }
    return n;
}

void order(struct pair *p)
{
    if (p->lo > p->hi) {
        int t = p->lo;
        p->lo = p->hi;
        p->hi = t;
    }
}

int same(int x)
{
    int y = x;
    y = x;
    return y;
}

int via_union(union u v)
{
    return v.i;
}

int half(int x)
{
    assert(x >= 0);
    return x / 2;
}

static int bump(int x)
{
    int y = x;
    int *p = &y;
    *p += 1;
    return *p;
}

/* Each call of `bump` makes a block for `y`: the model must not copy all
   earlier blocks to make a new one. */
int many_calls(void)
{
    int k = 0;
    for (int i = 0; i < 200000; i++)
        k = bump(k);
    return k;
}
