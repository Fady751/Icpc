#ifndef AVL_MASTER
#define AVL_MASTER
#include <string.h>


enum avl_direction
{
    AVL_LOW_TO_HIGH,
    AVL_HIGH_TO_LOW,
};

struct avl_node
{
    void *key;
    void *value;
    struct avl_node *rel[3]; // [0, 1, 2] = [left child, right child, parent]
    int height;
};

struct avl_manager
{
    struct avl_node *root;
    size_t count;
    int affected;
    int search_only;
    int (*comparator)(const void *, const void *);
    struct avl_node *(*inserter)(void *, const void *);
    void *inserter_argument;
};

#define avl_left rel[0]
#define avl_right rel[1]
#define avl_parent rel[2]

// h_ prefixed functions are intended for internal usage only.
// Thanks to the rotations, the heights of your BSTs are always lesser than 1.44 * log2(number of keys).
static inline void h_avl_rotate(struct avl_node *a, const int rel_a, struct avl_node *b, const int rel_b)
{
    if ((b->rel[rel_b] = a->rel[rel_a]))
    {
        a->rel[rel_a]->avl_parent = b;
    }
    else
    {
        b->rel[rel_b] = a->rel[rel_a];
    }
    b->avl_parent = a;
    a->rel[rel_a] = b;
}

static inline void h_avl_swap(struct avl_node **root, const struct avl_node *a, struct avl_node *b)
{
    if (a->avl_parent)
    {
        a->avl_parent->rel[a->avl_parent->avl_right == a] = b;
    }
    else
    {
        *root = b;
    }
    b->avl_parent = a->avl_parent;
}

static inline int h_avl_height(const struct avl_node *node)
{
    if (node->avl_right)
    {
        if (node->avl_left)
        {
            return 1 + node->rel[node->avl_right->height > node->avl_left->height]->height;
        }
        else
        {
            if (node->avl_right)
            {
                return 1 + node->avl_right->height;
            }
            else
            {
                return 1;
            }
        }
    }
    else
    {
        if (node->avl_left)
        {
            return 1 + node->avl_left->height;
        }
        else
        {
            if (node->avl_right)
            {
                return 1 + node->avl_right->height;
            }
            else
            {
                return 1;
            }
        }
    }
}

static inline char h_avl_op_kind(const struct avl_node *node)
{
    if (node->avl_left)
    {
        if (node->avl_right)
        {
            if (node->avl_left->height > node->avl_right->height)
            {
                return 'L';
            }
            else
            {
                return 'R';
            }
        }
        else
        {
            return 'L';
        }
    }
    else
    {
        return 'R';
    }
}

static inline char h_avl_has_op(const struct avl_node *node)
{
    switch ((node->avl_left ? node->avl_left->height : 0) - (node->avl_right ? node->avl_right->height : 0))
    {
    case 2:
        return 'L';
    case -2:
        return 'R';
    }
    return 0;
}

// Used after an insertion to execute at most 1 rotation.
static inline void h_avl_rebalance(struct avl_node **root, struct avl_node *top)
{
    struct avl_node *middle, *bottom;
    char op[3];
    int i;
    // Maybe "top" is now too tall.
    while (top)
    {
        i = top->height;
        top->height = h_avl_height(top);
        if (i == top->height)
        {          // Height not change ?
            break; // Retracing can stop.
        }
        *op = h_avl_has_op(top);
        if (*op)
        {
            middle = top->rel[*op == 'R'];
            op[1] = h_avl_op_kind(middle);
            i = op[1] == 'R';
            bottom = middle->rel[i];
            top->height = bottom->height;
            if (op[0] == op[1])
            {
                h_avl_swap(root, top, middle);
                h_avl_rotate(middle, !i, top, i); // LL or RR done.
            }
            else
            {
                h_avl_swap(root, top, bottom);
                h_avl_rotate(bottom, !i, middle, i);
                h_avl_rotate(bottom, i, top, !i);  // LR or RL done.
                middle->height = bottom->height++; // The 3 height has changed.
            }
            // Rebalanced out, nobody above would notice.
            break;
        }
        top = top->avl_parent;
    }
}

struct avl_node *avl_at(struct avl_manager *const manager, const void *key)
{
    // #1 Abdul Bari jDM6_TnYIqE
    struct avl_node *curr, *new_node;
    int i;
    if (manager->root)
    {
        curr = manager->root;
        for (;;)
        {
            const int cmp = manager->comparator(key, curr->key);
            if (cmp > 0)
            {
                if (curr->avl_right)
                {
                    curr = curr->avl_right;
                }
                else
                {
                    if (manager->search_only)
                    {
                        return 0;
                    }
                    i = 1;
                    break;
                }
            }
            else if (cmp == 0)
            {
                manager->affected = 0;
                return curr;
            }
            else
            {
                if (curr->avl_left)
                {
                    curr = curr->avl_left;
                }
                else
                {
                    if (manager->search_only)
                    {
                        return 0;
                    }
                    i = 0;
                    break;
                }
            }
        }
    }
    else if (manager->search_only)
    {
        return 0;
    }
    else
    {
        curr = 0;
        i = -1;
    }
    // This may replace root.
    new_node = *(i >= 0 ? &curr->rel[i] : &manager->root) = manager->inserter(manager->inserter_argument, key);
    new_node->height = 1;
    new_node->avl_parent = curr;
    h_avl_rebalance(&manager->root, curr);
    ++manager->count;
    manager->affected = 1;
    return new_node;
}

__attribute__((unused)) void avl_walk(const struct avl_manager *manager, void (*fn)(const struct avl_node *, void *), void *args, const enum avl_direction direction)
{
    struct avl_node *stack[64], *curr;
    int index = 0;
    const int opposite = !direction;
    if (manager->root)
    {
        curr = manager->root;
        do
        {
            while (curr)
            {
                stack[index++] = curr;
                curr = curr->rel[direction];
            }
            if (index)
            {
                curr = stack[--index];
                fn(curr, args);
                curr = curr->rel[opposite];
            }
        } while (index || curr);
    }
}

#endif // AVL_MASTER

#ifndef CINT_MASTER
#define CINT_MASTER

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

// These "cint" functions are provided to allow computation with large numbers (especially greater than the default limit)

// memory is supposed provided by the system, allocations are passed to "assert".
// cint use "computation sheets" instead of global vars.

// the functions name that terminates by "i" means immediate, in place.
// the functions name that begin by "h_" means intended for internal usage.

typedef int64_t h_cint_t;

static const h_cint_t cint_exponent = 4 * sizeof(h_cint_t) - 1;
static const h_cint_t cint_base = (h_cint_t)1 << cint_exponent;
static const h_cint_t cint_mask = cint_base - 1;
static const char *cint_alpha = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

typedef struct
{
    h_cint_t *mem; // reserved data pointer.
    h_cint_t *end;
    h_cint_t nat; // -1 = negative, +1 = positive, (zero is a positive)
    size_t size;
} cint;

typedef struct
{
    size_t immediate_state;
    cint temp[10];
} cint_sheet;

static cint_sheet *cint_new_sheet(const size_t bits)
{
    // a computation sheet is required by function needing temporary vars.
    cint_sheet *sheet = calloc(1, sizeof(cint_sheet));
    assert(sheet);
    const size_t num_size = 2 + bits / cint_exponent;
    if (sheet)
        for (size_t i = 0; i < 10; ++i)
        {
            sheet->temp[i].nat = 1;
            sheet->temp[i].mem = sheet->temp[i].end = calloc(num_size, sizeof(h_cint_t));
            assert(sheet->temp[i].mem);
            sheet->temp[i].size = num_size;
        }
    return sheet;
}

__attribute__((unused)) static inline void cint_negate(cint *N)
{
    N->nat *= 1 - ((N->mem != N->end) << 1);
}

static void cint_clear_sheet(cint_sheet *sheet)
{
    for (size_t i = 0; i < 10; ++i)
        free(sheet->temp[i].mem);
    free(sheet);
}

static size_t cint_count_bits(const cint *num)
{
    size_t res = 0;
    if (num->end != num->mem)
    {
        for (; *(num->end - 1) >> ++res;)
            ;
        res += (num->end - num->mem - 1) * cint_exponent;
    }
    return res;
}

static size_t cint_count_zeros(const cint *num)
{
    // it returns the total of "right shifts" it takes to turn "num" odd.
    size_t res = 0, i;
    h_cint_t *ptr;
    for (ptr = num->mem; ptr < num->end && !*ptr; ++ptr, res += cint_exponent)
        ;
    for (i = 0; !(*ptr >> i & 1); ++i)
        ;
    return res + i;
}

__attribute__((unused)) static inline int cint_compare_char(const cint *N, const h_cint_t val)
{
    const h_cint_t res = *N->mem + *(N->mem + 1) - val;
    return (res > 0) - (res < 0);
}

static inline int h_cint_compare(const cint *lhs, const cint *rhs)
{
    h_cint_t res = (h_cint_t)((lhs->end - lhs->mem) - (rhs->end - rhs->mem));
    if (res == 0 && rhs->end != rhs->mem)
        for (const h_cint_t *l = lhs->end, *r = rhs->end; !(res = *--l - *--r) && l != lhs->mem;)
            ;
    return (res > 0) - (res < 0);
}

static inline int cint_compare(const cint *lhs, const cint *rhs)
{
    // compare the sign first, then the data
    int res = (int)(lhs->nat - rhs->nat);
    if (res == 0)
        res = (int)lhs->nat * h_cint_compare(lhs, rhs);
    return res;
}

static void cint_init(cint *num, size_t bits, long long int value)
{
    num->size = bits / cint_exponent;
    num->size += 8 - num->size % 4;
    num->end = num->mem = calloc(num->size, sizeof(*num->mem));
    assert(num->mem);
    if ((num->nat = 1 - ((value < 0) << 1)) < 0)
        value = -value;
    for (; value; *num->end = (h_cint_t)(value % cint_base), value /= cint_base, ++num->end)
        ;
}

static inline void cint_erase(cint *num)
{
    num->nat = 1, num->end = memset(num->mem, 0, (num->end - num->mem) * sizeof(h_cint_t));
}

static void cint_reinit(cint *num, long long int value)
{
    // it's like an initialization, but there is no memory allocation here
    num->end = memset(num->mem, 0, (num->end - num->mem) * sizeof(h_cint_t));
    if ((num->nat = 1 - ((value < 0) << 1)) < 0)
        value = -value;
    for (; value; *num->end = (h_cint_t)(value % cint_base), value /= cint_base, ++num->end)
        ;
}

__attribute__((unused)) static inline cint *cint_immediate(cint_sheet *sheet, const long long int value)
{
    cint *res = &sheet->temp[8 + (sheet->immediate_state++ & 1)];
    cint_reinit(res, value);
    return res;
}

static void cint_reinit_by_string(cint *num, const char *str, const int base)
{
    cint_erase(num);
    for (; *str && memchr(cint_alpha, *str, base) == 0; num->nat *= 1 - ((*str++ == '-') << 1))
        ;
    for (h_cint_t *p; *str; *num->mem += (h_cint_t)((char *)memchr(cint_alpha, *str++, base) - cint_alpha), num->end += *num->end != 0)
        for (p = num->end; --p >= num->mem; *(p + 1) += (*p *= base) >> cint_exponent, *p &= cint_mask)
            ;
    for (h_cint_t *p = num->mem; p < num->end; *(p + 1) += *p >> cint_exponent, *p++ &= cint_mask)
        ;
    num->end += *num->end != 0, num->mem != num->end || (num->nat = 1);
}

static char *cint_to_string(const cint *num, const int base_out)
{
    // Very interesting function, only problem is that it can be slow.
    h_cint_t a, b, *c = num->end;
    size_t d, e = 1;
    char *s = malloc(2);
    assert(s);
    strcpy(s, "0");
    for (; --c >= num->mem;)
    {
        for (a = *c, d = e; d;)
        {
            b = (h_cint_t)((char *)memchr(cint_alpha, s[--d], base_out) - cint_alpha), b = b * cint_base + a;
            s[d] = cint_alpha[b % base_out];
            a = b / base_out;
        }
        for (; a; s = realloc(s, ++e + 1), assert(s), memmove(s + 1, s, e), *s = cint_alpha[a % base_out], a /= base_out)
            ;
    }
    if (num->nat < 0)
        s = realloc(s, e + 2), assert(s), memmove(s + 1, s, e + 1), *s = '-';
    return s;
}

__attribute__((unused)) static inline void cint_init_by_string(cint *num, const size_t bits, const char *str, const int base)
{
    cint_init(num, bits, 0), cint_reinit_by_string(num, str, base);
}

static void cint_reinit_by_double(cint *num, const double value)
{
    // sometimes tested, it worked.
    cint_erase(num);
    uint64_t memory;
    memcpy(&memory, &value, sizeof(value));
    uint64_t ex = (memory << 1 >> 53) - 1023, m_1 = 1ULL << 52;
    if (ex < 1024)
    {
        h_cint_t m_2 = 1 << ex % cint_exponent;
        num->nat *= (value > 0) - (value < 0);
        num->end = 1 + num->mem + ex / cint_exponent;
        h_cint_t *n = num->end;
        for (*(n - 1) |= m_2; --n >= num->mem; m_2 = cint_base)
            for (; m_2 >>= 1;)
                if (m_1 >>= 1)
                    *n |= m_2 * ((memory & m_1) != 0);
                else
                    return;
    }
}

__attribute__((unused)) static double cint_to_double(const cint *num)
{
    // sometimes tested, it worked.
    uint64_t memory = cint_count_bits(num) + 1022, m_write = 1ULL << 52, m_read = 1 << memory % cint_exponent;
    double res = 0;
    memory <<= 52;
    for (h_cint_t *n = num->end; --n >= num->mem; m_read = 1LL << cint_exponent)
        for (; m_read >>= 1;)
            if (m_write >>= 1)
                memory |= m_write * ((*n & m_read) != 0);
            else
                n = num->mem, m_read = 0;
    memcpy(&res, &memory, sizeof(memory));
    return (double)num->nat * res;
}

__attribute__((unused)) static inline void cint_init_by_double(cint *num, const size_t size, const double value) { cint_init(num, size, 0), cint_reinit_by_double(num, value); }

static void cint_dup(cint *to, const cint *from)
{
    // duplicate number (no verification about overlapping or available memory, caller must check)
    const size_t b = from->end - from->mem, a = to->end - to->mem;
    memcpy(to->mem, from->mem, b * sizeof(*from->mem));
    to->end = to->mem + b;
    to->nat = from->nat;
    if (b < a)
        memset(to->end, 0, (a - b) * sizeof(*to->mem));
}

static void cint_rescale(cint *num, const size_t bits)
{
    // rarely tested, it should allow to resize a number transparently.
    size_t new_size = 1 + bits / cint_exponent;
    new_size = new_size + 8 - new_size % 8;
    const size_t curr_length = num->end - num->mem;
    if (num->size < new_size)
    {
        num->mem = realloc(num->mem, new_size * sizeof(h_cint_t));
        assert(num->mem);
        memset(num->mem + num->size, 0, (new_size - num->size) * sizeof(h_cint_t));
        num->end = num->mem + curr_length;
        num->size = new_size;
    }
    else if (curr_length >= new_size)
    {
        cint_erase(num); // can't keep the number when reducing its size under the minimal size it needs.
        num->end = num->mem = realloc(num->mem, (num->size = new_size) * sizeof(h_cint_t));
        assert(num->mem); // realloc can fail on trimming.
    }
}

static inline cint *h_cint_tmp(cint_sheet *sheet, const int id, const cint *least)
{
    // request at least the double of "least" to allow performing multiplication then modulo...
    const size_t needed_size = (1 + least->end - least->mem) << 1;
    if (sheet->temp[id].size < needed_size)
    {
        const size_t needed_bits = (1 + ((needed_size * cint_exponent) >> 10)) << 10;
        cint_rescale(&sheet->temp[id], needed_bits);
    }
    return &sheet->temp[id];
}

static void h_cint_addi(cint *lhs, const cint *rhs)
{
    // perform an addition (without caring of the sign)
    h_cint_t *l = lhs->mem;
    for (const h_cint_t *r = rhs->mem; r < rhs->end;)
        *l += *r++, *(l + 1) += *l >> cint_exponent, *l++ &= cint_mask;
    for (; *l & cint_base; *(l + 1) += *l >> cint_exponent, *l++ &= cint_mask)
        ;
    if (rhs->end - rhs->mem > lhs->end - lhs->mem)
        lhs->end = lhs->mem + (rhs->end - rhs->mem);
    lhs->end += *lhs->end != 0;
}

static void h_cint_subi(cint *lhs, const cint *rhs)
{
    // perform a subtraction (without caring about the sign, it performs high subtract low)
    h_cint_t a = 0, cmp, *l, *r, *e, *o;
    if (lhs->mem == lhs->end)
        cint_dup(lhs, rhs);
    else if (rhs->mem != rhs->end)
    {
        cmp = h_cint_compare(lhs, rhs);
        if (cmp)
        {
            if (cmp < 0)
                l = lhs->mem, r = rhs->mem, e = rhs->end, lhs->nat = -lhs->nat;
            else
                l = rhs->mem, r = lhs->mem, e = lhs->end;
            for (o = lhs->mem; r < e; *o = *r++ - *l++ - a, a = (*o & cint_base) != 0, *o++ &= cint_mask)
                ;
            for (*o &= cint_mask, o += a; --o > lhs->mem && !*o;)
                ;
            lhs->end = 1 + o;
        }
        else
            cint_erase(lhs);
    }
}

// regular functions, they care of the input sign
static inline void cint_addi(cint *lhs, const cint *rhs) { lhs->nat == rhs->nat ? h_cint_addi(lhs, rhs) : h_cint_subi(lhs, rhs); }

static inline void cint_subi(cint *lhs, const cint *rhs) { lhs->nat == rhs->nat ? lhs->nat = -lhs->nat, h_cint_subi(lhs, rhs), lhs->mem == lhs->end || (lhs->nat = -lhs->nat), (void)0 : h_cint_addi(lhs, rhs); }

static void cint_left_shifti(cint *num, const size_t bits)
{
    // execute a left shift immediately over the input, for any amount of bits (no verification about available memory)
    if (num->end != num->mem)
    {
        const size_t a = bits / cint_exponent, b = bits % cint_exponent, c = cint_exponent - b;
        if (a)
        {
            memmove(num->mem + a, num->mem, (num->end - num->mem + 1) * sizeof(h_cint_t));
            memset(num->mem, 0, a * sizeof(h_cint_t));
            num->end += a;
        }
        if (b)
            for (h_cint_t *l = num->end, *e = num->mem + a; --l >= e; *(l + 1) |= *l >> c, *l = *l << b & cint_mask)
                ;
        num->end += *(num->end) != 0;
    }
}

static void cint_right_shifti(cint *num, const size_t bits)
{
    size_t a = bits / cint_exponent, b = bits % cint_exponent, c = cint_exponent - b;
    if (num->end - a > num->mem)
    {
        if (a)
        {
            if (num->mem + a > num->end)
                a = num->end - num->mem;
            memmove(num->mem, num->mem + a, (num->end - num->mem) * sizeof(h_cint_t));
            memset(num->end -= a, 0, a * sizeof(h_cint_t));
        }
        if (b)
            for (h_cint_t *l = num->mem; l < num->end; *l = (*l >> b | *(l + 1) << c) & cint_mask, ++l)
                ;
        if (num->end != num->mem)
            num->end -= *(num->end - 1) == 0, num->end == num->mem && (num->nat = 1);
    }
    else
        cint_erase(num);
}

static void cint_mul(const cint *lhs, const cint *rhs, cint *res)
{
    // the multiplication (no Karatsuba Algorithm, it's the "slow" multiplication)
    h_cint_t *l, *r, *o, *p;
    cint_erase(res);
    if (lhs->mem != lhs->end && rhs->mem != rhs->end)
    {
        res->nat = lhs->nat * rhs->nat, res->end += (lhs->end - lhs->mem) + (rhs->end - rhs->mem) - 1;
        for (l = lhs->mem, p = res->mem; l < lhs->end; ++l)
            for (r = rhs->mem, o = p++; r < rhs->end; *(o + 1) += (*o += *l * *r++) >> cint_exponent, *o++ &= cint_mask)
                ;
        res->end += *res->end != 0;
    }
}

static void cint_powi(cint_sheet *sheet, cint *n, const cint *exp)
{
    // read the exponent bit by bit to perform the "fast" exponentiation in place.
    if (n->mem != n->end)
    {
        size_t bits = cint_count_bits(exp);
        switch (bits)
        {
        case 0:
            cint_reinit(n, n->mem != n->end);
            break;
        case 1:
            break;
        default:;
            cint *a = h_cint_tmp(sheet, 0, n);
            cint *b = h_cint_tmp(sheet, 1, n), *res = n, *tmp;
            cint_erase(a), *a->end++ = 1;
            h_cint_t mask = 1;
            for (const h_cint_t *ptr = exp->mem;;)
            {
                if (*ptr & mask)
                    cint_mul(a, n, b), tmp = a, a = b, b = tmp;
                if (--bits)
                {
                    cint_mul(n, n, b), tmp = n, n = b, b = tmp;
                    mask <<= 1;
                    if (mask == cint_base)
                        mask = 1, ++ptr;
                }
                else
                    break;
            }
            if (res != a)
                cint_dup(res, a);
        }
    }
}

static inline void cint_pow(cint_sheet *sheet, const cint *n, const cint *exp, cint *res)
{
    cint_dup(res, n);
    cint_powi(sheet, res, exp);
}

__attribute__((unused)) static void cint_binary_div(const cint *lhs, const cint *rhs, cint *q, cint *r)
{
    // the original division algorithm, it doesn't take any temporary variable.
    cint_erase(r);
    if (rhs->end == rhs->mem)
        for (q->nat = lhs->nat * rhs->nat, q->end = q->mem; q->end < q->mem + q->size; *q->end++ = cint_mask)
            ; // DBZ
    else
    {
        h_cint_t a = h_cint_compare(lhs, rhs);
        if (a)
        {
            cint_erase(q);
            if (a > 0)
            {
                h_cint_t *l = lhs->end, *k, *qq = q->mem + (lhs->end - lhs->mem);
                for (; --qq, --l >= lhs->mem;)
                    for (a = cint_base; a >>= 1;)
                    {
                        for (k = r->end; --k >= r->mem; *(k + 1) |= (*k <<= 1) >> cint_exponent, *k &= cint_mask)
                            ;
                        *r->mem += (a & *l) != 0, r->end += *r->end != 0;
                        h_cint_compare(r, rhs) >= 0 ? h_cint_subi(r, rhs), *qq |= a : 0;
                    }
                q->end += (lhs->end - lhs->mem) - (rhs->end - rhs->mem), q->end += *q->end != 0;
                q->nat = rhs->nat * lhs->nat, (r->end == r->mem) || (r->nat = lhs->nat); // lhs = q * rhs + r
            }
            else
                cint_dup(r, lhs);
        }
        else
            cint_reinit(q, rhs->nat * lhs->nat);
    }
}

static void h_cint_div_approx(const cint *lhs, const cint *rhs, cint *res)
{
    // the division approximation algorithm (answer isn't always exact)
    h_cint_t x, bits = h_cint_compare(lhs, rhs), *o = rhs->end, *p;
    if (bits == 0)
        cint_erase(res), *res->end++ = 1, res->nat = lhs->nat * rhs->nat;
    else if (bits < 0)
        cint_erase(res);
    else
    {
        cint_dup(res, lhs);
        res->nat *= rhs->nat;
        x = *--o, --o < rhs->mem || (x = x << cint_exponent | *o);
        for (bits = 0; cint_mask < x; x >>= 1, ++bits)
            ;
        cint_right_shifti(res, (rhs->end - rhs->mem - 1) * cint_exponent + (bits > 0) * (bits - cint_exponent));
        p = res->end - 3 > res->mem ? res->end - 3 : res->mem;
        for (o = res->end; --o > p; *(o - 1) += (*o % x) << cint_exponent, *o /= x)
            ;
        *o /= x;
        res->end -= *(res->end - 1) == 0;
    }
}

static void cint_div(cint_sheet *sheet, const cint *lhs, const cint *rhs, cint *q, cint *r)
{
    // The combined division algorithm, it uses the approximation algorithm, "fast" with small inputs.
    assert(rhs->mem != rhs->end);
    cint_erase(q);
    const int cmp = h_cint_compare(lhs, rhs);
    if (cmp < 0)
        cint_dup(r, lhs);
    else if (cmp)
    {
        if (lhs->end < lhs->mem + 3 && rhs->end < rhs->mem + 3)
        {
            // System native division.
            cint_erase(r);
            const h_cint_t a = *lhs->mem | *(lhs->mem + 1) << cint_exponent, b = *rhs->mem | *(rhs->mem + 1) << cint_exponent;
            *q->mem = a / b, *r->mem = a % b;
            if (*q->mem & ~cint_mask)
            {
                *++q->end = *q->mem >> cint_exponent, *q->mem &= cint_mask;
            }
            q->end += *q->end != 0;
            if (*r->mem & ~cint_mask)
            {
                *++r->end = *r->mem >> cint_exponent, *r->mem &= cint_mask;
            }
            r->end += *r->end != 0;
        }
        else if (rhs->end == rhs->mem + 1)
        {
            // Special cased "divide by a single word".
            h_cint_t i;
            cint_erase(r);
            q->end = q->mem + (i = lhs->end - lhs->mem - 1);
            if (lhs->mem[i] < *rhs->mem)
                *r->mem = lhs->mem[i--];
            for (; i >= 0;)
            {
                const h_cint_t tmp = (*r->mem << cint_exponent) | lhs->mem[i];
                q->mem[i--] = tmp / *rhs->mem;
                *r->mem = tmp % *rhs->mem;
            }
            q->end += *q->end != 0;
            r->end += *r->end != 0;
        }
        else
        {
            // Regular division for larger numbers.
            cint *a = h_cint_tmp(sheet, 0, lhs), *b = h_cint_tmp(sheet, 1, lhs);
            cint_dup(r, lhs);
            for (; h_cint_div_approx(r, rhs, b), b->mem != b->end;)
                cint_addi(q, b), cint_mul(b, rhs, a), h_cint_subi(r, a);
            if (r->end != r->mem && r->nat != lhs->nat) // lhs = q * rhs + r
                cint_reinit(b, q->nat), h_cint_subi(q, b), h_cint_subi(r, rhs);
        }
    }
    else
        cint_erase(r), *q->end++ = 1;
    if (lhs->nat != rhs->nat) // Signs
        q->nat = q->mem == q->end ? 1 : -1, r->nat = r->mem == r->end ? 1 : lhs->nat;
}

__attribute__((unused)) static inline void cint_mul_mod(cint_sheet *sheet, const cint *lhs, const cint *rhs, const cint *mod, cint *res)
{
    cint *a = h_cint_tmp(sheet, 2, res), *b = h_cint_tmp(sheet, 3, res);
    cint_mul(lhs, rhs, a);
    cint_div(sheet, a, mod, b, res);
}

static inline void cint_mul_modi(cint_sheet *sheet, cint *lhs, const cint *rhs, const cint *mod)
{
    cint *a = h_cint_tmp(sheet, 2, lhs), *b = h_cint_tmp(sheet, 3, lhs);
    cint_mul(lhs, rhs, a);
    cint_div(sheet, a, mod, b, lhs);
}

static inline void cint_pow_modi(cint_sheet *sheet, cint *n, const cint *exp, const cint *mod)
{
    // same as "power" algorithm, difference is that it take the modulo as soon as possible.
    if (n->mem != n->end)
    {
        size_t bits = cint_count_bits(exp);
        switch (bits)
        {
        case 0:
            cint_reinit(n, n->mem != n->end);
            break;
        case 1:
            break;
        default:;
            cint *a = h_cint_tmp(sheet, 2, n);
            cint *b = h_cint_tmp(sheet, 3, n);
            cint *c = h_cint_tmp(sheet, 4, n);
            cint_erase(a), *a->end++ = 1;
            h_cint_t mask = 1;
            for (const h_cint_t *ptr = exp->mem;;)
            {
                if (*ptr & mask)
                    cint_mul(a, n, b), cint_div(sheet, b, mod, c, a);
                if (--bits)
                {
                    cint_mul(n, n, b), cint_div(sheet, b, mod, c, n);
                    mask <<= 1;
                    if (mask == cint_base)
                        mask = 1, ++ptr;
                }
                else
                    break;
            }
            cint_dup(n, a);
        }
    }
}

__attribute__((unused)) static void cint_pow_mod(cint_sheet *sheet, const cint *n, const cint *exp, const cint *mod, cint *res)
{
    cint_dup(res, n);
    cint_pow_modi(sheet, res, exp, mod);
}

static void cint_gcd(cint_sheet *sheet, const cint *lhs, const cint *rhs, cint *gcd)
{
    // the basic GCD algorithm, by frontal divisions.
    if (rhs->mem == rhs->end)
        cint_dup(gcd, lhs), gcd->nat = 1;
    else
    {
        cint *A = h_cint_tmp(sheet, 2, lhs),
             *B = h_cint_tmp(sheet, 3, lhs),
             *C = h_cint_tmp(sheet, 4, lhs),
             *TMP, *RES = gcd;
        cint_dup(gcd, lhs);
        cint_dup(A, rhs);
        gcd->nat = A->nat = 1;
        for (; A->mem != A->end;)
        {
            cint_div(sheet, gcd, A, B, C);
            TMP = gcd, gcd = A, A = C, C = TMP;
        }
        gcd->nat = 1;
        if (RES != gcd)
            cint_dup(RES, gcd);
    }
}

__attribute__((unused)) static void cint_binary_gcd(cint_sheet *sheet, const cint *lhs, const cint *rhs, cint *gcd)
{
    // a binary GCD algorithm.
    if (lhs->mem == lhs->end)
        cint_dup(gcd, rhs);
    else if (rhs->mem == rhs->end)
        cint_dup(gcd, lhs);
    else
    {
        cint *tmp = h_cint_tmp(sheet, 0, lhs),
             *swap, *res = gcd;
        cint_dup(gcd, lhs), gcd->nat = 1;
        cint_dup(tmp, rhs), tmp->nat = 1;
        const size_t a = cint_count_zeros(lhs), b = cint_count_zeros(rhs);
        for (size_t c = a > b ? b : a;; cint_right_shifti(tmp, cint_count_zeros(tmp)))
        {
            if (h_cint_compare(gcd, tmp) > 0)
                swap = gcd, gcd = tmp, tmp = swap;
            h_cint_subi(tmp, gcd);
            if (tmp->mem == tmp->end)
            {
                if (res != gcd)
                    cint_dup(res, gcd);
                cint_left_shifti(res, c);
                break;
            }
        }
    }
}

static unsigned cint_remove(cint_sheet *sheet, cint *N, const cint *F)
{
    // remove all occurrences of the factor from the input, and return the count.
    size_t res = 0;
    if (N->end != N->mem && F->end != F->mem)
        switch ((*N->mem == 1 && N->end == N->mem + 1) | (*F->mem == 1 && F->end == F->mem + 1) << 1)
        {
        case 1:
            break; // it asks remove other than [-1, 1] but N is [-1, 1].
        case 2:    // it asks remove [-1, 1], so remove one occurrence if N != 0.
        case 3:
            res = N->mem != N->end;
            if (res)
                N->nat *= F->nat;
            break;
        default:;
            cint *A = h_cint_tmp(sheet, 2, N), *B = h_cint_tmp(sheet, 3, N);
            // divides N by the factor until there is a remainder
            for (cint *tmp; cint_div(sheet, N, F, A, B), B->mem == B->end; tmp = N, N = A, A = tmp, ++res)
                ;
            if (res & 1)
                cint_dup(A, N);
        }
    return res;
}

static void cint_sqrt(cint_sheet *sheet, const cint *num, cint *res, cint *rem)
{
    // original square root algorithm.
    cint_erase(res), cint_dup(rem, num); // answer ** 2 + rem = num
    if (num->nat > 0 && num->end != num->mem)
    {
        cint *a = h_cint_tmp(sheet, 0, num), *b = h_cint_tmp(sheet, 1, num);
        cint_erase(a), *a->end++ = 1;
        cint_left_shifti(a, cint_count_bits(num) & ~1);
        for (; a->mem != a->end;)
        {
            cint_dup(b, res);
            h_cint_addi(b, a);
            cint_right_shifti(res, 1);
            if (h_cint_compare(rem, b) >= 0)
                h_cint_subi(rem, b), h_cint_addi(res, a);
            cint_right_shifti(a, 2);
        }
    }
}

static void cint_cbrt(cint_sheet *sheet, const cint *num, cint *res, cint *rem)
{
    // original cube root algorithm.
    cint_erase(res), cint_dup(rem, num); // answer ** 3 + rem = num
    if (num->mem != num->end)
    {
        cint *a = h_cint_tmp(sheet, 0, num), *b = h_cint_tmp(sheet, 1, num);
        for (size_t c = cint_count_bits(num) / 3 * 3; c < -1U; c -= 3)
        {
            cint_left_shifti(res, 1);
            cint_dup(a, res);
            cint_left_shifti(a, 1);
            h_cint_addi(a, res);
            cint_mul(a, res, b);
            ++*b->mem; // "b" isn't "normalized", it should work for an addition.
            h_cint_addi(b, a);
            cint_dup(a, rem);
            cint_right_shifti(a, c);
            if (h_cint_compare(a, b) >= 0)
                cint_left_shifti(b, c), h_cint_subi(rem, b), cint_erase(b), *b->end++ = 1, h_cint_addi(res, b);
        }
        res->nat = num->nat;
    }
}

static void cint_nth_root(cint_sheet *sheet, const cint *num, const unsigned nth, cint *res)
{
    // original nth-root algorithm, it does not try to decompose "nth" into prime factors.
    switch (nth)
    {
    case 0:
        cint_reinit(res, num->end == num->mem + 1 && *num->mem == 1);
        break;
    case 1:
        cint_dup(res, num);
        break;
    case 2:
        cint_sqrt(sheet, num, res, h_cint_tmp(sheet, 2, num));
        break;
    case 3:
        cint_cbrt(sheet, num, res, h_cint_tmp(sheet, 2, num));
        break;
    default:
        if (num->end > num->mem + 1 || *num->mem > 1)
        {
            cint *a = h_cint_tmp(sheet, 2, num),
                 *b = h_cint_tmp(sheet, 3, num),
                 *c = h_cint_tmp(sheet, 4, num),
                 *d = h_cint_tmp(sheet, 5, num),
                 *e = h_cint_tmp(sheet, 6, num), *r = res, *tmp;
            cint_erase(a), *a->end++ = 1, cint_erase(d), *d->end++ = 1;
            cint_left_shifti(a, (cint_count_bits(num) + nth - 1) / nth);
            h_cint_addi(r, d), cint_reinit(d, nth - 1), cint_reinit(e, nth);
            do
            {
                tmp = a, a = r, r = tmp, cint_dup(a, num);
                for (unsigned count = nth; --count && (cint_div(sheet, a, r, b, c), tmp = a, a = b, b = tmp, a->mem != a->end);)
                    ;
                cint_mul(r, d, b);
                h_cint_addi(b, a);
                cint_div(sheet, b, e, a, c);
            } while (h_cint_compare(a, r) < 0);
            r == res ? (void)0 : cint_dup(res, tmp == a ? a : r);
            res->nat = nth & 1 ? num->nat : 1;
        }
        else
            cint_dup(res, num);
    }
}

static void cint_nth_root_remainder(cint_sheet *sheet, const cint *num, const unsigned nth, cint *res, cint *rem)
{
    // nth-root algorithm don't provide the remainder, so here it computes the remainder.
    if (nth == 2)
        cint_sqrt(sheet, num, res, rem);
    else if (nth == 3)
        cint_cbrt(sheet, num, res, rem);
    else
    {
        cint_nth_root(sheet, num, nth, res);
        cint *a = h_cint_tmp(sheet, 2, num);
        cint_reinit(a, nth);
        cint_pow(sheet, res, a, rem);
        cint_subi(rem, num);
    }
}

static void cint_random_bits(cint *num, size_t bits)
{
    // provide a random number with exactly the number of bits asked.
    // Normally no one bit more, no one less.
    int i = 0;
    cint_erase(num);
    for (; bits; ++num->end)
        for (i = 0; bits && i < cint_exponent; ++i, --bits)
            *num->end = *num->end << 1 | (rand() & 1);
    if (i)
        *(num->end - 1) |= 1 << (i - 1);
}

static void cint_modular_inverse(cint_sheet *sheet, const cint *lhs, const cint *rhs, cint *res)
{
    // original modular inverse algorithm, answer is also called "u1" in extended Euclidean algorithm context.
    if (*rhs->mem > 1 || rhs->end > rhs->mem + 1)
    {
        cint *a = h_cint_tmp(sheet, 2, rhs),
             *b = h_cint_tmp(sheet, 3, rhs),
             *c = h_cint_tmp(sheet, 4, rhs),
             *d = h_cint_tmp(sheet, 5, rhs),
             *e = h_cint_tmp(sheet, 6, rhs),
             *f = h_cint_tmp(sheet, 7, rhs), *tmp, *out = res;
        cint_dup(a, lhs), cint_dup(b, rhs), cint_erase(res), *res->end++ = 1, cint_erase(e);
        a->nat = b->nat = 1;
        int i = 0;
        do
        {
            cint_div(sheet, a, b, c, d);
            cint_mul(c, e, f);
            cint_dup(c, res);
            cint_subi(c, f);
            tmp = a, a = b, b = d, d = tmp;
            tmp = res, res = e, e = c, c = tmp;
        } while (++i, (d->mem == d->end) == (b->mem == b->end));
        if (a->end == a->mem + 1 && *a->mem == 1)
        {
            if (i & 1)
                cint_addi(res, e);
        }
        else
            cint_erase(res);
        if (out != res)
            cint_dup(out, res);
    }
    else
        cint_erase(res);
}

int cint_is_prime(cint_sheet *sheet, const cint *N, int iterations)
{
    // is N is considered as a prime number ? the function returns 0 or 1.
    // if the number of Miller-Rabin iterations is negative, the function decides for the caller.
    int res;
    if (*N->mem < 961 && N->mem + 1 >= N->end)
    {
        int n = (int)*N->mem; // Small numbers for which Miller-Rabin is not used.
        res = (n > 1) & ((n < 6) * 42 + 0x208A2882) >> n % 30 && (n < 49 || (n % 7 && n % 11 && n % 13 && n % 17 && n % 19 && n % 23 && n % 29));
    }
    else if (res = (*N->mem & 1) != 0, res && iterations)
    {
        cint *A = h_cint_tmp(sheet, 5, N),
             *B = h_cint_tmp(sheet, 6, N),
             *C = h_cint_tmp(sheet, 7, N);
        size_t a, b, bits = cint_count_bits(N), rand_mod = bits - 3;
        if (iterations < 0) // decides for the caller ... 16 ... 8 ... 4 ... 2 ...
            iterations = 2 << ((bits < 128) + (bits < 256) + (bits < 1024));
        cint_dup(A, N);
        cint_erase(B), *B->end++ = 1;
        cint_subi(A, B);
        cint_dup(C, A); // C = (N - 1)
        a = cint_count_zeros(C);
        cint_right_shifti(C, a); // divides C by 2 until C is odd
        for (bits = 2; iterations-- && res;)
        {
            cint_random_bits(B, bits); // take any appropriate number
            bits = 3 + *B->mem % rand_mod;
            cint_pow_modi(sheet, B, C, N); // raise to the power C mod N
            if (*B->mem != 1 || B->end != B->mem + 1)
            {
                for (b = a; b-- && (res = h_cint_compare(A, B));)
                    cint_mul_modi(sheet, B, B, N);
                res = !res;
            } // only a prime number can hold (res = 1) forever
        }
    }
    return res;
}

#endif

#ifndef FAC_HEADERS
#define FAC_HEADERS

#include <errno.h>
#include <stddef.h>

typedef uint32_t qs_sm; // small size, like a factor base prime number (32-bit)
typedef uint64_t qs_md; // medium size, like a factor base prime number squared (64-bit)
typedef int64_t qs_tmp; // signed type to perform intermediates computations.

typedef struct
{
    cint cint;
    int power;
    int prime;
    int bits;
} fac_cint;

typedef struct
{
    unsigned testing;
    unsigned silent;
    unsigned help;
    unsigned qs_limit;
    unsigned qs_multiplier;
    unsigned qs_rand_seed;
} fac_params;

typedef struct
{

    struct
    {
        void *base;
        void *now;
    } mem;

    fac_params *params;

    struct
    {
        cint cint;
        qs_sm done_up_to;
    } trial;

    fac_cint *number; // the number to factor

    cint vars[10];
    cint_sheet *calc;

    struct
    {
        fac_cint *data;
        unsigned index;
    } questions;

    struct
    {
        fac_cint *data;
        unsigned index;
    } answers;

} fac_caller;

// Quadratic sieve structures

struct qs_relation
{
    qs_sm id; // definitive relations have a non-zero id.
    cint *X;
    struct
    {
        qs_sm *data;
        qs_sm length;
    } Y;
    union
    {
        struct
        {
            qs_sm *data;
            qs_sm length;
        } Z;
        struct qs_relation *next;
    } axis;
    // axis :
    // - "Z" field is used by definitive relations.
    // - "next" is used by data that wait to be paired, it uses a linked list instead of a "Z" field.
};

typedef struct
{

    // reference to the caller
    fac_caller *caller;

    // computation sheet
    cint_sheet *calc;

    // numbers that are updated
    struct
    {
        cint N;
        cint FACTOR;
        cint X;
        cint KEY;
        cint VALUE;
        cint CYCLE;
        cint TEMP[5];
        cint MY[5]; // available for developers, never used
    } vars;

    // polynomial vars
    struct
    {
        cint A;
        cint B;
        cint C;
        cint D;
        qs_sm d_bits;
        qs_sm offset;
        qs_sm min;
        qs_sm span;
        qs_sm span_half;
        qs_sm gray_max;
        qs_sm curves;
    } poly;

    // constants
    struct
    {
        cint kN;
        cint ONE;
        cint LARGE_PRIME;
        cint MULTIPLIER;
        cint M_HALF;
    } constants;

    // system
    struct
    {
        qs_sm bytes_allocated;
        void *base;
        void *now;
    } mem;

    // parameters and miscellaneous vars
    qs_md adjustor;
    qs_sm multiplier;
    qs_sm n_bits;
    qs_sm kn_bits;
    struct
    {
        uint8_t **positions[2];
        uint8_t *sieve;
        uint8_t *flags;
        qs_sm length;
        qs_sm length_half;
        qs_sm cache_size;
    } m;
    qs_sm iterative_list[5];
    qs_sm error_bits;
    struct
    {
        qs_sm value;
    } threshold;
    unsigned rand_seed;
    qs_sm sieve_again_perms;

    // useful data sharing same length
    struct
    {
        struct
        {
            qs_sm num;
            qs_sm size;
            qs_sm sqrt_kN_mod_prime;
            qs_sm root[2];
        } *data;
        qs_sm length;
    } base;

    // useful data sharing same length
    struct
    {
        qs_sm *A_indexes;
        struct
        {
            cint B_terms;
            qs_sm *A_inv_double_value_B_terms;
            qs_sm A_over_prime_mod_prime;
            qs_sm prime_index;
            qs_md prime_squared;
        } *data;
        struct
        {
            qs_sm defined;
            qs_sm subtract_one;
            qs_sm double_value;
        } values;
    } s;

    qs_sm *buffer[2]; // proportional to "length of factor base" (medium or large)

    // uniqueness trees : [ relations, cycle finder, divisors of N, ]
    struct avl_manager uniqueness[3];

    // data collection made by algorithm
    struct
    {
        struct qs_relation **data;
        struct
        {
            qs_sm now;
            qs_sm prev;
            qs_sm needs;
            qs_sm reserved;
        } length;
        qs_md large_prime;
    } relations;

    // pointers to the divisors of N are kept in a flat array
    struct
    {
        qs_sm processing_index;
        qs_sm total_primes;
        qs_sm length;
        cint **data;
    } divisors;

    // lanczos has its own struct
    struct
    {
        qs_sm safe_length;
        struct
        {
            struct qs_relation *relation;
            qs_sm y_length;
        } *snapshot;
    } lanczos;

} qs_sheet;

// Front-End Factor manager
static fac_cint **c_factor(const cint *, fac_params *);
static inline int fac_special_cases(fac_caller *);
static inline int fac_trial_division(fac_caller *, int);
static inline int fac_perfect_checker(fac_caller *);
static inline int fac_primality_checker(fac_caller *);
static inline int fac_pollard_rho_63_bits(fac_caller *);
static void fac_push(fac_caller *, const cint *, int, int, int);

// Math
static inline int is_prime_4669921(qs_sm);
static double log_computation(double);
static inline qs_sm multiplication_modulo(qs_md, qs_md, qs_sm);
static inline qs_sm power_modulo(qs_md, qs_md, qs_sm);
static qs_sm tonelli_shanks(qs_sm, qs_sm);
static qs_sm modular_inverse(qs_sm, qs_sm);
static inline qs_md rand_64();
static inline qs_md rand_upto(qs_md);
static inline unsigned add_rand_seed(void *);

// Cint shortcuts
static inline void simple_inline_cint(cint *, size_t, void **);
static inline void simple_dup_cint(cint *, const cint *, void **);
static inline void simple_int_to_cint(cint *, qs_md);
static inline qs_md simple_cint_to_int(const cint *);

// Avl;
static inline struct avl_node *avl_cint_inserter(void *, const void *);

// System
static inline void *mem_aligned(void *);

// Misc.
static inline int fac_apply_custom_param(const char *, const char *, int, unsigned *);
static inline char *fac_fill_params(fac_params *, int, char **);
static char *fac_answer_to_string(fac_cint **);
static inline void fac_display_progress(const char *, double);
static inline int fac_sort_result(const void *, const void *);

// Quadratic sieve functions
static inline qs_sm linear_param_resolution(const double[][2], qs_sm);
static inline void qs_parametrize(qs_sheet *);
static int quadratic_sieve(fac_caller *);
static inline int inner_continuation_condition(qs_sheet *);
static inline int outer_continuation_condition(qs_sheet *);
static inline void preparation_part_1(qs_sheet *, fac_caller *);
static inline void preparation_part_2(qs_sheet *);
//
static inline void preparation_part_3(qs_sheet *);
static inline qs_sm preparation_part_3_michel(qs_sheet *qs);
//
static inline void preparation_part_4(qs_sheet *);
static inline void preparation_part_5(qs_sheet *);
static inline void preparation_part_6(qs_sheet *);
static inline void get_started_iteration(qs_sheet *);
static inline void iteration_part_1(qs_sheet *, const cint *, cint *);
static inline void iteration_part_2(qs_sheet *, const cint *, cint *);
static inline void iteration_part_3(qs_sheet *, const cint *, const cint *);
static inline qs_sm iteration_part_4(const qs_sheet *, qs_sm nth_curve, qs_sm **, cint *);
static inline void iteration_part_5(qs_sheet *, const cint *, const cint *);
static inline void iteration_part_6(qs_sheet *, const cint *, const cint *, const cint *, cint *);
static inline void iteration_part_7(qs_sheet *, qs_sm, const qs_sm *);
static inline void iteration_part_8(qs_sheet *, qs_sm, const qs_sm *);
static int qs_register_factor(qs_sheet *);
static inline void register_relations(qs_sheet *, const cint *, const cint *, const cint *);
static inline void register_relation_kind_1(qs_sheet *, const cint *, const qs_sm *const restrict[4]);
static inline void register_relation_kind_2(qs_sheet *, const cint *, const cint *, const qs_sm *const restrict[4]);
static inline void finalization_part_1(qs_sheet *, const uint64_t *);
static inline void finalization_part_2(qs_sheet *);
static inline int finalization_part_3(qs_sheet *);

// Quadratic sieve Lanczos part
static inline void lanczos_mul_MxN_Nx64(const qs_sheet *, const uint64_t *, qs_sm, uint64_t *);
static inline void lanczos_mul_trans_MxN_Nx64(const qs_sheet *, const uint64_t *, uint64_t *);
static void lanczos_mul_64xN_Nx64(const qs_sheet *, const uint64_t *, const uint64_t *, uint64_t *, uint64_t *);
static uint64_t lanczos_find_non_singular_sub(const uint64_t *, const uint64_t *, uint64_t *, uint64_t, uint64_t *);
static void lanczos_mul_Nx64_64x64_acc(qs_sheet *, const uint64_t *, const uint64_t *, uint64_t *, uint64_t *);
static void lanczos_mul_64x64_64x64(const uint64_t *, const uint64_t *, uint64_t *);
static void lanczos_transpose_vector(qs_sheet *, const uint64_t *, uint64_t **);
static void lanczos_combine_cols(qs_sheet *, uint64_t *, uint64_t *, uint64_t *, uint64_t *);
static inline void lanczos_build_array(qs_sheet *, uint64_t **, size_t, size_t);
static inline uint64_t *lanczos_block_worker(qs_sheet *);
static inline uint64_t *lanczos_block(qs_sheet *);

#endif // FAC_HEADERS

// Front-End Factor manager
fac_cint **c_factor(const cint *N, fac_params *config)
{
    void *mem;
    fac_caller m = {0};
    const int input_bits = (int)cint_count_bits(N);
    int alloc_bits = (1 + (input_bits >> 9)) << 14;
    // initially allocates 16 Kb for each 512-bit chunk.
    mem = m.mem.base = calloc(1, alloc_bits);
    assert(mem);
    add_rand_seed(&mem);
    if (config)
        m.params = config;
    else
        m.params = mem, mem = m.params + 1;
    m.calc = cint_new_sheet((1 + (input_bits >> 10)) << 10);
    assert(m.calc);

    // prepare some vars.
    const size_t vars_size = 500 * (1 + input_bits / 500) / cint_exponent;
    for (size_t i = 0; i < sizeof(m.vars) / sizeof(*m.vars); ++i)
        simple_inline_cint(&m.vars[i], vars_size, &mem);

    simple_inline_cint(&m.trial.cint, vars_size, &mem);

    // prepare a working array.
    const int max_factors = input_bits / 10 + 32;
    m.questions.data = mem, mem = m.questions.data + max_factors;
    m.answers.data = mem, mem = m.answers.data + max_factors;

    m.number = &m.questions.data[m.questions.index++];
    simple_dup_cint(&m.number->cint, N, &mem);
    m.number->bits = input_bits;
    m.number->power = 1, m.number->prime = -1;

    m.mem.now = mem;
    // iterates the array until it's empty, begin with the input N.
    // functions must not push their input to the stack, they return 0 instead.
    do
    {
        m.number = &m.questions.data[--m.questions.index];
        int res = fac_special_cases(&m) || fac_trial_division(&m, 1) || fac_perfect_checker(&m) || fac_primality_checker(&m) || fac_pollard_rho_63_bits(&m)
                  // Quadratic sieve can assume N is 63+ bits,
                  // isn't easily divisible, isn't a perfect power.
                  || quadratic_sieve(&m) || fac_trial_division(&m, 2);
        if (res == 0)
            fac_push(&m, &m.number->cint, 0, 1, 0);
    } while (m.questions.index);

    // answer goes into an appropriately sized memory allocation.
    size_t bytes = 0;
    for (unsigned i = 0; i < m.answers.index; ++i)
        bytes += m.answers.data[i].cint.end - m.answers.data[i].cint.mem + 1;
    bytes *= sizeof(h_cint_t);
    bytes += (sizeof(fac_cint) + sizeof(fac_cint *)) * (m.answers.index + 1);
    fac_cint **res = mem = calloc(1, bytes);
    assert(mem);

    qsort(m.answers.data, m.answers.index, sizeof(fac_cint), &fac_sort_result);

    mem = res + m.answers.index + 1;
    for (unsigned i = 0; i < m.answers.index; ++i)
    {
        fac_cint *factor = &m.answers.data[i];
        res[i] = mem, mem = res[i] + 1;
        res[i]->power = factor->power;
        res[i]->prime = factor->prime;
        res[i]->bits = (int)cint_count_bits(&factor->cint);
        simple_inline_cint(&res[i]->cint, factor->cint.size, &mem);
        cint_dup(&res[i]->cint, &factor->cint);
    }
    free(m.mem.base);
    cint_clear_sheet(m.calc);
    return res;
}

int fac_special_cases(fac_caller *m)
{
    int res = m->number->bits < 3;
    if (res && m->answers.index == 0)
    {
        const int prime = m->number->bits > 1;
        fac_push(m, &m->number->cint, prime, 1, 0);
    }
    return res;
}

int fac_trial_division(fac_caller *m, const int level)
{
    cint *F = m->vars;
    int res = (*m->number->cint.mem & 1) == 0; // remove power of 2.
    if (m->trial.done_up_to == 0)
    {
        if (res)
        {
            simple_int_to_cint(F, 2);
            const int power = (int)cint_count_zeros(&m->number->cint);
            fac_push(m, F, 1, power, 0);
            cint_right_shifti(&m->number->cint, power);
        }
        m->trial.done_up_to = 1;
    }

    qs_sm bound;
    if (m->number->bits < 64)
        bound = 1024;
    else if (bound = 4650000, level == 1)
        for (int i = 0; i < 250; bound >>= (m->number->bits < i), i += 30)
            ;

    for (; (m->trial.done_up_to += 2) < bound;)
    {
        if (is_prime_4669921(m->trial.done_up_to))
        {
            simple_int_to_cint(F, m->trial.done_up_to);
            const unsigned power = cint_remove(m->calc, &m->number->cint, F);
            if (power)
            {
                fac_push(m, F, 1, (int)power, 0);
                ++res;
            }
        }
    }
    simple_int_to_cint(&m->trial.cint, m->trial.done_up_to);
    if (res)
        fac_push(m, &m->number->cint, -1, 1, 1);
    return res;
}

int fac_any_root_check(fac_caller *m, const cint *N, cint *ROOT, cint *REM)
{
    // Can normally say if a number is a perfect power, it takes in account the trial divisions initially done.
    // Indicates the lowest root found, not the highest, functions can call recursively if they are not "satisfied".
    int res = 0;
    const int max_root = 30;
    for (int nth = 2; nth < max_root; ++nth)
        if (is_prime_4669921(nth))
        {
            cint_nth_root_remainder(m->calc, N, nth, ROOT, REM);
            if (REM->mem == REM->end)
            {
                res = nth;
                break;
            }
            if (h_cint_compare(ROOT, &m->trial.cint) <= 0)
                break;
        }
    return res;
}

int fac_perfect_checker(fac_caller *m)
{
    assert(m->number->bits > 2);
    cint *Q = m->vars, *R = Q + 1;
    int power = fac_any_root_check(m, &m->number->cint, Q, R);
    if (power)
        fac_push(m, Q, -1, power, 1);
    return power;
}

int fac_primality_checker(fac_caller *m)
{
    m->number->prime = cint_is_prime(m->calc, &m->number->cint, m->number->bits > 2048 ? 1 : -1);
    if (m->number->prime)
        fac_push(m, &m->number->cint, 1, 1, 0);
    return m->number->prime;
}

int fac_pollard_rho_63_bits(fac_caller *m)
{
    int res = m->number->bits > 0 && m->number->bits < 64;
    if (res)
    {
        // Perform a Pollard's Rho test, this function can't complete with a prime number.
        qs_md n[2] = {
            simple_cint_to_int(&m->number->cint),
            1,
        }; // number and its factor.
        for (size_t limit = 7; n[1] == 1 || n[0] == n[1]; ++limit)
        {
            if (m->params->silent == 0)
                ; // fac_display_progress("Pollard Rho", 100. * (double) limit / 21);
            size_t a = -1, b = 2, c = limit;
            qs_md d, e = rand(), f = 1;
            for (n[1] = 1, d = e %= n[0]; n[1] == 1 && --c; e = d, b <<= 1, a = -1)
            {
                for (; n[1] |= f, n[1] == 1 && ++a != b;)
                {
                    qs_md lhs = d % n[0], rhs = lhs, tmp;
                    for (d = 0; lhs; lhs & 1 ? rhs >= n[0] - d ? d -= n[0] : 0, d += rhs : 0, lhs >>= 1, (tmp = rhs) >= n[0] - rhs ? tmp -= n[0] : 0, rhs += tmp)
                        ;
                    for (d %= n[0], ++d, d *= d != n[0], f = n[0], n[1] = d > e ? d - e : e - d; (n[1] %= f) && (f %= n[1]);)
                        ;
                }
            }
        }
        n[0] /= n[1];
        cint *F = m->vars;
        for (int i = 0; i < 2; ++i)
        {
            simple_int_to_cint(F, n[i]);
            fac_push(m, F, -1, 1, 1);
        }
    }
    return res;
}

// functions submit factors of N, they don't push N itself with "forward" (otherwise there is an infinite loop).
void fac_push(fac_caller *m, const cint *num, const int prime, const int power, const int forward)
{
    // the product of "stack last" and "stack next" must remain N.
    fac_cint *row;
    if (forward)
    {
        row = &m->questions.data[m->questions.index++];
        const size_t needed_size = num->end - num->mem + 1;
        if (row->cint.size < needed_size)
            simple_inline_cint(&row->cint, needed_size, &m->mem.now);
        row->bits = (int)cint_count_bits(num);
    }
    else
    {
        row = &m->answers.data[m->answers.index++];
        simple_inline_cint(&row->cint, num->end - num->mem + 1, &m->mem.now);
    }
    cint_dup(&row->cint, num);
    row->prime = prime;
    row->power = power * m->number->power;
    assert(row->power);
}

// Math
int is_prime_4669921(const qs_sm n)
{
    // Used to iterate over primes, there are 326,983 prime numbers under 4,669,921, very fast.
    return ((n > 1) & ((n < 6) * 42 + 0x208A2882) >> n % 30 && (n < 49 || (n % 7 && n % 11 && n % 13 && n % 17 && n % 19 && n % 23 && n % 29 && (n < 961 || (n % 31 && n % 37 && n % 41 && n % 43 && n % 47 && n % 53 && n % 59 && n % 61 && n % 67 && (n < 5041 || (n % 71 && n % 73 && n % 79 && n % 83 && n % 89 && n % 97 && n % 101 && n % 103 && n % 107 && (n < 11881 || (n % 109 && n % 113 && n % 127 && n % 131 && n % 137 && n % 139 && n % 149 && n % 151 && n % 157 && (n < 26569 || (n % 163 && n % 167 && n % 173 && n % 179 && n % 181 && n % 191 && n % 193 && n % 197 && n % 199 && (n < 44521 || (n % 211 && n % 223 && n % 227 && n % 229 && n % 233 && n % 239 && n % 241 && n % 251 && n % 257 && (n < 69169 || (n % 263 && n % 269 && n % 271 && n % 277 && n % 281 && n % 283 && n % 293 && n % 307 && n % 311 && (n < 97969 || (n % 313 && n % 317 && n % 331 && n % 337 && n % 347 && n % 349 && n % 353 && n % 359 && n % 367 && (n < 139129 || (n % 373 && n % 379 && n % 383 && n % 389 && n % 397 && n % 401 && n % 409 && n % 419 && n % 421 && (n < 185761 || (n % 431 && n % 433 && n % 439 && n % 443 && n % 449 && n % 457 && n % 461 && n % 463 && n % 467 && (n < 229441 || (n % 479 && n % 487 && n % 491 && n % 499 && n % 503 && n % 509 && n % 521 && n % 523 && n % 541 && (n < 299209 || (n % 547 && n % 557 && n % 563 && n % 569 && n % 571 && n % 577 && n % 587 && n % 593 && n % 599 && (n < 361201 || (n % 601 && n % 607 && n % 613 && n % 617 && n % 619 && n % 631 && n % 641 && n % 643 && n % 647 && (n < 426409 || (n % 653 && n % 659 && n % 661 && n % 673 && n % 677 && n % 683 && n % 691 && n % 701 && n % 709 && (n < 516961 || (n % 719 && n % 727 && n % 733 && n % 739 && n % 743 && n % 751 && n % 757 && n % 761 && n % 769 && (n < 597529 || (n % 773 && n % 787 && n % 797 && n % 809 && n % 811 && n % 821 && n % 823 && n % 827 && n % 829 && (n < 703921 || (n % 839 && n % 853 && n % 857 && n % 859 && n % 863 && n % 877 && n % 881 && n % 883 && n % 887 && (n < 822649 || (n % 907 && n % 911 && n % 919 && n % 929 && n % 937 && n % 941 && n % 947 && n % 953 && n % 967 && (n < 942841 || (n % 971 && n % 977 && n % 983 && n % 991 && n % 997 && n % 1009 && n % 1013 && n % 1019 && n % 1021 && (n < 1062961 || (n % 1031 && n % 1033 && n % 1039 && n % 1049 && n % 1051 && n % 1061 && n % 1063 && n % 1069 && n % 1087 && (n < 1190281 || (n % 1091 && n % 1093 && n % 1097 && n % 1103 && n % 1109 && n % 1117 && n % 1123 && n % 1129 && n % 1151 && (n < 1329409 || (n % 1153 && n % 1163 && n % 1171 && n % 1181 && n % 1187 && n % 1193 && n % 1201 && n % 1213 && n % 1217 && (n < 1495729 || (n % 1223 && n % 1229 && n % 1231 && n % 1237 && n % 1249 && n % 1259 && n % 1277 && n % 1279 && n % 1283 && (n < 1661521 || (n % 1289 && n % 1291 && n % 1297 && n % 1301 && n % 1303 && n % 1307 && n % 1319 && n % 1321 && n % 1327 && (n < 1852321 || (n % 1361 && n % 1367 && n % 1373 && n % 1381 && n % 1399 && n % 1409 && n % 1423 && n % 1427 && n % 1429 && (n < 2053489 || (n % 1433 && n % 1439 && n % 1447 && n % 1451 && n % 1453 && n % 1459 && n % 1471 && n % 1481 && n % 1483 && (n < 2211169 || (n % 1487 && n % 1489 && n % 1493 && n % 1499 && n % 1511 && n % 1523 && n % 1531 && n % 1543 && n % 1549 && (n < 2411809 || (n % 1553 && n % 1559 && n % 1567 && n % 1571 && n % 1579 && n % 1583 && n % 1597 && n % 1601 && n % 1607 && (n < 2588881 || (n % 1609 && n % 1613 && n % 1619 && n % 1621 && n % 1627 && n % 1637 && n % 1657 && n % 1663 && n % 1667 && (n < 2785561 || (n % 1669 && n % 1693 && n % 1697 && n % 1699 && n % 1709 && n % 1721 && n % 1723 && n % 1733 && n % 1741 && (n < 3052009 || (n % 1747 && n % 1753 && n % 1759 && n % 1777 && n % 1783 && n % 1787 && n % 1789 && n % 1801 && n % 1811 && (n < 3323329 || (n % 1823 && n % 1831 && n % 1847 && n % 1861 && n % 1867 && n % 1871 && n % 1873 && n % 1877 && n % 1879 && (n < 3568321 || (n % 1889 && n % 1901 && n % 1907 && n % 1913 && n % 1931 && n % 1933 && n % 1949 && n % 1951 && n % 1973 && (n < 3916441 || (n % 1979 && n % 1987 && n % 1993 && n % 1997 && n % 1999 && n % 2003 && n % 2011 && n % 2017 && n % 2027 && (n < 4116841 || (n % 2029 && n % 2039 && n % 2053 && n % 2063 && n % 2069 && n % 2081 && n % 2083 && n % 2087 && n % 2089 && (n < 4405801 || (n % 2099 && n % 2111 && n % 2113 && n % 2129 && n % 2131 && n % 2137 && n % 2141 && n % 2143 && n % 2153)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
}

double log_computation(const double n)
{
    // Basic logarithm computation, believing you can't include <math.h>.
    static const double euler = 2.7182818284590452354;
    unsigned a = 0, d;
    double b, c, e, f;
    if (n > 0)
    {
        for (c = n < 1 ? 1 / n : n; (c /= euler) > 1; ++a)
            ;
        c = 1 / (c * euler - 1), c = c + c + 1, f = c * c, b = 0;
        for (d = 1, c /= 2; e = b, b += 1 / (d * c), b - e > 0.00001;)
        {
            d += 2, c *= f;
        }
    }
    else
        b = (n == 0) / 0.;
    return n < 1 ? -(a + b) : a + b;
}

qs_sm multiplication_modulo(qs_md a, qs_md b, const qs_sm mod)
{
#ifdef __SIZEOF_INT128__
    return (qs_sm)((__int128_t)a * (__int128_t)b % (__int128_t)mod);
#else
    qs_md res = 0, tmp;
    for (b %= mod; a; a & 1 ? b >= mod - res ? res -= mod : 0, res += b : 0, a >>= 1, (tmp = b) >= mod - b ? tmp -= mod : 0, b += tmp)
        ;
    return (qs_sm)(res % mod);
#endif
}

qs_sm power_modulo(qs_md n, qs_md exp, const qs_sm mod)
{
    // Return (n ^ exp) % mod
    qs_sm res = 1;
    for (n %= mod; exp; exp & 1 ? res = multiplication_modulo(res, n, mod) : 0, n = multiplication_modulo(n, n, mod), exp >>= 1)
        ;
    return res;
}

int kronecker_symbol(qs_sm a, qs_sm b)
{
    static const int s[8] = {0, 1, 0, -1, 0, -1, 0, 1};
    qs_sm c;
    int res = (int)(a | b);
    if (a && b)
        if (res & 1)
        {
            for (c = 0; !(b & 1); ++c, b >>= 1)
                ;
            for (res = c & 1 ? s[a & 7] : 1; a; c & 1 ? res *= s[b & 7] : 0, a &b & 2 ? res = -res : 0, c = b % a, b = a, a = c)
                for (c = 0; !(a & 1); ++c, a >>= 1)
                    ;
            res = b == 1 ? res : 0;
        }
        else
            res = 0;
    else
        res = res == 1;
    return res;
}

qs_sm tonelli_shanks(const qs_sm n, const qs_sm mod)
{
    const qs_sm a = (qs_sm)(n % mod);
    qs_sm res = kronecker_symbol(a, mod) == 1, b, c, d, e, f, g, h;
    if (res)
        switch (mod & 7)
        {
        case 3:
        case 7:
            res = power_modulo(a, (mod + 1) >> 2, mod);
            break;
        case 5:
            res = power_modulo(a, (mod + 3) >> 3, mod);
            if (multiplication_modulo(res, res, mod) != a)
            {
                b = power_modulo(2, (mod - 1) >> 2, mod);
                res = multiplication_modulo(res, b, mod);
            }
            break;
        default:
            if (a == 1)
                res = 1;
            else
            {
                for (c = mod - 1, d = 2; d < mod && power_modulo(d, c >> 1, mod) != c; ++d)
                    ;
                for (e = 0; !(c & 1); ++e, c >>= 1)
                    ;
                f = power_modulo(a, c, mod);
                b = power_modulo(d, c, mod);
                for (h = 0, g = 0; h < e; h++)
                {
                    d = power_modulo(b, g, mod);
                    d = multiplication_modulo(d, f, mod);
                    d = power_modulo(d, 1 << (e - h - 1), mod);
                    if (d == mod - 1)
                        g += 1 << h;
                }
                f = power_modulo(a, (c + 1) >> 1, mod);
                b = power_modulo(b, g >> 1, mod);
                res = multiplication_modulo(f, b, mod);
            }
        }
    return res;
}

qs_sm modular_inverse(qs_sm ra, qs_sm rb)
{
    qs_sm rc, sa = 1, sb = 0, sc, i = 0;
    if (rb > 1)
        do
        {
            rc = ra % rb;
            sc = sa - (ra / rb) * sb;
            sa = sb, sb = sc;
            ra = rb, rb = rc;
        } while (++i, rc);
    sa *= (i *= ra == 1) != 0;
    sa += (i & 1) * sb;
    return sa;
}

qs_md rand_64()
{
    qs_md res = 0;
    for (qs_sm i = 65; --i; res <<= 1, res |= rand() & 1)
        ;
    return res;
}

qs_md rand_upto(const qs_md limit)
{
    return rand_64() % limit;
}

unsigned add_rand_seed(void *addr)
{
    static unsigned seed;
    if (addr)
    {
        seed ^= *(unsigned *)addr + (unsigned)(uintptr_t)&errno;
        seed = power_modulo(seed + 1, seed - 3, -5);
        srand(seed);
    }
    return seed;
}

// Cint shortcuts
void simple_inline_cint(cint *N, const size_t size, void **mem)
{
    N->mem = N->end = (h_cint_t *)*mem;
    *mem = N->mem + (N->size = size);
}

void simple_dup_cint(cint *A, const cint *B, void **mem)
{
    A->mem = A->end = (h_cint_t *)*mem;
    cint_dup(A, B);
    A->size = A->end - A->mem + 1;
    *mem = A->mem + A->size;
}

void simple_int_to_cint(cint *num, qs_md value)
{
    // Pass the given 64-bit number into the given cint (positive only).
    for (cint_erase(num); value; *num->end++ = (h_cint_t)(value & cint_mask), value >>= cint_exponent)
        ;
}

qs_md simple_cint_to_int(const cint *num)
{
    // Return the value of a cint as a 64-bit integer (sign is ignored).
    qs_md res = 0;
    for (h_cint_t *ptr = num->end; ptr > num->mem; res = (qs_md)(res * cint_base + *--ptr))
        ;
    return res;
}

// Avl
struct avl_node *avl_cint_inserter(void *args, const void *key_to_save)
{
    // it expects as result a new node containing the given constant key.
    void *mem = *(void **)args;
    struct avl_node *res = mem;
    res->key = (cint *)(res + 1);
    mem = (cint *)res->key + 1;
    simple_dup_cint(res->key, key_to_save, &mem);
    assert(res->value == 0);
    *(void **)args = mem;
    return res;
}

// System
void *mem_aligned(void *ptr)
{
    // Default alignment of the return value is 64.
    char *res __attribute__((aligned(64)));
    res = (char *)ptr + (64 - (uintptr_t)ptr) % 64;
    return res;
}

// Misc.
int fac_apply_custom_param(const char *a, const char *b, int length, unsigned *val)
{
    int res = memcmp(a, b, length) == 0;
    if (res)
    {
        for (; *b && !(*b >= '1' && *b <= '9'); ++b)
            ;
        for (*val = 0; *b && !(*val >> 26); ++b)
            *val = *val * 10 + *b - '0';
        if (*val == 0)
            *val = 1;
    }
    return res;
}

char *fac_fill_params(fac_params *params, int argc, char **args)
{
    char *n = 0;
    for (int i = 1; i < argc; ++i)
    {
        char *s = args[i];
        for (; *s && !(*s >= '1' && *s <= '9') && !(*s >= 'a' && *s <= 'z'); ++s)
            ;
        if (*s >= 'a' && *s <= 'z')
        {
            int a = // add command line parameters...
                fac_apply_custom_param("limit=", s, 1, &params->qs_limit) || fac_apply_custom_param("testing=", s, 1, &params->testing) || fac_apply_custom_param("silent=", s, 1, &params->silent) || fac_apply_custom_param("multiplier=", s, 1, &params->qs_multiplier) || fac_apply_custom_param("rand=", s, 1, &params->qs_rand_seed) || fac_apply_custom_param("help=", s, 1, &params->help);
            assert(a >= 0);
        }
        else if (n == 0)
        {
            for (n = s; *n >= '0' && *n <= '9'; ++n)
                ;
            n = *n == 0 ? s : 0;
        }
    }
    return n;
}

char *fac_answer_to_string(fac_cint **ans)
{
    // Basic function that should return a string to represent the given answer.
    if (ans == 0 || ans[0] == 0)
        return strdup("factorizer has no answer to format.");
    int bytes = 0, i, j;
    for (i = 0; ans[i]; ++i)
    {
        bytes += (int)(1. + 0.30102999566 * ans[i]->bits);
        if (ans[i]->power > 1)
        {
            for (j = 2; ans[i]->power >> j; ++j)
                ;
            bytes += (int)(6. + 0.30102999566 * j);
        }
        bytes += (ans[i]->prime < 1) << 2;
    }
    bytes += 3 * i - 2;
    char *str, *res = str = malloc(bytes);
    assert(res);
    for (*str = 0, i = 0; ans[i]; ++i)
    {
        char *s = cint_to_string(&ans[i]->cint, 10);
        if (ans[i]->prime < 1)
            strcat(str, " \""), str += 2;
        str += sprintf(str, "%s", s);
        if (ans[i]->prime < 1)
            strcat(str, "\" "), str += 2;
        if (ans[i]->power >= 1)
            str += sprintf(str, "^%d", ans[i]->power);
        if (ans[i + 1])
            str += sprintf(str, " ");
        free(s);
    }
    return res;
}

int fac_sort_result(const void *lhs, const void *rhs)
{
    const fac_cint *L = lhs, *R = rhs;
    return h_cint_compare(&L->cint, &R->cint);
}

int quadratic_sieve(fac_caller *caller)
{
    int limit = (int)caller->params->qs_limit;
    if (limit == 0)
        limit = 220; // the default limit is such that the QS answer in seconds.
    if (caller->number->bits < 64 || caller->number->bits > limit)
        return 0;

    qs_sheet qs = {0};
    preparation_part_1(&qs, caller);
    preparation_part_2(&qs);
    preparation_part_3(&qs);
    qs_parametrize(&qs);
    preparation_part_4(&qs);
    preparation_part_5(&qs);
    preparation_part_6(&qs);
    do
    {
        do
        {
            // Keep randomly trying various polynomials.
            get_started_iteration(&qs);
            iteration_part_1(&qs, &qs.poly.D, &qs.poly.A);
            iteration_part_2(&qs, &qs.poly.A, &qs.poly.B);
            iteration_part_3(&qs, &qs.poly.A, &qs.poly.B);
            for (qs_sm i = 0, addi, *corr; i < qs.poly.gray_max && qs.n_bits != 1; ++i, ++qs.poly.curves)
            {
                addi = iteration_part_4(&qs, i, &corr, &qs.poly.B);
                iteration_part_5(&qs, &qs.constants.kN, &qs.poly.B);
                iteration_part_6(&qs, &qs.constants.kN, &qs.poly.A, &qs.poly.B, &qs.poly.C);
                iteration_part_7(&qs, addi, corr);
                iteration_part_8(&qs, addi, corr);
                register_relations(&qs, &qs.poly.A, &qs.poly.B, &qs.poly.C);
            }
        } while (inner_continuation_condition(&qs));
        // Analyzes all observations made by the algorithm.
        finalization_part_1(&qs, lanczos_block(&qs));
        finalization_part_2(&qs);
    } while (outer_continuation_condition(&qs));
    const int res = finalization_part_3(&qs);
    free(qs.mem.base);
    return res;
}

int inner_continuation_condition(qs_sheet *qs)
{
    int res = 1;
    res &= qs->n_bits != 1;                                       // the bit count of N may have changed.
    res &= qs->relations.length.now < qs->relations.length.needs; // the condition.
    if (qs->caller->params->silent == 0)
    {
        const double rel_begin = (double)qs->relations.length.now, rel_end = (double)qs->relations.length.needs;
        // fac_display_progress("Quadratic sieve", 100. * rel_begin / rel_end); // progress isn't linear.
    }
    return res;
}

int outer_continuation_condition(qs_sheet *qs)
{
    int res = qs->sieve_again_perms-- > 0;                    // avoid infinite loop.
    res &= qs->divisors.total_primes < qs->sieve_again_perms; // search prime factors.
    res &= qs->n_bits != 1;                                   // the bit count of N isn't 1.
    if (res)
    {
        qs_sm new_needs = qs->relations.length.needs;
        new_needs += new_needs >> (1 + qs->sieve_again_perms);
        if (qs->caller->params->silent == 0)
            printf("quadratic sieve targets %u more relations\n", new_needs - qs->relations.length.needs);
        qs->relations.length.needs = new_needs;
    }
    return res;
}

qs_sm linear_param_resolution(const double v[][2], const qs_sm point)
{
    qs_sm res, i, j;
    if (v[1][0] == 0)
        res = (qs_sm)v[0][1];
    else
    {
        for (j = 1; v[j + 1][0] && point > v[j][0]; ++j)
            ;
        i = j - 1;
        if (v[i][0] > point)
            res = (qs_sm)v[i][1];
        else if (v[j][0] < point)
            res = (qs_sm)v[j][1];
        else
        {
            const double a = (v[j][1] - v[i][1]) / (v[j][0] - v[i][0]);
            const double b = v[i][1] - a * v[i][0];
            res = (qs_sm)(a * point + b);
        }
    }
    return res + (res > 512) * (16 - res % 16);
}

void qs_parametrize(qs_sheet *qs)
{
    const qs_sm bits = (qs_sm)cint_count_bits(qs->caller->vars); // kN
    qs->kn_bits = bits;                                          // input was adjusted, there is at least 115-bit.

    // params as { bits, value } take the extremal value if bits exceed.
    static const double param_base_size[][2] = {{110, 800}, {130, 1500}, {210, 6e3}, {240, 12e3}, {260, 24e3}, {320, 36e3}, {0}};
    qs->base.length = linear_param_resolution(param_base_size, bits);

    static const double param_laziness[][2] = {{110, 90}, {180, 100}, {220, 100}, {250, 110}, {0}};
    // collecting more/fewer relations than recommended (used to verify "sieve again" feature).
    qs->relations.length.needs = qs->base.length * linear_param_resolution(param_laziness, bits) / 100;

    static const double param_m_value[][2] = {{110, 1}, {190, 4}, {0}};
    qs->m.length = (qs->m.length_half = 31744 * linear_param_resolution(param_m_value, bits)) << 1;

    qs->m.cache_size = 126976; // algorithm reaches "M length" by steps of "cache size".

    static const double param_error[][2] = {{110, 13}, {300, 33}, {0}};
    qs->error_bits = linear_param_resolution(param_error, bits);

    static const double param_threshold[][2] = {{110, 63}, {220, 78}, {300, 99}, {0}};
    qs->threshold.value = linear_param_resolution(param_threshold, bits);

    static const double param_alloc[][2] = {{1e3, 2}, {3e3, 8}, {5e3, 20}, {1e4, 100}, {3e4, 256}, {0}};
    qs->mem.bytes_allocated = linear_param_resolution(param_alloc, qs->base.length) << 20; // { base size, overall needs of megabytes }

    qs->sieve_again_perms = 3; // Sieve again up to 3 times before giving up

    // Iterative list
    qs->iterative_list[0] = 1; // one
    static const double param_first_prime[][2] = {{170, 8}, {210, 12}, {300, 30}, {0}};
    qs->iterative_list[1] = linear_param_resolution(param_first_prime, bits); // first
    const qs_sm large_base = qs->base.length > 5000 ? 5000 : qs->base.length;
    qs->iterative_list[2] = large_base >> 2; // medium
    qs->iterative_list[3] = large_base >> 1; // mid
    qs->iterative_list[4] = large_base;      // sec

    const double last_prime_in_base = qs->base.length * 2.5 * log_computation(qs->base.length);
    qs->relations.large_prime = (qs_md)(last_prime_in_base * last_prime_in_base * 1.25);

    // Other parameters (they have never been changed)
    qs->s.values.double_value = (qs->s.values.defined = (qs->s.values.subtract_one = bits / 28) + 1) << 1;
    qs->poly.gray_max = 1 << (qs->s.values.defined - 3); // computing the roots of f(x) once for all these polynomials.
}

// Quadratic sieve source (algorithm)
void preparation_part_1(qs_sheet *qs, fac_caller *caller)
{
    // initializing with the caller's resources
    qs->caller = caller;
    qs->calc = caller->calc;
    qs->n_bits = caller->number->bits;
}

void preparation_part_2(qs_sheet *qs)
{
    cint *N = &qs->caller->number->cint, *kN = qs->caller->vars, *ADJUSTOR = kN + 1;
    // Input is "transparently" adjusted by a prime number to measure at least 115-bit.
    static const int prime_generator[] = {
        9, 7, 5, 3, 17, 27, 3, 1, 29, 3, 21, 7, 17, 15,
        9, 43, 35, 15, 29, 3, 11, 3, 11, 15, 17, 25, 53,
        31, 9, 7, 23, 15, 27, 15, 29, 7, 59, 15, 5, 21,
        69, 55, 21, 21, 5, 159, 3, 81, 9, 69, 131, 33, 15};
    const qs_sm bits = qs->n_bits;
    if (bits < 115)
    {
        qs->adjustor = bits < 115 ? ((qs_md)1 << (124 - bits)) + prime_generator[115 - bits] : 1;
        simple_int_to_cint(ADJUSTOR, qs->adjustor);
        cint_mul(N, ADJUSTOR, kN);
    }
    else
        qs->adjustor = 1, cint_dup(kN, N);
}

void preparation_part_3(qs_sheet *qs)
{
    qs_sm mul = (qs_sm)qs->caller->params->qs_multiplier;
    if (mul == 0)
        mul = preparation_part_3_michel(qs);
    qs->multiplier = mul;
    cint *kN = qs->caller->vars, *MUL = kN + 1, *N = kN + 2;
    if (qs->multiplier > 1)
    {
        simple_int_to_cint(MUL, qs->multiplier);
        cint_dup(N, kN);
        cint_mul(MUL, N, kN);
    }
}

static inline qs_sm preparation_part_3_michel(qs_sheet *qs)
{
    qs_sm mul[] = {1, 2, 3, 4, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}, n_mul = (qs_sm)(sizeof(mul) / sizeof(qs_sm));
    cint *N = qs->caller->vars, *PRIME = N + 1, *Q = N + 2, *R = N + 3;
    qs_sm i, j;
    double score[n_mul];
    const qs_sm n_mod_8 = (qs_sm)(*N->mem % 8);
    for (i = j = 0; i < n_mul; ++i)
    {
        const qs_sm x = n_mod_8 * mul[i] % 8;
        if (x == 1 || x == 7)
        {
            mul[j] = mul[i];
            score[j] = 1.38629436 - log_computation((double)mul[i]) / 2.0;
            ++j;
        }
    }
    if (j)
        for (n_mul = j, i = 3; i < 500; i += 2)
            if (is_prime_4669921(i))
            {
                const double intake = log_computation((double)i) / (i - 1);
                simple_int_to_cint(PRIME, i);
                cint_div(qs->calc, N, PRIME, Q, R);
                const int kronecker = kronecker_symbol((qs_sm)simple_cint_to_int(R), i);
                for (j = 0; j < n_mul; ++j)
                    score[j] += intake + intake * kronecker * kronecker_symbol(mul[j], i);
            }
    for (i = 1, j = 0; i < n_mul; ++i)
        if (score[i] > 1.075 * score[0])
            score[0] = score[j = i];
    return mul[j];
}

void preparation_part_4(qs_sheet *qs)
{
    void *mem;
    mem = qs->mem.base = calloc(1, qs->mem.bytes_allocated);
    assert(mem);

    if (qs->caller->params->qs_rand_seed)
        srand(qs->rand_seed = qs->caller->params->qs_rand_seed);
    else
        qs->caller->params->qs_rand_seed = qs->rand_seed = add_rand_seed(&mem);

    // kN was computed into the caller's courtesy memory, now the QS has parametrized and "allocated"
    const size_t kn_size = qs->caller->vars[0].end - qs->caller->vars[0].mem + 1;
    // the quadratic sieve variables can store at most kN ^ 2 in terms of bits
    const size_t vars_size = kn_size << 1;
    const size_t buffers_size = qs->base.length + (qs->iterative_list[1] << 1);
    // more relation pointers than "guessed" are available (sieve again feature).
    const size_t relations_size = (qs->base.length < qs->relations.length.needs ? qs->relations.length.needs : qs->base.length) * 9 / 4;

    {
        // list of the numbers used by the algorithm
        cint *const n[] = {
            &qs->vars.N,
            // polynomial
            &qs->poly.A,
            &qs->poly.B,
            &qs->poly.C,
            &qs->poly.D,
            // temporary
            &qs->vars.TEMP[0],
            &qs->vars.TEMP[1],
            &qs->vars.TEMP[2],
            &qs->vars.TEMP[3],
            &qs->vars.TEMP[4],
            // "MY" is used to facilitate development controls, not used so far
            &qs->vars.MY[0],
            &qs->vars.MY[1],
            &qs->vars.MY[2],
            &qs->vars.MY[3],
            &qs->vars.MY[4],
            // relations finder
            &qs->vars.X,
            &qs->vars.KEY,
            &qs->vars.VALUE,
            &qs->vars.CYCLE,
            // a factor of N
            &qs->vars.FACTOR,
            // constants
            &qs->constants.kN,
            &qs->constants.ONE,
            &qs->constants.M_HALF,
            &qs->constants.LARGE_PRIME,
            &qs->constants.MULTIPLIER,
            0,
        };
        for (int i = 0; n[i]; ++i)
        {
            n[i]->mem = n[i]->end = mem_aligned(mem);
            mem = n[i]->mem + (n[i]->size = vars_size);
        }
    }

    cint_dup(&qs->vars.N, &qs->caller->number->cint);
    cint_dup(&qs->constants.kN, qs->caller->vars);

    simple_int_to_cint(&qs->constants.ONE, 1);
    simple_int_to_cint(&qs->constants.M_HALF, qs->m.length_half);
    simple_int_to_cint(&qs->constants.LARGE_PRIME, qs->relations.large_prime);
    simple_int_to_cint(&qs->constants.MULTIPLIER, qs->multiplier);

    // Allocates "s" rows
    qs->s.data = mem_aligned(mem);
    mem = mem_aligned(qs->s.data + qs->s.values.defined);
    for (qs_sm i = 0; i < qs->s.values.defined; ++i)
    {
        simple_inline_cint(&qs->s.data[i].B_terms, kn_size, &mem); // also "s" more cint
        qs->s.data[i].A_inv_double_value_B_terms = mem;
        mem = mem_aligned(qs->s.data[i].A_inv_double_value_B_terms + qs->base.length);
    }
    qs->s.A_indexes = mem_aligned(mem); // the indexes of the prime numbers that compose A

    // Allocates "base length" rows
    qs->base.data = mem_aligned(qs->s.A_indexes + qs->s.values.double_value);
    qs->m.positions[0] = mem_aligned(qs->base.data + qs->base.length);
    qs->m.positions[1] = mem_aligned(qs->m.positions[0] + qs->base.length);
    qs->m.sieve = mem_aligned(qs->m.positions[1] + qs->base.length);
    qs->m.sieve[qs->m.length] = 0xFF; // the end of the sieve evaluates to "true" under any "truthy" mask.
    qs->m.flags = mem_aligned(qs->m.sieve + qs->m.length + sizeof(uint64_t));
    // buffer[0] is zeroed after use, buffer[1] isn't supposed zeroed.
    qs->buffer[0] = mem_aligned(qs->m.flags + qs->base.length);
    qs->buffer[1] = mem_aligned(qs->buffer[0] + buffers_size);

    // Other allocations
    qs->relations.length.reserved = (qs_sm)relations_size;
    // Lanczos Block has a part of memory, it takes a "lite" snapshot before throwing relations.
    qs->lanczos.snapshot = mem_aligned(qs->buffer[1] + buffers_size);
    qs->relations.data = mem_aligned(qs->lanczos.snapshot + relations_size);
    qs->divisors.data = mem_aligned(qs->relations.data + relations_size);
    qs->mem.now = mem_aligned(qs->divisors.data + 512);

    const qs_sm n_trees = (qs_sm)(sizeof(qs->uniqueness) / sizeof(struct avl_manager));
    for (qs_sm i = 0; i < n_trees; ++i)
    {
        // the trees are used to identify duplicates (relations, partials, factors of N)
        qs->uniqueness[i].inserter_argument = &qs->mem.now;
        qs->uniqueness[i].inserter = &avl_cint_inserter;
        qs->uniqueness[i].comparator = (int (*)(const void *, const void *)) & h_cint_compare;
        // they use default sign-less comparator.
    }
}

void preparation_part_5(qs_sheet *qs)
{
    static const double inv_ln_2 = 1.44269504088896340736;
    cint *A = qs->vars.TEMP, *B = A + 1, *C = A + 2;
    qs_sm i = 0, prime;
    // the factor base contain the multiplier if different from 2.
    if (qs->multiplier != 2)
        qs->base.data[i].size = (qs_sm)(.35 + inv_ln_2 * log_computation(qs->base.data[i].num = qs->multiplier)), ++i;

    // then it contains the number 2.
    qs->base.data[i].num = 2, qs->base.data[i].size = 1;
    qs->base.data[i].sqrt_kN_mod_prime = *qs->constants.kN.mem % 8 == 1 || *qs->constants.kN.mem % 8 == 7, ++i;

    // then the prime numbers for which kN is a quadratic residue modulo.
    for (prime = 3; i < qs->base.length; prime += 2)
        if (is_prime_4669921(prime))
        {
            simple_int_to_cint(A, prime);
            cint_div(qs->calc, &qs->constants.kN, A, B, C);
            const qs_sm kn_mod_prime = (qs_sm)simple_cint_to_int(C);
            qs->base.data[i].sqrt_kN_mod_prime = tonelli_shanks(kn_mod_prime, prime);
            if (qs->base.data[i].sqrt_kN_mod_prime)
            {
                qs->base.data[i].num = prime;
                qs->base.data[i].size = (qs_sm)(.35 + inv_ln_2 * log_computation(prime)), ++i;
            } // 2.5 * (base size) * ln(base size) is close to the largest prime number in factor base.
        }
}

void preparation_part_6(qs_sheet *qs)
{
    const qs_sm s = qs->s.values.defined;
    qs_sm i, min;
    qs->poly.span_half = (qs->poly.span = qs->base.length / s / s / 2) >> 1;
    cint *kN = qs->vars.TEMP, *TMP = kN + 1, *R = kN + 2;
    cint_dup(kN, &qs->constants.kN);
    cint_left_shifti(kN, 1);
    cint_sqrt(qs->calc, kN, TMP, R);
    cint_div(qs->calc, TMP, &qs->constants.M_HALF, &qs->poly.D, R);
    qs->poly.d_bits = (qs_sm)cint_count_bits(&qs->poly.D);
    cint_nth_root(qs->calc, &qs->poly.D, s, R);
    assert(s >= 3); // use the s-th root of D.
    const qs_sm root = (qs_sm)simple_cint_to_int(R);
    for (i = 1; assert(i < qs->base.length), qs->base.data[i].num <= root; ++i)
        ;
    assert(i >= qs->poly.span);
    for (min = i - qs->poly.span_half, i *= i; i / min < qs->poly.span + min; --min)
        ;
    qs->poly.min = min;
}

void get_started_iteration(qs_sheet *qs)
{
    if (qs->lanczos.snapshot[0].relation)
    {
        // the operation is fast, it shouldn't happen in average case.
        // it restores the relations reduced by Lanczos algorithm.
        qs_sm i;
        for (i = 0; qs->lanczos.snapshot[i].relation; ++i)
        {
            qs->relations.data[i] = qs->lanczos.snapshot[i].relation;
            qs->relations.data[i]->Y.length = qs->lanczos.snapshot[i].y_length;
            qs->lanczos.snapshot[i].relation = 0;
        }
        qs->relations.length.now = i;
    }
    // D is randomized if algorithm remarks that no relation accumulates (the software tester didn't remove it)
    if (qs->relations.length.prev == qs->relations.length.now && qs->poly.curves)
        cint_random_bits(&qs->poly.D, qs->poly.d_bits);
    qs->relations.length.prev = qs->relations.length.now;
}

void iteration_part_1(qs_sheet *qs, const cint *D, cint *A)
{
    // A is a "random" product of "s" distinct prime numbers from the factor base.
    cint *X = qs->vars.TEMP, *Y = X + 1, *TMP;
    qs_sm a, b = qs->poly.min + qs->poly.span_half, i = 0, j;
    if (qs->s.values.defined & 1)
        TMP = A, A = X, X = TMP;
    // swap pointers so the last multiplication completes inside the A variable.
    simple_int_to_cint(A, 1);
    for (a = 0, b *= b; a < qs->s.values.subtract_one; ++a)
    {
        if (a & 1)
            i = b / (i + qs->poly.min) - (qs_sm)rand_upto(10);
        else
            i = qs->poly.span_half + (qs_sm)rand_upto(qs->poly.span_half) + qs->poly.min;
        for (j = 0; j < a; j = i == qs->s.data[j].prime_index ? ++i, 0 : j + 1)
            ;
        qs->s.data[a].prime_index = i; // the selected divisor of A wasn't already present in the product.
        simple_int_to_cint(Y, qs->base.data[i].num);
        cint_mul(A, Y, X), TMP = A, A = X, X = TMP;
    }
    // a prime number from the factor base completes A, which must be close to D.
    cint_div(qs->calc, D, A, X, Y);
    const qs_sm d_over_a = (qs_sm)simple_cint_to_int(X);
    for (i = qs->base.data[0].num != 2; qs->base.data[i].num <= d_over_a; ++i)
        ;
    for (j = 0; j < qs->s.values.subtract_one; j = i == qs->s.data[j].prime_index ? ++i, 0 : j + 1)
        ;
    qs->s.data[qs->s.values.subtract_one].prime_index = i;
    simple_int_to_cint(Y, qs->base.data[i].num);
    cint_mul(A, Y, X); // generated A values should always be distinct, "A" no longer change.
    assert(X == &qs->poly.A);
}

void iteration_part_2(qs_sheet *qs, const cint *A, cint *B)
{
    cint *X = qs->vars.TEMP, *PRIME = X + 1, *Y = X + 2, *R = X + 3;
    qs_sm i, *pen = qs->s.A_indexes;
    cint_erase(B);
    for (i = 0; i < qs->s.values.defined; ++i)
    {
        const qs_sm idx = qs->s.data[i].prime_index, prime = qs->base.data[idx].num;
        if (idx >= qs->iterative_list[3])
            qs->iterative_list[3] = 8 + idx - idx % 8;
        // write [index of prime number, power] of the A factors into buffer.
        *pen++ = qs->s.data[i].prime_index, *pen++ = 1;
        qs->s.data[i].prime_squared = (qs_md)prime * (qs_md)prime;
        simple_int_to_cint(PRIME, prime);
        cint_div(qs->calc, A, PRIME, X, R), assert(R->mem == R->end); // div exact.
        cint_div(qs->calc, X, PRIME, Y, R);
        qs->s.data[i].A_over_prime_mod_prime = (qs_sm)simple_cint_to_int(R);
        qs_md x = modular_inverse(qs->s.data[i].A_over_prime_mod_prime, prime);
        x = x * qs->base.data[qs->s.data[i].prime_index].sqrt_kN_mod_prime % prime;
        simple_int_to_cint(X, x > prime >> 1 ? prime - x : x);
        cint_mul(A, X, Y);
        cint_div(qs->calc, Y, PRIME, &qs->s.data[i].B_terms, R), assert(R->mem == R->end); // div exact.
        cint_addi(B, &qs->s.data[i].B_terms);
    }
}

void iteration_part_3(qs_sheet *qs, const cint *A, const cint *B)
{
    cint *Q = qs->vars.TEMP, *R = Q + 1, *PRIME = Q + 2;
    qs_md i, j, x, y;
    for (i = 0; i < qs->base.length; ++i)
    {
        // prepare the "roots" and "A_inv_double_value_B_terms". The algorithm will
        // fill 2 ** (s - 3) sieves by using these values and adding "prime sizes".
        const qs_sm prime = qs->base.data[i].num;
        simple_int_to_cint(PRIME, prime);
        cint_div(qs->calc, A, PRIME, Q, R);
        const qs_sm a_mod_prime = (qs_sm)simple_cint_to_int(R);
        cint_div(qs->calc, B, PRIME, Q, R);
        const qs_sm b_mod_prime = (qs_sm)simple_cint_to_int(R);
        const qs_sm a_inv_double_value = modular_inverse(a_mod_prime, prime) << 1;
        // Arithmetic shifts "<<" and ">>" performs multiplication or division by powers of two.
        x = y = prime;
        x += qs->base.data[i].sqrt_kN_mod_prime;
        y -= qs->base.data[i].sqrt_kN_mod_prime;
        x -= b_mod_prime;
        x *= a_inv_double_value >> 1;
        y *= a_inv_double_value;
        x += qs->m.length_half;
        x %= prime;
        y += x;
        y %= prime;
        qs->base.data[i].root[0] = (qs_sm)x;
        qs->base.data[i].root[1] = (qs_sm)y;
        for (j = 0; j < qs->s.values.defined; ++j)
        {
            // compute the roots update value for all "s".
            cint_div(qs->calc, &qs->s.data[j].B_terms, PRIME, Q, R);
            const qs_md b_term = simple_cint_to_int(R);
            qs->s.data[j].A_inv_double_value_B_terms[i] = (qs_sm)(a_inv_double_value * b_term % prime);
        }
    }
    // The next function operates over "B_terms" multiplied by 2.
    for (i = 0; i < qs->s.values.defined; cint_left_shifti(&qs->s.data[i++].B_terms, 1))
        ;
}

qs_sm iteration_part_4(const qs_sheet *qs, const qs_sm nth_curve, qs_sm **corr, cint *B)
{
    qs_sm i, gray_act; // the Gray code in "nth_curve" indicates which "B_term" to consider.
    for (i = 0; nth_curve >> i & 1; ++i)
        ;
    if (gray_act = (nth_curve >> i & 2) != 0, gray_act)
        cint_addi(B, &qs->s.data[i].B_terms);
    else // and which action to perform.
        cint_subi(B, &qs->s.data[i].B_terms);
    *corr = qs->s.data[i].A_inv_double_value_B_terms;
    return gray_act; // B values generated here should always be distinct.
}

void iteration_part_5(qs_sheet *qs, const cint *kN, const cint *B)
{
    cint *P = qs->vars.TEMP, *Q = P + 1, *R_kN = P + 2, *R_B = P + 3, *TMP = P + 4;
    for (qs_sm a = 0; a < qs->s.values.defined; ++a)
    {
        const qs_sm i = qs->s.data[a].prime_index;
        const qs_tmp prime = qs->base.data[i].num;
        simple_int_to_cint(P, qs->s.data[a].prime_squared);
        cint_div(qs->calc, B, P, Q, R_B);
        cint_div(qs->calc, kN, P, Q, R_kN);
        if (B->nat < 0)
            cint_addi(R_B, P); // if B is negative.
        const qs_tmp rem_b = (qs_tmp)simple_cint_to_int(R_B);
        const qs_tmp rem_kn = (qs_tmp)simple_cint_to_int(R_kN);
        qs_tmp s; // both remainders are modulo the prime number squared.
        if (rem_b >> 31)
        {
            // the multiplication can overflow.
            cint_mul(R_B, R_B, TMP);
            cint_subi(TMP, R_kN);
            simple_int_to_cint(P, (qs_md)prime);
            cint_div(qs->calc, TMP, P, Q, R_B);
            s = (qs_tmp)simple_cint_to_int(Q);
            if (Q->nat < 0)
                s = -s;
        }
        else
        {
            // the system can multiply.
            s = rem_b * rem_b - rem_kn;
            s /= prime;
        }
        //
        qs_tmp bezout = (rem_b % prime) * (qs_tmp)qs->s.data[a].A_over_prime_mod_prime;
        bezout = (qs_tmp)modular_inverse((qs_sm)(bezout % prime), (qs_sm)prime);
        //
        s = (qs_tmp)qs->m.length_half - s * bezout;
        s %= prime;
        s += (s < 0) * prime;
        qs->base.data[i].root[0] = (qs_sm)s;
        qs->base.data[i].root[1] = (qs_sm)-1;
    }
}

void iteration_part_6(qs_sheet *qs, const cint *kN, const cint *A, const cint *B, cint *C)
{
    cint *TMP = qs->vars.TEMP, *R = TMP + 1;
    cint_mul(B, B, TMP);                                        // (B * B) % A = kN % A
    cint_subi(TMP, kN);                                         // C = (B * B - kN) / A
    cint_div(qs->calc, TMP, A, C, R), assert(R->mem == R->end); // div exact.
}

void iteration_part_7(qs_sheet *qs, const qs_sm gray_addi, const qs_sm *restrict corr)
{
    memset(qs->m.sieve, 0, qs->m.length * sizeof(*qs->m.sieve));
    memset(qs->m.flags, 0, qs->base.length * sizeof(*qs->m.flags));
    uint8_t *restrict end = qs->m.sieve + qs->m.length, *p_0, *p_1;
    for (qs_sm i = qs->iterative_list[3], j = qs->iterative_list[4]; i < j; ++i)
    {
        const qs_sm prime = qs->base.data[i].num, size = qs->base.data[i].size, co = gray_addi ? prime - corr[i] : corr[i];
        qs->base.data[i].root[0] += co;
        if (qs->base.data[i].root[0] >= prime)
            qs->base.data[i].root[0] -= prime;
        qs->base.data[i].root[1] += co;
        if (qs->base.data[i].root[1] >= prime)
            qs->base.data[i].root[1] -= prime;
        p_0 = qs->m.sieve + qs->base.data[i].root[0];
        p_1 = qs->m.sieve + qs->base.data[i].root[1];
        for (; end > p_0 && end > p_1;)
            *p_0 += size, p_0 += prime, *p_1 += size, p_1 += prime;
        *p_0 += (end > p_0) * size, *p_1 += (end > p_1) * size;
    }
    for (qs_sm i = qs->iterative_list[4], j = qs->base.length; i < j; ++i)
    {
        const qs_sm prime = qs->base.data[i].num, size = qs->base.data[i].size, co = gray_addi ? prime - corr[i] : corr[i];
        qs->base.data[i].root[0] += co;
        if (qs->base.data[i].root[0] >= prime)
            qs->base.data[i].root[0] -= prime;
        qs->base.data[i].root[1] += co;
        if (qs->base.data[i].root[1] >= prime)
            qs->base.data[i].root[1] -= prime;
        for (p_0 = qs->m.sieve + qs->base.data[i].root[0]; end > p_0; qs->m.flags[i] |= 1 << ((p_0 - qs->m.sieve) & 7), *p_0 += size, p_0 += prime)
            ;
        for (p_1 = qs->m.sieve + qs->base.data[i].root[1]; end > p_1; qs->m.flags[i] |= 1 << ((p_1 - qs->m.sieve) & 7), *p_1 += size, p_1 += prime)
            ;
    }
}

void iteration_part_8(qs_sheet *qs, const qs_sm gray_addi, const qs_sm *corr)
{
    uint8_t *chunk_begin = qs->m.sieve, *chunk_end = chunk_begin;
    uint8_t *sieve_end = chunk_begin + qs->m.length;
    qs_sm *buffer = qs->buffer[0], walk_idx, *walk = buffer;
    // Since the previous function, the check is performed for the prime numbers of the factor base.
    for (qs_sm i = 0; i < qs->iterative_list[3]; ++i)
        if (qs->base.data[i].root[1] != (qs_sm)-1)
        {
            *walk++ = i; // the current prime number isn't a factor of A.
            const qs_sm prime = qs->base.data[i].num, co = gray_addi ? prime - corr[i] : corr[i];
            qs->base.data[i].root[0] += co;
            if (qs->base.data[i].root[0] >= prime)
                qs->base.data[i].root[0] -= prime;
            qs->base.data[i].root[1] += co;
            if (qs->base.data[i].root[1] >= prime)
                qs->base.data[i].root[1] -= prime;
            qs->m.positions[0][i] = chunk_begin + qs->base.data[i].root[0];
            qs->m.positions[1][i] = chunk_begin + qs->base.data[i].root[1];
        }
    for (walk_idx = 0; buffer[walk_idx] < qs->iterative_list[1]; ++walk_idx)
        ;
    do
    {
        walk = buffer + walk_idx;
        chunk_end = chunk_end + qs->m.cache_size < sieve_end ? chunk_end + qs->m.cache_size : sieve_end;
        do
        {
            const qs_sm size = qs->base.data[*walk].size, prime = qs->base.data[*walk].num, times = 4 >> (*walk > qs->iterative_list[2]);
            uint8_t **const p_0 = qs->m.positions[0] + *walk, **const p_1 = qs->m.positions[1] + *walk;
            const ptrdiff_t diff = *p_1 - *p_0;
            for (const uint8_t *const bound = chunk_end - prime * times; bound > *p_0;)
                for (qs_sm i = 0; i < times; ++i)
                    **p_0 += size, *(*p_0 + diff) += size, *p_0 += prime;
            for (; *p_0 < chunk_end && *p_0 + diff < chunk_end;)
                **p_0 += size, *(*p_0 + diff) += size, *p_0 += prime;
            *p_1 = *p_0 + diff;
            if (*p_0 < chunk_end)
                **p_0 += size, *p_0 += prime;
            if (*p_1 < chunk_end)
                **p_1 += size, *p_1 += prime;
        } while (*++walk);
    } while (chunk_begin = chunk_end, chunk_begin < sieve_end);
    memset(qs->buffer[0], 0, (walk - qs->buffer[0]) * sizeof(*walk));
}

int qs_register_factor(qs_sheet *qs)
{
    cint *F = &qs->vars.FACTOR;
    int i, res = h_cint_compare(F, &qs->constants.ONE) > 0 && h_cint_compare(F, &qs->vars.N) < 0;
    if (res)
    {
        F->nat = 1; // absolute value of the factor.
        const struct avl_node *node = avl_at(&qs->uniqueness[2], F);
        if (qs->uniqueness[2].affected)
            for (i = 0; i < 2 && qs->n_bits != 1; ++i)
            {
                const int is_prime = cint_is_prime(qs->calc, F, -1);
                if (is_prime)
                {
                    const int power = (int)cint_remove(qs->calc, &qs->vars.N, F);
                    assert(power); // 200-bit RSA take about 10,000,000+ "duplications".
                    fac_push(qs->caller, F, 1, power, 0);
                    ++qs->divisors.total_primes;
                    // if "n_bits" is greater than one the functions must continue to search factors.
                    qs->n_bits = (qs_sm)cint_count_bits(&qs->vars.N);
                    if (qs->n_bits == 1)
                        res = -1;
                    else
                        cint_dup(F, &qs->vars.N);
                }
                else if (i++ == 0)
                    qs->divisors.data[qs->divisors.length++] = node->key;
            }
    }
    return res;
}

void register_relations(qs_sheet *qs, const cint *A, const cint *B, const cint *C)
{
    cint *TMP = qs->vars.TEMP, *K = &qs->vars.KEY, *V = &qs->vars.VALUE;
    qs_sm m_idx, idx, mod;
    // iterates the values of X in [-M/2, +M/2].
    for (m_idx = 0; m_idx < qs->m.length; ++m_idx)
        // the trick that permit to step faster using typecast and 0xC0C0C0C0C0C0C0C0 isn't implemented.
        if (qs->m.sieve[m_idx] >= qs->threshold.value)
        {
            // over the threshold, compute f(X) and check candidate for smoothness.
            simple_int_to_cint(&qs->vars.X, m_idx);
            cint_subi(&qs->vars.X, &qs->constants.M_HALF); // X = "current index" - M/2
            cint_mul(A, &qs->vars.X, TMP);                 // TMP = AX
            cint_addi(TMP, B);                             // TMP = AX + B
            cint_dup(K, TMP);                              // Key = copy of AX + B
            cint_addi(TMP, B);                             // TMP = AX + 2B
            cint_mul(TMP, &qs->vars.X, V);                 // V = AX^2 + 2BX
            cint_addi(V, C);                               // Value = f(X) = AX^2 + 2BX + C
            // it should hold that kN = (Key * Key) - (A * Value)
            V->nat = 1; // absolute value
            qs_sm target_bits = (qs_sm)cint_count_bits(V) - qs->error_bits;
            qs_sm removed_bits = 0, *restrict pen = qs->buffer[1];
            //  writes the pairs [index of the prime number, power found in V].
            if (qs->base.data[0].num != 1)
            {
                simple_int_to_cint(TMP, qs->base.data[0].num);
                *pen++ = 0; // remove powers of the multiplier.
                *pen = (qs_sm)cint_remove(qs->calc, V, TMP);
                if (*pen)
                    removed_bits += *pen++ * qs->base.data[0].size;
                else
                    --pen;
            }
            for (idx = 1; idx < qs->iterative_list[1]; ++idx)
                if (qs->base.data[idx].root[1] == (qs_sm)-1 || (mod = m_idx % qs->base.data[idx].num, mod == qs->base.data[idx].root[0] || mod == qs->base.data[idx].root[1]))
                {
                    simple_int_to_cint(TMP, qs->base.data[idx].num);
                    *pen++ = idx;
                    *pen = (qs_sm)cint_remove(qs->calc, V, TMP);
                    if (*pen)
                        removed_bits += *pen++ * qs->base.data[idx].size;
                    else
                        --pen;
                }
            if (removed_bits + qs->m.sieve[m_idx] >= target_bits)
            {
                // there is a chance to register a new relation.
                for (removed_bits = 0, target_bits = qs->m.sieve[m_idx]; idx < qs->iterative_list[4] && removed_bits < target_bits; ++idx)
                    if (qs->base.data[idx].root[1] == (qs_sm)-1 || (mod = m_idx % qs->base.data[idx].num, mod == qs->base.data[idx].root[0] || mod == qs->base.data[idx].root[1]))
                    {
                        simple_int_to_cint(TMP, qs->base.data[idx].num);
                        *pen++ = idx;
                        *pen = (qs_sm)cint_remove(qs->calc, V, TMP);
                        if (*pen)
                            removed_bits += *pen++ * qs->base.data[idx].size;
                        else
                            --pen;
                    }
                for (const uint8_t mask = 1 << (m_idx & 7); idx < qs->base.length && removed_bits < target_bits; ++idx)
                    if (qs->m.flags[idx] & mask)
                        if (mod = m_idx % qs->base.data[idx].num, mod == qs->base.data[idx].root[0] || mod == qs->base.data[idx].root[1])
                        {
                            simple_int_to_cint(TMP, qs->base.data[idx].num);
                            *pen++ = idx;
                            *pen = (qs_sm)cint_remove(qs->calc, V, TMP);
                            if (*pen)
                                removed_bits += *pen++ * qs->base.data[idx].size;
                            else
                                --pen;
                        }
                const qs_sm *restrict const prime_indexes_and_powers[4] = {
                    qs->s.A_indexes, // really factoring A * f(X), commit outstanding A factors.
                    qs->s.A_indexes + qs->s.values.double_value,
                    qs->buffer[1],
                    pen,
                };
                if (h_cint_compare(V, &qs->constants.ONE) == 0)
                    register_relation_kind_1(qs, K, prime_indexes_and_powers);
                // #1 warwick.ac.uk, not a relation, perhaps a partial ?
                else if (h_cint_compare(V, &qs->constants.LARGE_PRIME) < 0)
                    register_relation_kind_2(qs, K, V, prime_indexes_and_powers);
            }
        }
}

void register_relation_kind_1(qs_sheet *qs, const cint *KEY, const qs_sm *const restrict args[4])
{
    struct avl_node *node = avl_at(&qs->uniqueness[0], KEY);
    if (node->value)
        return; // duplicates at this stage are ignored.
    struct qs_relation *rel = qs->mem.now;
    qs_sm i, j;
    qs->mem.now = rel + 1;     // a relation must be swappable for Lanczos Block reducing.
    rel->X = node->key;        // constant X is stored by the node key.
    rel->Y.data = qs->mem.now; // Y data length only decreases.
    const size_t y_length = (args[1] - args[0] + args[3] - args[2]) >> 1;
    rel->axis.Z.data = rel->Y.data + y_length; // writes Z ahead.
    for (i = 0; i < 4;)
    {
        // processes the given column arrays.
        const qs_sm *restrict idx = args[i++], *restrict const end_index = args[i++];
        for (; idx < end_index; idx += 2)
        {
            const qs_sm power = *(idx + 1);
            if (power & 1)
            {
                // remove from Y the indexes of the prime numbers that are already listed (factors of A).
                for (j = 0; j < rel->Y.length && rel->Y.data[j] != *idx; ++j)
                    ;
                if (j == rel->Y.length) // add, the index wasn't present.
                    rel->Y.data[rel->Y.length++] = *idx;
                else // or remove.
                    memmove(rel->Y.data + j, rel->Y.data + j + 1, (--rel->Y.length - j) * sizeof(*rel->Y.data));
            }
            for (j = 0; j < power; ++j)
                rel->axis.Z.data[rel->axis.Z.length++] = *idx;
        }
    }
    qs->mem.now = rel->axis.Z.data + rel->axis.Z.length; // Z length is known.
    int verified = 0;
    if (rel->Y.length > qs->s.values.defined)
    {
        // it often passes.
        cint *A = qs->vars.TEMP, *B = A + 1;
        simple_int_to_cint(A, 1);
        for (j = 0; j < rel->axis.Z.length; ++j)
        {
            simple_int_to_cint(B, qs->base.data[rel->axis.Z.data[j]].num);
            cint_mul_modi(qs->calc, A, B, &qs->constants.kN);
        }
        cint_mul_mod(qs->calc, rel->X, rel->X, &qs->constants.kN, B);
        verified = !cint_compare(A, B) || (cint_addi(A, B), !cint_compare(A, &qs->constants.kN));
    }
    if (verified)
    {
        node->value = qs->relations.data[qs->relations.length.now] = rel;
        qs->mem.now = rel->axis.Z.data + rel->axis.Z.length;
        rel->id = ++qs->relations.length.now; // Keep the relation
    }
    else
    {
        char *open = (char *)rel, *close = qs->mem.now;
        qs->mem.now = memset(open, 0, close - open); // Throw
    }
}

void register_relation_kind_2(qs_sheet *qs, const cint *KEY, const cint *VALUE, const qs_sm *const restrict args[4])
{
    if (qs->kn_bits < 150)
        return; // but does not have time to "start" with a small N.
    struct avl_node *node = avl_at(&qs->uniqueness[1], VALUE);
    struct qs_relation *old, *new;
    cint *BEZOUT = 0;
    old = node->value;
    if (old)
    {
        if (old->X == 0)
            return; // the value is already marked as "ignored".
        if (old->axis.next)
            return; // accepting all "next" without caring reduce the "chance".
        for (; old && h_cint_compare(KEY, old->X); old = old->axis.next)
            ;
        if (old)
            return; // same KEY already registered.
        old = node->value;
        if (old->axis.next == 0)
        {
            cint *A = qs->vars.TEMP, *B = A + 1;
            if (qs->multiplier != 1)
                if (cint_gcd(qs->calc, VALUE, &qs->constants.MULTIPLIER, A), *A->mem != 1)
                {
                    old->X = 0; // they shouldn't be related so close to the multiplier.
                    return;
                }
            cint_modular_inverse(qs->calc, VALUE, &qs->constants.kN, A);
            if (A->mem == A->end)
            {
                old->X = 0; // no solution to the linear congruence.
                cint_gcd(qs->calc, VALUE, &qs->constants.kN, &qs->vars.FACTOR);
                cint_div(qs->calc, &qs->vars.N, &qs->vars.FACTOR, A, B);
                if (B->mem == B->end) // found a small factor of N ?
                    qs_register_factor(qs);
                return; // nothing.
            }
            else
                BEZOUT = A;
        }
    }

    new = mem_aligned(qs->mem.now);
    qs->mem.now = new + 1;
    new->X = qs->mem.now;

    if (BEZOUT)
    {
        qs->mem.now = new->X + 2;
        simple_dup_cint(new->X, KEY, &qs->mem.now);
        simple_dup_cint(new->X + 1, BEZOUT, &qs->mem.now);
        // The 2nd newcomer become the root of the linked list.
        new->axis.next = old, node->value = new = old = new;
    }
    else
    {
        qs->mem.now = new->X + 1; // they come at the end of the linked list.
        simple_dup_cint(new->X, KEY, &qs->mem.now);
        if (old)
        {
            for (; old->axis.next; old = old->axis.next)
                ;
            old->axis.next = new, old = node->value;
        }
        else
            node->value = new;
    }

    qs_sm *data = new->Y.data = mem_aligned(qs->mem.now);
    new->Y.length = (qs_sm)(args[1] - args[0]);
    memcpy(data, args[0], new->Y.length * sizeof(*data));
    memcpy(data + new->Y.length, args[2], (args[3] - args[2]) * sizeof(*data));
    new->Y.length += (qs_sm)(args[3] - args[2]);
    qs->mem.now = new->Y.data + new->Y.length;

    if (old)
    {
        BEZOUT = old->X + 1; // the modular inverse was stored here.
        cint_mul_mod(qs->calc, new->X, BEZOUT, &qs->constants.kN, &qs->vars.CYCLE);
        do
        {
            if (old != new)
            {
                cint_mul_mod(qs->calc, &qs->vars.CYCLE, old->X, &qs->constants.kN, &qs->vars.KEY);
                qs_sm *restrict begin = qs->buffer[0], *restrict pen = begin;
                data = memset(qs->buffer[1], 0, qs->base.length * sizeof(*data));
                for (qs_sm i = 0; i < new->Y.length; i += 2)
                    data[new->Y.data[i]] += new->Y.data[i + 1];
                for (qs_sm i = 0; i < old->Y.length; i += 2)
                    data[old->Y.data[i]] += old->Y.data[i + 1];
                for (qs_sm i = 0; i < qs->base.length; ++i)
                    if (data[i]) // writes [index of the prime number, power]
                        *pen++ = i, *pen++ = data[i];
                args = (const qs_sm *restrict const[4]){
                    begin,
                    pen,
                    0,
                    0,
                };
                register_relation_kind_1(qs, &qs->vars.KEY, args);
                memset(begin, 0, (char *)pen - (char *)begin); // zeroed.
            }
        } while ((old = old->axis.next));
    }
}

void finalization_part_1(qs_sheet *qs, const uint64_t *restrict const lanczos_answer)
{
    const uint64_t mask = *lanczos_answer, *restrict null_rows = lanczos_answer + 1;
    // Lanczos "linear algebra" answer is simply "mask followed by null_rows", with read-only.
    if (mask == 0 || null_rows == 0)
        return;
    cint *X = qs->vars.TEMP, *Y = X + 1, *TMP = X + 2, *POW = X + 3;
    qs_sm *restrict power_of_primes;
    for (qs_sm row = 0; row < 64 && qs->n_bits != 1; ++row)
        if (mask >> row & 1)
        {
            simple_int_to_cint(X, 1), simple_int_to_cint(TMP, 1), simple_int_to_cint(Y, 1);
            power_of_primes = memset(qs->buffer[1], 0, qs->base.length * sizeof(*power_of_primes));
            for (qs_sm i = 0; i < qs->relations.length.now; ++i)
                if (null_rows[i] >> row & 1)
                {
                    const struct qs_relation *restrict const rel = qs->relations.data[i];
                    cint_mul_modi(qs->calc, X, rel->X, &qs->vars.N);
                    for (qs_sm j = 0; j < rel->axis.Z.length; ++j)
                        ++power_of_primes[rel->axis.Z.data[j]];
                }
            for (qs_sm i = 0; i < qs->base.length; ++i)
                if (power_of_primes[i])
                {
                    // powers are even ... square root ...
                    simple_int_to_cint(TMP, qs->base.data[i].num);
                    simple_int_to_cint(POW, power_of_primes[i] >> 1);
                    cint_pow_modi(qs->calc, TMP, POW, &qs->vars.N);
                    cint_mul_modi(qs->calc, Y, TMP, &qs->vars.N);
                }
            h_cint_subi(Y, X);
            if (Y->mem != Y->end)
            {
                cint_gcd(qs->calc, &qs->vars.N, Y, &qs->vars.FACTOR);
                // 100 digits RSA number has been factored by the software in 2022.
                qs_register_factor(qs);
            }
        }
}

void finalization_part_2(qs_sheet *qs)
{
    if (qs->n_bits == 1)
        return;

    // Algorithm checked Lanczos answer but N is still greater than one.
    // Perform basic checks until no new divisor can be discovered.

    cint *F = &qs->vars.FACTOR, **di = qs->divisors.data, *Q = qs->vars.TEMP, *R = Q + 1;
    qs_sm i, j, k, count = 0;

    for (i = qs->divisors.processing_index, j = qs->divisors.length; i < j; ++i)
        for (k = 1 + i; k < j; ++k)
            if (cint_gcd(qs->calc, di[i], di[k], F), qs_register_factor(qs) == -1)
                return; // register "gcd of new divisors with old divisors"
    do
    {
        for (; i = j, j = qs->divisors.length, i != j;)
            for (; i < j; ++i)
                for (k = 0; k < i; ++k)
                    if (cint_gcd(qs->calc, di[i], di[k], F), qs_register_factor(qs) == -1)
                        return; // register "gcd of new divisors with old divisors"

        for (i = qs->divisors.processing_index; i < j; ++i)
            if (fac_any_root_check(qs->caller, di[i], &qs->vars.FACTOR, R))
                if (qs_register_factor(qs) == -1)
                    return; // register "perfect power of new divisors"

        if (count != qs->divisors.total_primes)
            if (fac_any_root_check(qs->caller, &qs->vars.N, &qs->vars.FACTOR, R))
                if (qs_register_factor(qs) == -1)
                    return; // register "prefect root of N"

        count = qs->divisors.total_primes;
        qs->divisors.processing_index = j;
    } while (j != qs->divisors.length);
}

int finalization_part_3(qs_sheet *qs)
{
    int res = qs->n_bits == 1;
    if (res == 0)
    {
        cint *F = &qs->vars.FACTOR;
        for (qs_sm i = 0; i < qs->divisors.length; ++i)
        {
            if (qs->caller->params->silent == 0)
            {
                char *str = cint_to_string(qs->divisors.data[i], 10);
                printf("- quadratic sieve can't silently ignore %s\n", str);
                free(str);
            }
            if (h_cint_compare(&qs->vars.N, qs->divisors.data[i]) > 0)
            {
                const int power = (int)cint_remove(qs->calc, &qs->vars.N, qs->divisors.data[i]);
                if (power)
                {
                    assert(power == 1);
                    fac_push(qs->caller, F, 0, 1, 1);
                }
            }
        }
        res = h_cint_compare(&qs->vars.N, &qs->caller->number->cint);
        if (res) // res is true if QS was able to decompose N.
            if (h_cint_compare(&qs->vars.N, &qs->constants.ONE))
                fac_push(qs->caller, &qs->vars.N, -1, 1, 1);
    }
    return res;
}

void lanczos_mul_MxN_Nx64(const qs_sheet *qs, const uint64_t *X, const qs_sm max_size, uint64_t *Y)
{
    assert(Y != X);
    memset(Y, 0, max_size * sizeof(uint64_t));
    for (qs_sm a = 0, b; a < qs->relations.length.now; ++a)
    {
        struct qs_relation *const rel = qs->relations.data[a];
        for (b = 0; b < rel->Y.length; ++b)
            Y[rel->Y.data[b]] ^= X[a];
    }
}

void lanczos_mul_trans_MxN_Nx64(const qs_sheet *qs, const uint64_t *X, uint64_t *Y)
{
    assert(Y != X);
    for (qs_sm a = 0, b; a < qs->relations.length.now; ++a)
    {
        struct qs_relation *const rel = qs->relations.data[a];
        for (Y[a] = 0, b = 0; b < rel->Y.length; ++b)
            Y[a] ^= X[rel->Y.data[b]];
    }
}

void lanczos_mul_64xN_Nx64(const qs_sheet *qs, const uint64_t *X, const uint64_t *Y, uint64_t *Z, uint64_t *T)
{
    assert(X != Z && Y != Z);
    qs_sm a, b, c, d;
    memset(Z, 0, 256 * 8 * sizeof(*Z));
    memset(T, 0, 64 * sizeof(*T));
    for (a = 0; a < qs->relations.length.now; ++a)
    {
        const uint64_t tmp = X[a]; // read while writing ?!
        for (b = 0, c = 0; c < 64; c += 8, b += 256)
            Z[b + (tmp >> c & 0xff)] ^= Y[a];
    }
    for (a = 0; a < 8; ++a, ++T)
    {
        uint64_t tmp[8] = {0};
        for (b = 0; b < 256; ++b)
            if (b >> a & 1)
                for (c = d = 0; c < 8; ++c, d += 256)
                    tmp[c] ^= Z[b + d];
        for (b = 0, c = 0; b < 8; ++b, c += 8)
            T[c] = tmp[b];
    }
}

uint64_t lanczos_find_non_singular_sub(const uint64_t *t, const uint64_t *last_s, uint64_t *s, uint64_t last_dim, uint64_t *w)
{
    uint64_t i, j, dim, cols[64];
    uint64_t M[64][2], mask, *row_i, *row_j, m_0, m_1;
    for (i = 0; i < 64; ++i)
        M[i][0] = t[i], M[i][1] = (uint64_t)1 << i;
    mask = 0;
    for (i = 0; i < last_dim; ++i)
        mask |= (uint64_t)1 << (cols[63 - i] = last_s[i]);
    for (i = j = 0; i < 64; ++i)
        if (!(mask & ((uint64_t)1 << i)))
            cols[j++] = i;
    for (i = dim = 0; i < 64; ++i)
    {
        mask = (uint64_t)1 << (cols[i]);
        row_i = M[cols[i]];
        for (j = i; j < 64; ++j)
        {
            row_j = M[cols[j]];
            if (row_j[0] & mask)
            {
                m_0 = row_j[0];
                m_1 = row_j[1];
                row_j[0] = row_i[0];
                row_j[1] = row_i[1];
                row_i[0] = m_0;
                row_i[1] = m_1;
                break;
            }
        }
        if (j < 64)
        {
            for (j = 0; j < 64; ++j)
            {
                row_j = M[cols[j]];
                if (row_i != row_j && (row_j[0] & mask))
                    row_j[0] ^= row_i[0], row_j[1] ^= row_i[1];
            }
            s[dim++] = cols[i];
            continue;
        }
        for (j = i; j < 64; ++j)
        {
            row_j = M[cols[j]];
            if (row_j[1] & mask)
            {
                m_0 = row_j[0];
                m_1 = row_j[1];
                row_j[0] = row_i[0];
                row_j[1] = row_i[1];
                row_i[0] = m_0;
                row_i[1] = m_1;
                break;
            }
        }
        if (j == 64)
            return 0; // sub-matrix is not invertible

        for (j = 0; j < 64; ++j)
        {
            row_j = M[cols[j]];
            if (row_i != row_j && (row_j[1] & mask))
                row_j[0] ^= row_i[0], row_j[1] ^= row_i[1];
        }

        row_i[0] = row_i[1] = 0;
    }
    for (i = 0; i < 64; ++i)
        w[i] = M[i][1];
    mask = 0;
    for (i = 0; i < dim; ++i)
        mask |= (uint64_t)1 << s[i];
    for (i = 0; i < last_dim; ++i)
        mask |= (uint64_t)1 << last_s[i];
    dim *= mask == -(uint64_t)1;
    return dim;
}

void lanczos_mul_Nx64_64x64_acc(qs_sheet *qs, const uint64_t *X, const uint64_t *Y, uint64_t *Z, uint64_t *T)
{
    qs_sm a;
    uint64_t b, c, d, e;
    for (b = 0; b < 8; Y += 8, Z += 256, ++b)
        for (c = 0; c < 256; ++c)
            for (d = Z[c] = 0, e = c; e; e >>= 1, ++d)
                Z[c] ^= (e & 1) * Y[d];
    for (a = 0, Z -= 2048; a < qs->relations.length.now; ++a)
        for (c = d = 0; c < 64; c += 8, d += 256)
        {
            const uint64_t w = X[a];
            T[a] ^= Z[d + (w >> c & 0xff)];
        }
}

void lanczos_mul_64x64_64x64(const uint64_t *X, const uint64_t *Y, uint64_t *Z)
{
    uint64_t a, b, c, d, tmp[64];
    for (a = 0; a < 64; tmp[a++] = c)
    {
        for (b = 0, c = 0, d = X[a]; d; d >>= 1, ++b)
            c ^= (d & 1) * Y[b];
    }
    memcpy(Z, tmp, sizeof(tmp));
}

void lanczos_transpose_vector(qs_sheet *qs, const uint64_t *X, uint64_t **Y)
{
    qs_sm a; // Z will be zeroed automatically by the loop.
    uint64_t b, c, d, *Z;
    Z = memcpy(qs->mem.now, X, qs->relations.length.now * sizeof(*X));
    for (a = 0; a < qs->relations.length.now; ++a)
        for (b = 0, c = a >> 6, d = (uint64_t)1 << (a % 64); Z[a]; Z[a] >>= 1, ++b)
            Y[b][c] |= (Z[a] & 1) * d;
}

void lanczos_combine_cols(qs_sheet *qs, uint64_t *x, uint64_t *v, uint64_t *ax, uint64_t *av)
{
    qs_sm i, j, bit_pos, num_deps;
    uint64_t k, col, col_words;
    uint64_t mask, *mat_1[128], *mat_2[128], *tmp;
    num_deps = 64 << (v && av);
    col_words = (qs->relations.length.now + 63) / 64;
    for (i = 0; i < num_deps; ++i)
    {
        mat_1[i] = qs->mem.now;
        mat_2[i] = mat_1[i] + col_words;
        qs->mem.now = mat_2[i] + col_words;
    }
    lanczos_transpose_vector(qs, x, mat_1);
    lanczos_transpose_vector(qs, ax, mat_2);
    if (num_deps == 128)
    {
        lanczos_transpose_vector(qs, v, mat_1 + 64);
        lanczos_transpose_vector(qs, av, mat_2 + 64);
    }
    for (i = bit_pos = 0; i < num_deps && bit_pos < qs->relations.length.now; ++bit_pos)
    {
        mask = (uint64_t)1 << (bit_pos % 64);
        col = bit_pos / 64;
        for (j = i; j < num_deps; ++j)
            if (mat_2[j][col] & mask)
            {
                tmp = mat_1[i];
                mat_1[i] = mat_1[j];
                mat_1[j] = tmp;
                tmp = mat_2[i];
                mat_2[i] = mat_2[j];
                mat_2[j] = tmp;
                break;
            }
        if (j == num_deps)
            continue;
        for (++j; j < num_deps; ++j)
            if (mat_2[j][col] & mask)
                for (k = 0; k < col_words; ++k)
                {
                    mat_2[j][k] ^= mat_2[i][k];
                    mat_1[j][k] ^= mat_1[i][k];
                }
        ++i;
    }

    for (j = 0; j < qs->relations.length.now; ++j)
    {
        uint64_t word = 0;
        col = j / 64;
        mask = (uint64_t)1 << (j % 64);
        for (k = i; k < 64; ++k)
            if (mat_1[k][col] & mask)
                word |= (uint64_t)1 << k;
        x[j] = word;
    }
    char *open = (char *)mat_1[0], *close = qs->mem.now;
    qs->mem.now = memset(open, 0, close - open);
}

void lanczos_build_array(qs_sheet *qs, uint64_t **target, const size_t quantity, const size_t size)
{
    const char *mem_needs = (char *)qs->mem.now + quantity * size * sizeof(uint64_t);
    const char *mem_ends = (char *)qs->mem.now + qs->mem.bytes_allocated;
    assert(mem_needs < mem_ends);
    for (size_t i = 0; i < quantity; ++i)
        target[i] = qs->mem.now, qs->mem.now = mem_aligned(target[i] + size);
}

uint64_t *lanczos_block_worker(qs_sheet *qs)
{
    const qs_sm n_cols = qs->relations.length.now, v_size = n_cols > qs->base.length ? n_cols : qs->base.length;
    const uint64_t safe_size = qs->lanczos.safe_length;
    uint64_t *md[6], *xl[2], *sm[13], *tmp, *res, mask_0, mask_1, endless_guard = 1 << 11;
    qs_sm i, dim_0, dim_1;
    qs->mem.now = mem_aligned((uint64_t *)qs->mem.now + 1); // keep some padding.
    lanczos_build_array(qs, md, 6, safe_size);
    lanczos_build_array(qs, sm, 13, 64);
    lanczos_build_array(qs, xl, 2, safe_size < 2048 ? 2048 : safe_size);
    res = (*md) - 1; // simple "trick" to return mask + null_rows
    for (i = 0; i < 64; ++i)
        sm[12][i] = i;
    dim_0 = 0;
    dim_1 = 64;
    mask_1 = (uint64_t)-1;
    for (i = 0; i < qs->relations.length.now; ++i)
        md[1][i] = (uint64_t)rand_64();
    memcpy(md[0], md[1], v_size * sizeof(uint64_t));
    lanczos_mul_MxN_Nx64(qs, md[1], v_size, xl[1]);
    lanczos_mul_trans_MxN_Nx64(qs, xl[1], md[1]);
    memcpy(xl[0], md[1], v_size * sizeof(uint64_t));
    do
    {
        lanczos_mul_MxN_Nx64(qs, md[1], v_size, xl[1]);
        lanczos_mul_trans_MxN_Nx64(qs, xl[1], md[4]);
        lanczos_mul_64xN_Nx64(qs, md[1], md[4], xl[1], sm[3]);
        lanczos_mul_64xN_Nx64(qs, md[4], md[4], xl[1], sm[5]);
        for (i = 0; i < 64 && !(sm[3][i]); ++i)
            ;
        if (i != 64)
        {
            dim_0 = (qs_sm)lanczos_find_non_singular_sub(sm[3], sm[12], sm[11], dim_1, sm[0]);
            if (dim_0)
            {
                mask_0 = 0;
                for (i = 0; i < dim_0; ++i)
                    mask_0 |= (uint64_t)1 << sm[11][i];
                for (i = 0; i < 64; ++i)
                    sm[7][i] = (sm[5][i] & mask_0) ^ sm[3][i];
                lanczos_mul_64x64_64x64(sm[0], sm[7], sm[7]);
                for (i = 0; i < 64; ++i)
                    sm[7][i] ^= (uint64_t)1 << i;
                lanczos_mul_64x64_64x64(sm[1], sm[3], sm[8]);
                for (i = 0; i < 64; ++i)
                    sm[8][i] &= mask_0;
                lanczos_mul_64x64_64x64(sm[4], sm[1], sm[9]);
                for (i = 0; i < 64; ++i)
                    sm[9][i] ^= (uint64_t)1 << i;
                lanczos_mul_64x64_64x64(sm[2], sm[9], sm[9]);
                for (i = 0; i < 64; ++i)
                    sm[10][i] = ((sm[6][i] & mask_1) ^ sm[4][i]) & mask_0;
                lanczos_mul_64x64_64x64(sm[9], sm[10], sm[9]);
                for (i = 0; i < qs->relations.length.now; ++i)
                    md[4][i] &= mask_0;
                lanczos_mul_Nx64_64x64_acc(qs, md[1], sm[7], xl[1], md[4]);
                lanczos_mul_Nx64_64x64_acc(qs, md[3], sm[8], xl[1], md[4]);
                lanczos_mul_Nx64_64x64_acc(qs, md[2], sm[9], xl[1], md[4]);
                lanczos_mul_64xN_Nx64(qs, md[1], xl[0], xl[1], sm[7]);
                lanczos_mul_64x64_64x64(sm[0], sm[7], sm[7]);
                lanczos_mul_Nx64_64x64_acc(qs, md[1], sm[7], xl[1], md[0]);
                tmp = md[2], md[2] = md[3], md[3] = md[1], md[1] = md[4], md[4] = tmp;
                tmp = sm[2], sm[2] = sm[1], sm[1] = sm[0], sm[0] = tmp;
                tmp = sm[4], sm[4] = sm[3], sm[3] = tmp;
                tmp = sm[6], sm[6] = sm[5], sm[5] = tmp;
                memcpy(sm[12], sm[11], 64 * sizeof(uint64_t));
                mask_1 = mask_0;
                dim_1 = dim_0;
            }
        }
    } while (dim_0 && i != 64 && --endless_guard);

    dim_0 *= endless_guard != 0;
    *res = 0; // mask

    if (dim_0)
    {
        lanczos_mul_MxN_Nx64(qs, md[0], v_size, md[3]);
        lanczos_mul_MxN_Nx64(qs, md[1], v_size, md[2]);
        lanczos_combine_cols(qs, md[0], md[1], md[3], md[2]);
        lanczos_mul_MxN_Nx64(qs, md[0], v_size, md[1]);
        if (*md[1] == 0) // should hold (the buffer must contain only zero)
            if (memcmp(md[1], md[1] + 1, (v_size - 1) * sizeof(uint64_t)) == 0)
                for (i = 0; i < n_cols; *res |= (*md)[i++])
                    ;
    }
    char *open = (char *)md[*res != 0], *close = qs->mem.now;
    qs->mem.now = memset(open, 0, close - open);
    return res;
}

void lanczos_reduce_matrix(qs_sheet *qs)
{
    qs_sm a, b, c, row, col, reduced_rows = qs->base.length, *counts;
    counts = memset(qs->buffer[1], 0, qs->base.length * sizeof(*qs->buffer[1]));
    if (qs->sieve_again_perms)
        for (a = 0; a < qs->relations.length.now; ++a)
        {
            // "snapshot" pointers, so they can be restored if "sieve again" is fired.
            qs->lanczos.snapshot[a].relation = qs->relations.data[a];
            qs->lanczos.snapshot[a].y_length = qs->relations.data[a]->Y.length;
        }
    for (a = 0; a < qs->relations.length.now; ++a)
        for (b = 0; b < qs->relations.data[a]->Y.length; ++b)
            ++counts[qs->relations.data[a]->Y.data[b]];
    //
    do
    {
        row = reduced_rows;
        do
        {
            col = qs->relations.length.now;
            for (a = b = 0; a < qs->relations.length.now; ++a)
            {
                struct qs_relation *restrict const rel = qs->relations.data[a];
                for (c = 0; c < rel->Y.length && counts[rel->Y.data[c]] > 1; ++c)
                    ;
                if (c < rel->Y.length)
                    for (; rel->Y.length;)
                        --counts[rel->Y.data[--rel->Y.length]];
                else
                    qs->relations.data[b++] = qs->relations.data[a]; // relation is thrown.
            }
        } while (qs->relations.length.now = b, b != col);
        for (a = reduced_rows = 0; a < qs->base.length; reduced_rows += counts[a++] != 0)
            ;
        if (b = reduced_rows + 64, qs->relations.length.now > b)
        { // 64 extra rows
            for (a = b; a < qs->relations.length.now; ++a)
                for (struct qs_relation *restrict const rel = qs->relations.data[a]; rel->Y.length;)
                    --counts[rel->Y.data[--rel->Y.length]];
            qs->relations.length.now = b;
        }
    } while (row != reduced_rows);
}

uint64_t *lanczos_block(qs_sheet *qs)
{
    if (qs->n_bits == 1)
        return (uint64_t *)qs->mem.now; // nothing to solve when N = 1, return any zeroed buffer.

    uint64_t *res;
    qs_sm tries = 4, reduce_at;
    //
    if (qs->sieve_again_perms < 3)
        tries <<= 1; // 8
    if (qs->sieve_again_perms < 2)
        tries <<= 1; // 16 tries in desperation.
    reduce_at = tries >> 1;
    //
    if (qs->lanczos.safe_length < qs->relations.length.now)
        qs->lanczos.safe_length = qs->relations.length.now;
    if (qs->lanczos.safe_length < qs->base.length)
        qs->lanczos.safe_length = qs->base.length;
    qs->lanczos.safe_length += 64 - qs->lanczos.safe_length % 64;
    //
    do
    {
        if (tries == reduce_at) // 230-bit can need reduce
            lanczos_reduce_matrix(qs);
        // Try to find a subset of all exponent vectors such that
        // the sum of their exponent vectors is the zero vector.
        res = lanczos_block_worker(qs);
    } while (!*res && --tries);
    return res;
}

static inline void fac_display_verbose(fac_cint **ans);
static inline void fac_display_help(char *name);
int main()
{
//    freopen("input.txt", "r", stdin);
//    freopen("output.txt", "w", stdout);
    cint N;
    fac_params config = {0};
    char *n = calloc(100, 1); // the string to factor in base 10.
//    gets(n);
    scanf("%s", n);
    while (n[0] != '0')
    {
        const int bits = 64 + 4 * (int)strlen(n);
        cint_init_by_string(&N, bits, n, 10);      // init the number as a cint.
        fac_cint **answer = c_factor(&N, &config); // execute the routine.
        fac_display_verbose(answer);               // print answer.
        free(answer);                              // release answer memory.
        free(N.mem);                               // release number memory.
        free(n);
        n = calloc(100, 1);
//        gets(n);
        scanf("%s", n);
    }

    return 0;
}

static inline void fac_display_verbose(fac_cint **ans)
{
    char *str = fac_answer_to_string(ans);
    fputs(str, stdout);
    puts("");
    free(str);
}