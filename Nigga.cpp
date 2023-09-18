#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define Nigga_ ios::sync_with_stdio(false), cin.tie(0), cout.tie(0);
#define all(x) x.begin(), x.end()
//#define int long long
typedef long long ll;
const int MOD = 1e9 + 7;
const short dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
const short dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
const char dc[] = {'U', 'L', 'R', 'D'};
using namespace std;
using namespace __gnu_pbds;
//----------------------------------------------------------------------------------
template<typename K, typename V, typename Comp = less<K>>
using ordered_map = tree<K, V, Comp, rb_tree_tag, tree_order_statistics_node_update>;
template<typename K, typename Comp = less<K>>
using ordered_set = ordered_map<K, null_type, Comp>;

template<typename K, typename V, typename Comp = less_equal<K>>
using ordered_multimap = tree<K, V, Comp, rb_tree_tag, tree_order_statistics_node_update>;
template<typename K, typename Comp = less_equal<K>>
using ordered_multiset = ordered_multimap<K, null_type, Comp>;
//----------------------------------------------------------------------------------
template<typename T> using min_queue = priority_queue<T, vector<T>, greater<>>;

template<typename T> struct nT {
    T mod;
    vector <T> fac;
    vector<int> Sieve;

    explicit nT(T m = 1e9 + 7) : mod(m) {}
    void buildFac(int numberOfFactorial){
        fac.resize(numberOfFactorial + 1);
        fac[0] = 1;
        for (int i = 1; i <= numberOfFactorial; i++)
            fac[i] = ((__int128) fac[i - 1] * i) % mod;
    }
    void buildSieve(int sieve){
        Sieve.resize(sieve + 1, 0);
        for (int i = 1; i <= sieve; i++){
            for(int j = i; j <= sieve; j += i)
                Sieve[j]++;
        }

    }
    bool isPrime(ll num) {
        if (num == 2) return true;
        if (num % 2 == 0 || num < 2) return false;
        for (ll i = 3; i * i <= num; i += 2)
            if (num % i == 0)
                return false;
        return true;
    }

    T fastPower(T base, T power) {
        if (power < 0) return 0;
        if (power == 0) return 1;
        if (power == 1) return base;
        T temp = fastPower(base, power / 2);
        if (power & 1) return ((__int128) temp * temp * base) % mod;
        return ((__int128) temp * temp) % mod;
    }

    void moveOneStep(T &a, T &b, T q) {
        T next = a - b * q;
        a = b;
        b = next;
    }

    T eGcd(T r0, T r1, T &x0, T &y0) {
        T x1 = y0 = 0, y1 = x0 = 1;
        while (r1 > 0) {
            T q = r0 / r1;
            moveOneStep(r0, r1, q);
            moveOneStep(x0, x1, q);
            moveOneStep(y0, y1, q);
        }
        return r0;
    }

    T modularInverse(T num) {
        T x, y, g = eGcd(num, mod, x, y);
        assert(g == 1);
        return ((__int128) x + mod) % mod;
    }

    T nCr(T n, T r) {
        if (r > n) return 0;
        return ((__int128) fac[n] * modularInverse(((__int128) fac[n - r] * fac[r]) % mod)) % mod;
    }

    T nPr(T n, T r) {
        if (r > n) return 0;
        return ((__int128) fac[n] * modularInverse(fac[n - r])) % mod;
    }
};


class segtree {
    struct node{
        int v;
        bool f = false;
        int e = 0;
        node *l, *r;
        explicit node(int v = 1e7, node *l = nullptr, node *r = nullptr) : v(v), l(l), r(r) { }
    };
    void update(node *x) {
        if(x && x->f) {
            x->f = false;
            x->v += x->e;
            if(x->l)
                x->l->f = true, x->l->e += x->e;
            if(x->r)
                x->r->f = true, x->r->e += x->e;
            x->e = 0;
        }
    }
    void merge(node *x) {
        update(x), update(x->l), update(x->r);
        x->v = min(x->l->v, x->r->v);
    }
    node *build(int lx, int rx) {
        if(lx == rx)
            return new node(arr[lx]);

        int m = (lx + rx) >> 1;
        node *l = build(lx, m), *r = build(m + 1, rx), *x = new node(1e9, l, r);
        merge(x);
        return x;
    }
    int q(node *x, int lx, int rx, int l, int r) {
        update(x);
        if(lx > r || l > rx)
            return 1e9;
        if(lx >= l && rx <= r)
            return x->v;
        int m = (lx + rx) >> 1;
        return min(q(x->l, lx, m, l, r), q(x->r, m + 1, rx, l, r));
    }
    void setRange(node *x, int lx, int rx, int l, int r, int v) {
        update(x);
        if(lx > r || l > rx)
            return;
        if(lx >= l && rx <= r) {
            x->f = true;
            x->e += v;
            update(x);
            return;
        }
        int m = (lx + rx) >> 1;
        setRange(x->l, lx, m, l, r, v);
        setRange(x->r, m + 1, rx, l, r, v);
        merge(x);
    }
    int size;
    node *root = nullptr;
    vector<int> &arr;
    void del(node *x) {
        if(x) {
            del(x->l);
            del(x->r);
            delete x;
        }
    }
public:
    explicit segtree(vector<int> &arr) : arr(arr), size((int)arr.size() - 1) {
        root = build(0, size);
    }
    ~segtree() {
        del(root);
    }
    int Q(int l, int r) {
        if(l <= r)
            return q(root, 0, size, l, r);
        return min(q(root, 0, size, 0, r), q(root, 0, size, l, size));
    }
    void setRange(int l, int r, int v) {
        if(l <= r)
            setRange(root, 0, size, l, r, v);
        else
            setRange(root, 0, size, 0, r, v), setRange(root, 0, size, l, size, v);
    }
};

void go() {

}

int32_t main() {
    Nigga_
    cout << fixed << setprecision(10);
    //freopen("output.txt", "w", stdout); freopen("input.txt", "r", stdin);
    int test = 1; //cin >> test;
    while (test-- > 0){
        go();
    }
    return 0;
}