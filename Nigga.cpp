#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define Nigga_ ios::sync_with_stdio(false), cin.tie(0), cout.tie(0);
#define all(x) x.begin(), x.end()
//#define int long long
typedef long long ll;
const int MOD = 1e9 + 7, inf = (1 << 30) - 1;
const ll INF = (1LL << 62) - 1;
const short dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
const short dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
const char dc[] = {'U', 'L', 'R', 'D'};
using namespace std;
using namespace __gnu_pbds;
//---------------------------------------------------------------------------------
template<typename K, typename V, typename Comp = less<K>>
using ordered_map = tree<K, V, Comp, rb_tree_tag, tree_order_statistics_node_update>;
template<typename K, typename Comp = less<K>>
using ordered_set = ordered_map<K, null_type, Comp>;

template<typename K, typename V, typename Comp = less_equal<K>>
using ordered_multimap = tree<K, V, Comp, rb_tree_tag, tree_order_statistics_node_update>;
template<typename K, typename Comp = less_equal<K>>
using ordered_multiset = ordered_multimap<K, null_type, Comp>;
//---------------------------------------------------------------------------------
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

class SegmentTree {
    struct node {
        node *l, *r;
        ll v;
        explicit node(ll v = {}, node *l = nullptr, node *r = nullptr)
                : v(v), r(r), l(l) {
        }
    };
    vector<int> &arr;
    node *root = nullptr;
    int size;
    void merge(node *x) {
        x->v = x->l->v + x->r->v;
    }
    node *build(int lx, int rx) {
        if(lx == rx)
            return new node(arr[lx]);

        int m = (lx + rx) >> 1;
        node *l = build(lx, m),
                *r = build(m + 1, rx),
                *x = new node({}, l, r);
        merge(x);
        return x;
    }
    ll get(node *x, int lx, int rx, int l, int r, int v) {
        if(lx > r || l > rx)
            return 0;
        if(lx >= l && rx <= r)
            return x->v;
        int m = (lx + rx) >> 1;
        return get(x->l, lx, m, l, r, v) + get(x->r, m + 1, rx, l, r, v);
    }
    void set(node *x, int lx, int rx, int i) {
        if(lx == rx)
            return void(x->v = arr[lx]);
        int m = (lx + rx) >> 1;
        i <= m? set(x->l, lx, m, i): set(x->r, m + 1, rx, i);
    }
    void del(node *x) {
        if(x){
            del(x->l);
            del(x->r);
            delete x;
        }
    }
public://based index 1
    explicit SegmentTree(vector<int> &arr) : size((int)arr.size() - 1), arr(arr) {
        root = build(1, size);
    }
    ~SegmentTree(){
        del(root);
    }
    void set(int i, int v) {
        arr[i] = v;
        set(root, 1, size, i);
    }
    ll ans(int l, int r, int v) {
        return get(root, 1, size, l, r, v);
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
