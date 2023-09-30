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
        for (int i = 2; i <= sieve; i++){
            if(!Sieve[i]) {
                Sieve[i] = i;
                for(int j = i * i; j <= sieve; j += i)
                    Sieve[j] = i;
            }
        }

    }
    bool isPrime(ll num) {
        if(num < 2) return false;
        if(num < 4) return true;
        if(num % 2 == 0 || num % 3 == 0) return false;
        for (ll i = 5; i * i <= num; i += 6)
            if (num % i == 0 || num % (i + 2) == 0)
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
    ll get(node *x, int lx, int rx, int l, int r) {
        if(lx > r || l > rx)
            return 0;
        if(lx >= l && rx <= r)
            return x->v;
        int m = (lx + rx) >> 1;
        return get(x->l, lx, m, l, r) + get(x->r, m + 1, rx, l, r);
    }
    void set(node *x, int lx, int rx, int i) {
        if(lx == rx)
            return void(x->v = arr[lx]);
        int m = (lx + rx) >> 1;
        i <= m? set(x->l, lx, m, i): set(x->r, m + 1, rx, i);
        merge(x);
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
        return get(root, 1, size, l, r);
    }
};

struct sparse{
    int Log, n;
    vector<vector<int>> table;
    vector<int> LOG;
    int merge(int &x, int &y) {
        return max(x, y);
    }
    explicit sparse(vector<int> &arr) : n((int)arr.size()), Log((int)log2(arr.size()) + 1) {
        table.resize(Log, vector<int>(n));
        table[0] = arr;
        LOG.resize(n + 1);
        for(int i = 2; i <= n; i++)
            LOG[i] = LOG[i >> 1] + 1;
        for(int l = 1; l < Log; l++) {
            for(int i = 0; i + (1 << (l - 1)) < n; i++) {
                table[l][i] = merge(table[l - 1][i], table[l - 1][i + (1 << (l - 1))]);
            }
        }
    }
    int ans(int l, int r) {
        if(l > r)
            return 0;
        int len = LOG[r - l + 1];
        return merge(table[len][l], table[len][r - (1 << len) + 1]);
    }
};

class Hash{
    using pi = pair<int, int>;
    const int b1 = 31, b2 = 69, mod = 1e9 + 7;
    vector<int> Pb1, Pb2;
    int mul(int x, int y) {
        x = (x % mod + mod) % mod;
        y = (y % mod + mod) % mod;
        return int(1LL * x * y % mod);
    }
    int plus(int x, int y) {
        x = (x % mod + mod) % mod;
        y = (y % mod + mod) % mod;
        return int((0LL + x + y) % mod);
    }
    int fastPower(int b, int p) {
        if(p == 0) return 1;
        long long res = fastPower(b, p >> 1);
        return int(res * res % mod * (p & 1? b: 1) % mod);
    }
    const int b1I = fastPower(b1, mod - 2), b2I = fastPower(b2, mod - 2);
public:
    Hash(int maxSize) {
        Pb1.resize(maxSize, 1);
        Pb2.resize(maxSize, 1);
        for(int i = 1; i < maxSize; i++) {
            Pb1[i] = int(1LL * Pb1[i - 1] * b1 % mod);
            Pb2[i] = int(1LL * Pb2[i - 1] * b2 % mod);
        }
    }
    pi shiftL(pi codex) {
        return {mul(codex.first, b1), mul(codex.second, b2)};
    }
    pi shiftR(pi codex) {
        return {mul(codex.first, b1I), mul(codex.second, b2I)};
    }
    pi add(pi codex, int at, int val) {
        return {plus(mul(val, Pb1[at]), codex.first),
                plus(mul(val, Pb2[at]), codex.second)};
    }
    pi remove(pi codex, int at, int val) {
        return {plus(codex.first, -mul(Pb1[at], val)),
                plus(codex.second, -mul(Pb2[at], val))};
    }
    pi code{};
    int size{};
    void push_back(int x) {
        code = add(code, size++, x);
    }
    void push_front(int x) {
        code = shiftL(code);
        code = add(code, 0, x);
        size++;
    }
    void remove_back(int x) {
        code = remove(code, --size, x);
    }
    void remove_front(int x) {
        code = remove(code, 0, x);
        code = shiftR(code);
        size--;
    }
    void clear() {
        code = {}, size = 0;
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
