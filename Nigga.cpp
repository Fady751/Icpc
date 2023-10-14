#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <utility>
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

namespace numberTheory {
    using Type = int;
    Type mod = 1e9 + 7;
    vector <Type> fac;
    vector<int> sieve;

    void buildFac(int n){
        fac.resize(n + 1);
        fac[0] = 1;
        for (int i = 1; i <= n; i++)
            fac[i] = Type((__int128(fac[i - 1]) * i) % mod);
    }
    void buildSieve(int n){
        sieve.resize(n + 1);
        for (int i = 2; i <= n; i++){
            if(!sieve[i]) {
                sieve[i] = i;
                for(ll j = ll(i) * i; j <= n; j += i)
                    sieve[j] = i;
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

    Type fastPower(Type base, Type power) {
        if (power < 0) return 0;
        if (power == 0) return 1;
        Type temp = fastPower(base, power >> 1);
        return Type((__int128(temp) * temp * (power & 1? base: 1)) % mod);
    }

    void moveOneStep(Type &a, Type &b, Type q) {
        Type next = a - b * q;
        a = b;
        b = next;
    }

    Type eGcd(Type r0, Type r1, Type &x0, Type &y0) {
        Type x1 = y0 = 0, y1 = x0 = 1;
        while (r1 > 0) {
            Type q = r0 / r1;
            moveOneStep(r0, r1, q);
            moveOneStep(x0, x1, q);
            moveOneStep(y0, y1, q);
        }
        return r0;
    }

    Type modularInverse(Type num) {
        Type x, y, g = eGcd(num, mod, x, y);
        assert(g == 1);
        return (x + mod) % mod;
    }

    Type nCr(Type n, Type r) {
        if (r > n) return 0;
        return Type((__int128(fac[n]) * modularInverse(Type((__int128(fac[n - r]) * fac[r]) % mod))) % mod);
    }

    Type nPr(Type n, Type r) {
        if (r > n) return 0;
        return Type((__int128(fac[n]) * modularInverse(fac[n - r])) % mod);
    }
}
//using namespace numberTheory;

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
    static void merge(node *x) {
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
    ll ans(int l, int r) {
        return get(root, 1, size, l, r);
    }
};

struct sparse{
    int Log, n;
    vector<vector<int>> table;
    vector<int> LOG;
    static int merge(int &x, int &y) {
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

namespace RollingHash {
    int b1 = 31, b2 = 69, mod = 1e9 + 7, b1I = 129032259, b2I = 579710149;
    vector<int> Pb1, Pb2;
    using pi = pair<int, int>;

    void pre(unsigned maxSize) {
        Pb1 = Pb2 = vector<int>(maxSize + 1, 1);
        for (int i = 1; i <= maxSize; i++) {
            Pb1[i] = int(1LL * Pb1[i - 1] * b1 % mod);
            Pb2[i] = int(1LL * Pb2[i - 1] * b2 % mod);
        }
    }
    class Hash {
    public:
        pi code;
        int size;
        explicit Hash(pi x = {}, int sz = {}) : code(std::move(x)), size(sz) { }

        void push_back(int x) {
            code.first = int((code.first + 1LL * Pb1[size] * x) % mod);
            code.second = int((code.second + 1LL * Pb2[size++] * x) % mod);
        }
        void push_front(int x) {
            code.first = int((1LL * code.first * b1 + x) % mod);
            code.second = int((1LL * code.second * b2 + x) % mod);
            size++;
        }
        void pop_back(int x) {
            code.first = int((code.first - 1LL * Pb1[--size] * x % mod + mod) % mod);
            code.second = int((code.second - 1LL * Pb2[size] * x % mod + mod) % mod);
        }
        void pop_front(int x) {
            code.first = int((1LL * (code.first - x + mod) * b1I) % mod);
            code.second = int((1LL * (code.second - x + mod) * b2I) % mod);
            size--;
        }
        void clear() {
            code = {}, size = 0;
        }

        Hash operator+(const Hash &o) const {//based on push_front (... 2 1 0) + (... 2 1 0) => "hell" + "o" = "hello"
            return Hash({int((1LL * code.first * Pb1[o.size] + o.code.first) % mod),
                         int((1LL * code.second * Pb2[o.size] + o.code.second) % mod)}
                    , size + o.size);
        }
        Hash operator-(const Hash &o) const {//based on push_front (... 3 2 1 0) - (... 2 1 0) => "hello" - "hell" = "o"
            assert(size >= o.size);
            int m = size - o.size;
            return Hash({int((code.first - 1LL * o.code.first * Pb1[m] % mod + mod) % mod),
                         int((code.second - 1LL * o.code.second * Pb2[m] % mod + mod) % mod)}
                    , m);
        }
        bool operator<(const Hash &o) const {
            if (code == o.code) return size < o.size;
            return code < o.code;
        }
        bool operator==(const Hash &o) const {
            return size == o.size && code == o.code;
        }
        bool operator!=(const Hash &o) const {
            return size != o.size || code != o.code;
        }
    };
    template<typename T>
    Hash getHash(T &s) {
        Hash c;
        for(auto &i : s)
            c.push_front(i);
        return c;
    }
    template<typename T>
    vector<Hash> getPreHash(T &s) {
        vector<Hash> arr;
        arr.reserve(s.size());
        Hash c;
        for(auto &i : s) {
            c.push_front(i);
            arr.push_back(c);
        }
        return arr;
    }
    Hash getRange(vector<Hash> &pre, int l, int r) {
        return l == 0? pre[r]: pre[r] - pre[l - 1];
    }
}
//using namespace RollingHash;

namespace Trie{
    struct node{
        int cnt = 0;
        node *mp[2];
        node(){for(auto &i: mp)i=nullptr;}
    };
    #define Log 30
    node *root = nullptr;
    void insert(int num, node *x = root, int i = Log) {
        x->cnt++;
        if(i == -1)
            return;
        bool l = num & (1 << i);
        if(!x->mp[l])
            x->mp[l] = new node();
        insert(num, x->mp[l], i - 1);
    }
    int Max(int num, node *x = root, int i = Log) {
        if(i == -1 || !x)
            return 0;
        bool l = !(num & (1 << i));

        if(x->mp[l] && x->mp[l]->cnt)
            return (1 << i) * l + Max(num, x->mp[l], i - 1);
        return (1 << i) * !l + Max(num, x->mp[!l], i - 1);
    }
    int Min(int num, node *x = root, int i = Log) {
        if(i == -1 || !x)
            return 0;
        bool l = (num & (1 << i));

        if(x->mp[l] && x->mp[l]->cnt)
            return (1 << i) * l + Min(num, x->mp[l], i - 1);
        return (1 << i) * !l + Min(num, x->mp[!l], i - 1);
    }
    void clear(node *x = root) {
        if(!x) return;
        for(auto &i : x->mp)
            clear(i);
        delete x;
    }
}
//using namespace Trie;

void solve() {

}

int32_t main() {
    Nigga_
    cout << fixed << setprecision(10);
    //freopen("output.txt", "w", stdout); freopen("input.txt", "r", stdin);
    int test = 1;
    //cin >> test;
    while(test-- > 0) {
        solve();
    }
    cerr << clock() / 1000.0 << " Secs";
    return 0;
}
