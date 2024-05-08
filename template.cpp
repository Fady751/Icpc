#include <bits/stdc++.h>
#include <utility>

#define all(x) x.begin(), x.end()
#define fun(return, ...) function<return(__VA_ARGS__)>
//#define int long long

//typedef long long ll;
const int MOD = 1e9 + 7, inf = (1 << 30) - 1;
const int64_t INF = (1LL << 62) - 1;
const short dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
const short dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
const char dc[] = {'U', 'L', 'R', 'D'};
std::mt19937 rnd(time(nullptr)); //uniform_int_distribution<ll>(l, r)(rnd);
using namespace std;

template<class U, typename T>
U& operator >> (U &input, vector<T> &x){
    x.clear();
    T element;
    while(input >> element) {
        x.push_back(element);
        if(input.peek() == '\n') break;
    }
    return input;
}

//---------------------------------------------------------------------------------
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace __gnu_pbds;

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
    using type = int;
    using cast = long long;
    type mod = static_cast<type>(1e9) + 7;

    vector<type> fac;
    void buildFac(int n){
        fac.resize(n + 1);
        fac[0] = 1;
        for (int i = 1; i <= n; i++)
            fac[i] = static_cast<type>((static_cast<cast>(fac[i - 1]) * i) % mod);
    }

    vector<int> sieve;
    void buildSieve(int n){
        sieve.resize(n + 1);
        for (int i = 2; i <= n; i++){
            if(!sieve[i]) {
                sieve[i] = i;
                for(int64_t j = int64_t(i) * i; j <= n; j += i) if(!sieve[j])
                    sieve[j] = i;
            }
        }
    }
    vector<array<int, 2>> getFac(int _n) {
        if(_n < 2) return {};
        vector<array<int, 2>> _res;
        int _p = sieve[_n];
        while(_p > 1) {
            int _c = 0;
            while(_n % _p == 0)
                _n /= _p, _c++;
            _res.push_back({_p, _c});
            _p = sieve[_n];
        }
        return _res;
    }
    vector<int> getDivisors(int _n) {
        auto _fac = getFac(_n);
        vector<int> res;
        function<void(int, int)> slv = [&](int i, int cur) -> void {
            if (i == _fac.size()) {
                res.push_back(cur);
                return;
            }
            for (int _ = 0; _ <= _fac[i][1]; ++_) {
                slv(i + 1, cur);
                cur *= _fac[i][0];
            }
        };
        slv(0, 1);
        return res;
    }

    bool isPrime(int64_t num) {
        if(num < 2) return false;
        if(num < 4) return true;
        if(num % 2 == 0 || num % 3 == 0) return false;
        for (int64_t i = 5; i * i <= num; i += 6)
            if (num % i == 0 || num % (i + 2) == 0)
                return false;
        return true;
    }

    type fastPower(type base, type power, type m = mod) {
        if (power < 0) return 0;
        if (power == 0) return 1;
        type temp = fastPower(base, power >> 1, m);
        return static_cast<type>((static_cast<cast>(temp) * temp * (power & 1 ? base : 1)) % m);
    }

    void moveOneStep(type &a, type &b, type q) {
        type next = a - b * q;
        a = b;
        b = next;
    }

    type eGcd(type r0, type r1, type &x0, type &y0) {
        type x1 = y0 = 0, y1 = x0 = 1;
        while (r1 > 0) {
            type q = r0 / r1;
            moveOneStep(r0, r1, q);
            moveOneStep(x0, x1, q);
            moveOneStep(y0, y1, q);
        }
        return r0;
    }

    type modularInverse(type num, type m = mod) {
        type x0 = 1, x1 = 0, q, t;
        while(m) {
            q = num / m;
            num -= q * m, t = num, num = m, m = t;
            x0 -= q * x1, t = x0, x0 = x1, x1 = t;
        }
        assert(num == 1);
        return (x0 + mod) % mod;
    }

    type nCr(type n, type r) {
        if (r > n) return 0;
        return static_cast<type>((static_cast<cast>(fac[n]) * modularInverse(static_cast<type>((static_cast<cast>(fac[n - r]) * fac[r]) % mod))) % mod);
    }

    type nPr(type n, type r) {
        if (r > n) return 0;
        return static_cast<type>((static_cast<cast>(fac[n]) * modularInverse(fac[n - r])) % mod);
    }
    template<typename T>
    inline T lowBit(T x) {return x&-x;}
}
//using namespace numberTheory;

template<class T = long long, class U = int>
class SegTree {
    struct node {
        node *l, *r;
        T v{}, E{};
        explicit node() : l(nullptr), r(nullptr) { }
        void build() {
            if(!l) l = new node(), r = new node();
        }
    } *root;
    int size;
    inline static void merge(node *x) {
        x->v = x->l->v + x->r->v;
    }
    inline static T merge(const T &v1, const T &v2) {
        return v1 + v2;
    }
    inline static void edit(node *x, const int &lx, const int &rx) {
        if(x->E) {
            if(x->l) x->l->E += x->E;
            if(x->r) x->r->E += x->E;
            x->v += x->E * (rx - lx + 1);
            x->E = 0;
        }
    }

    void build(node *x, int lx, int rx, vector<U> &arr) {
        if(lx == rx) return void(x->v = arr[lx]);
        x->build();
        int m = (lx + rx) >> 1;
        build(x->l, lx, m, arr);
        build(x->r, m + 1, rx, arr);
        merge(x);
    }

    T get(node *x, int lx, int rx, int l, int r) {
        if(lx != rx) x->build();
        edit(x, lx, rx);
        if(lx > r || l > rx) return 0;
        if(lx >= l && rx <= r) return x->v;
        int m = (lx + rx) >> 1;
        return merge(get(x->l, lx, m, l, r), get(x->r, m + 1, rx, l, r));
    }
    void set(node *x, int lx, int rx, int i, T val) {
        if(lx != rx) x->build();
        edit(x, lx, rx);
        if (i < lx || i > rx) return;
        if(lx == rx) return void(x->v = val);
        int m = (lx + rx) >> 1;
        set(x->l, lx, m, i, val), set(x->r, m + 1, rx, i, val);
        merge(x);
    }
    void setRange(node *x, int lx, int rx, int l, int r, T val) {
        if(lx != rx) x->build();
        edit(x, lx, rx);
        if(lx > r || l > rx) return;
        if(lx >= l && rx <= r) return x->E = val, edit(x, lx, rx);
        int m = (lx + rx) >> 1;
        setRange(x->l, lx, m, l, r, val), setRange(x->r, m + 1, rx, l, r, val);
        merge(x);
    }
    void del(node *x) {
        if(x){
            del(x->l), del(x->r);
            delete x;
        }
    }
public://based index 0
    explicit SegTree(int n) : size(n), root(new node()) { }

    explicit SegTree(vector<U> &arr) : size(arr.size() - 1), root(new node()) {
        build(root, 0, size, arr);
    }
    ~SegTree(){
        del(root);
    }
    void set(int i, T v) {
        set(root, 0, size, i, v);
    }
    T get(int l, int r) {
        return get(root, 0, size, l, r);
    }
    T operator[](int i) {
        return get(i, i);
    }
    void plusRange(int l, int r, T val) {
        setRange(root, 0, size, l, r, val);
    }
};

template<class info = int64_t, info defaultVal = info{}>
class segmentTree {
    struct node {
        node *l, *r;
        info v;
        explicit node() : l(nullptr), r(nullptr), v(defaultVal) { }
        void create() {
            if(!l) l = new node(), r = new node();
        }
    } *root;
    int size;
    inline void _merge(node *x) {
        x->v = merge(x->l->v, x->r->v);
    }

    template<class U>
    void build(node *x, int lx, int rx, vector<U> &arr) {
        if(lx == rx) return void(x->v = arr[lx]);
        x->create();
        int m = (lx + rx) >> 1;
        build(x->l, lx, m, arr);
        build(x->r, m + 1, rx, arr);
        _merge(x);
    }

    info get(node *x, int lx, int rx, int l, int r) {
        if(lx != rx) x->create();
        if(lx > r || l > rx) return defaultVal;
        if(lx >= l && rx <= r) return x->v;
        int m = (lx + rx) >> 1;
        return merge(get(x->l, lx, m, l, r), get(x->r, m + 1, rx, l, r));
    }
    void set(node *x, int lx, int rx, int i, info val) {
        if(lx != rx) x->create();
        if (i < lx || i > rx) return;
        if(lx == rx) return void(x->v = val);
        int m = (lx + rx) >> 1;
        set(x->l, lx, m, i, val), set(x->r, m + 1, rx, i, val);
        _merge(x);
    }
    void del(node *x) {
        if(x){
            del(x->l), del(x->r);
            delete x;
        }
    }
    function<info(const info &, const info &)> merge;
public://0-based
    explicit segmentTree(int n = 1000000000, function<info(const info &, const info &)> _merge = [](const info &v1, const info &v2){return v1 + v2;}) : size(n), root(new node()), merge(std::move(_merge)) { }

    template<class U>
    explicit segmentTree(vector<U> &arr, function<info(const info &, const info &)> _merge = [](const info &v1, const info &v2){return v1 + v2;}) : size(arr.size() - 1), root(new node()), merge(std::move(_merge)) {
        build(root, 0, size, arr);
    }
    ~segmentTree(){
        del(root);
    }
    void set(int i, info v) {
        set(root, 0, size, i, v);
    }
    info get(int l, int r) {
        return get(root, 0, size, l, r);
    }
    info operator[](int i) {
        return get(root, 0, size, i, i);
    }
    void clear() {
        del(root);
        root = new node();
    }
};

template<typename T>
struct sparse{
    int Log, n;
    vector<vector<T>> table;
    static T merge(T &x, T &y) {
        return __gcd(x, y);
    }
    explicit sparse(vector<T> &arr) : n((int)arr.size()), Log(__lg(arr.size()) + 1) {
        table.resize(Log, vector<T>(n));
        table[0] = arr;
        for(int l = 1; l < Log; l++) {
            for(int i = 0; i + (1 << (l - 1)) < n; i++) {
                table[l][i] = merge(table[l - 1][i], table[l - 1][i + (1 << (l - 1))]);
            }
        }
    }
    T ans(int l, int r) {
        if(l > r)
            return {};
        int len = __lg(r - l + 1);
        return merge(table[len][l], table[len][r - (1 << len) + 1]);
    }
};

namespace RollingHash {
    int b1 = 31, b2 = 69, mod = 1e9 + 7, b1I = 129032259, b2I = 579710149;
    vector<int> Pb1, Pb2, inv1, inv2;
    using pi = pair<int, int>;

    void pre(unsigned maxSize) {
        inv1 = inv2 = Pb1 = Pb2 = vector<int>(maxSize + 1, 1);
        Pb1[1] = b1, Pb2[1] = b2, inv1[1] = b1I, inv2[1] = b2I;
        for (int i = 2; i <= maxSize; i++) {
            Pb1[i] = int(1LL * Pb1[i - 1] * b1 % mod);
            Pb2[i] = int(1LL * Pb2[i - 1] * b2 % mod);
            inv1[i] = int(1LL * inv1[i - 1] * b1I % mod);
            inv2[i] = int(1LL * inv2[i - 1] * b2I % mod);
        }
    }
    class Hash {
    public:
        pi code;
        int size;
        explicit Hash(pi x = {}, int sz = {}) : code(std::move(x)), size(sz) { }

        template<class T>
        Hash(const T s) : size(0) {
            for(const auto x : s) push_front(x);
        }

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
            if (size == o.size) return code < o.code;
            return size < o.size;
        }
        bool operator==(const Hash &o) const {
            return size == o.size && code == o.code;
        }
        bool operator!=(const Hash &o) const {
            return size != o.size || code != o.code;
        }
    };

    class HashRange {
    public:
        vector<Hash> pre, invPre;

        template<class T>
        HashRange(const T &s) {
            pre.reserve(s.size());
            invPre.reserve(s.size());
            Hash c, c1;
            for(auto &i : s) {
                c.push_front(i);
                c1.push_back(i);
                pre.push_back(c);
                invPre.push_back(c1);
            }
        }
        Hash get(int l, int r) {
            return l == 0? pre[r]: pre[r] - pre[l - 1];
        }
        Hash getInv(int l, int r) {
            return l == 0? invPre[r]: Hash({
                   (invPre[r].code.first - invPre[l - 1].code.first + mod) % mod * 1LL * inv1[invPre[l - 1].size] % mod,
                   (invPre[r].code.second - invPre[l - 1].code.second + mod) % mod * 1LL * inv2[invPre[l - 1].size] % mod
           }, r - l + 1);
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
    Hash getInvHash(T &s) {
        Hash c;
        for(auto &i : s)
            c.push_back(i);
        return c;
    }
}
//using namespace RollingHash;

namespace Trie{
    struct node{
        int cnt = 0;
        node *mp[2]{};
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

template<class T = long long>
struct BIT { //1-based
    vector<T> tree;
    explicit BIT(int size = 1e6) {
        tree.resize(size + 1);
    }

    void update(int i, T val) {
        assert(i > 0);
        while (i < tree.size()) {
            tree[i] += val;
            i += (i & -i);
        }
    }

    T query(int i) {
        T sum = 0;
        while (i > 0) {
            sum += tree[i];
            i -= (i & -i);
        }
        return sum;
    }

    T rangeQuery(int l, int r) {
        return query(r) - query(l - 1);
    }
};

class DSU {
    vector<int> p;
public: //1-based
    explicit DSU(int _n) : p(_n + 1, -1) { }
    int find(int i) {
        return p[i] < 0? i: p[i] = find(p[i]);
    }
    bool merge(int u, int v) {
        u = find(u);
        v = find(v);
        if(u == v)
            return false;
        if(p[u] < p[v]) swap(u, v);
        p[v] += p[u];
        p[u] = v;
        return true;
    }
    int size(int i) {
        return -p[find(i)];
    }
    bool same(int u, int v) {
        return find(u) == find(v);
    }
};

template<class T, class cast>
class Mint {
public:
    Mint() : num() { }
    template<typename U>
    Mint(const U &x) : num{nrm(x)} { }

    const T& operator()() const { return num; }
    Mint operator -() const {return -num;}
    Mint& operator --() {num = nrm(num - 1); return *this;}
    Mint& operator ++() {num = nrm(num + 1); return *this;}
    Mint operator --(int) {Mint res = *this; num = nrm(num - 1); return res;}
    Mint operator ++(int) {Mint res = *this; num = nrm(num + 1); return res;}
    bool operator <(const Mint &s) const {return num < s.num;}
    template<class U> operator U() const { return static_cast<U>(num); }
    bool operator ==(const Mint &s) const {return num == s.num;}
    template<typename U> bool operator ==(const U s) const {return num == nrm(s);}
    template<typename U> friend bool operator ==(const U s, const Mint &f) {return f.num == nrm(s);}
    bool operator !=(const Mint &s) const {return num != s.num;}
    template<typename U> bool operator !=(const U s) const {return num != nrm(s);}
    template<typename U> friend bool operator !=(const U s, const Mint &f) {return f.num != nrm(s);}

    // +++
    template<typename U> Mint operator + (const U s) const { return num + s; }
    template<typename U> friend Mint operator + (const U f, const Mint &s) { return f + s.num; }
    Mint operator + (const Mint &s) const { return num + s.num; }
    template<typename U>
    Mint& operator += (const U s)  { num = nrm(num + s); return *this; }
    Mint& operator += (const Mint &s)  { num = nrm(num + s.num); return *this; }
    template<typename U>
    friend U& operator += (U &s, const Mint &f)  { s = nrm(f.num + s); return s; }

    // ---
    template<typename U> Mint operator - (const U s) const { return num - s; }
    template<typename U> friend Mint operator - (const U f, const Mint &s) { return f - s.num; }
    Mint operator - (const Mint &s) const { return num - s.num; }
    template<typename U>
    Mint& operator -= (const U s)  { num = nrm(num - s); return *this; }
    Mint& operator -= (const Mint &s)  { num = nrm(num - s.num); return *this; }
    template<typename U>
    friend U& operator -= (U &s, const Mint &f)  { s = nrm(s - f.num); return s; }

    // ***
    template<typename U>
    Mint operator * (const U s) const { return static_cast<cast>(num) * static_cast<cast>(nrm(s)); }
    template<typename U> friend Mint operator * (const U f, const Mint &s) { return static_cast<cast>(s.num) * static_cast<cast>(nrm(f)); }
    Mint operator * (const Mint &s) const { return static_cast<cast>(num) * static_cast<cast>(s.num); }
    template<typename U> Mint& operator *= (const U s) { num = nrm(static_cast<cast>(num) * static_cast<cast>(nrm(s))); return *this; }
    Mint& operator *= (const Mint &s) { num = nrm(static_cast<cast>(num) * static_cast<cast>(s.num)); return *this; }
    template<typename U>
    friend U& operator *= (U &s, const Mint &f)  { s = nrm(static_cast<cast>(nrm(s)) * static_cast<cast>(f.num)); return s; }

    // ///
    template<typename U> Mint operator / (const U s) const { return static_cast<cast>(num) * static_cast<cast>(inverse(nrm(s))); }
    template<typename U> friend Mint operator / (const U f, const Mint &s) { return static_cast<cast>(inverse(s.num)) * static_cast<cast>(nrm(f)); }
    Mint operator / (const Mint &s) const { return static_cast<cast>(num) * static_cast<cast>(inverse(s.num)); }
    template<typename U> Mint& operator /= (const U s) { return *this *= inverse(nrm(s)); }
    Mint& operator /= (const Mint &s) { return *this *= inverse(s.num); }
    template<typename U>
    friend U& operator /= (U &s, const Mint &f)  { s = nrm(static_cast<cast>(nrm(s)) * static_cast<cast>(inverse(f.num))); return s; }

    //cout, cin
    friend istream &operator>>(istream &is, Mint &x) {
        is >> x.num;
        x.num = nrm(x.num);
        return is;
    }
    friend ostream &operator<<(ostream &os, const Mint &x) { return os << x.num; }
    template<typename U>
    inline static T nrm(U x) {
        T v;
        if(x >= -mod && x < mod) v = static_cast<T>(x);
        else v = static_cast<T>(x % mod);
        if(v < 0) return v + mod;
        return v;
    }
    inline static T inverse(T x, T m = mod) {
        T x0 = 1, x1 = 0, q, t;
        while(m) {
            q = x / m;
            x -= q * m, t = x, x = m, m = t;
            x0 -= q * x1, t = x0, x0 = x1, x1 = t;
        }
        assert(x == 1);
        return x0;
    }
    inline static T fastPower(T base, T power) {
        if (power < 0) return 0;
        if (power == 0) return 1;
        T temp = fastPower(base, power >> 1);
        return static_cast<T>((static_cast<cast>(temp) * static_cast<cast>(temp) * (power & 1 ? static_cast<cast>(base) : static_cast<cast>(1))) % mod);
    }
private:
    static T mod;
    T num;
};

//template<> long long Mint<long long, __int128>::mod = static_cast<long long>(1E18) + 9;
template<> int Mint<int, long long>::mod = static_cast<int>(1E9) + 7;
using Z = Mint<int, long long>;

class Decompo {
public:
    int n, z;
    vector<vector<int>> freq;
    vector<vector<int>> arr;
    explicit Decompo(const vector<int> &_arr) : n(int(_arr.size())), z(int(sqrt(_arr.size())) + 1), arr(z), freq(z, vector<int>(n + 1)) {
        for(int i = 0; i < n; i++) {
            arr[i / z].push_back(_arr[i]);
            freq[i / z][_arr[i]]++;
        }
    }
    int erase(int j) {
        for(int i = 0; i < z; i++) {
            if(j < arr[i].size()) {
                int x = arr[i][j];
                for(j++; j < arr[i].size(); j++)
                    arr[i][j - 1] = arr[i][j];
                arr[i].pop_back();
                freq[i][x]--;
                return x;
            }
            j -= int(arr[i].size());
        }
        return -1;
    }
    void insert(int j, int x) {
        for(int i = 0; i < z; i++) {
            if(j <= arr[i].size()) {
                arr[i].insert(arr[i].begin() + j, x);
                freq[i][x]++;
                return;
            }
            j -= int(arr[i].size());
        }
    }
    int count(int x, int l, int r) {
        int ans = 0;
        int j = 0;
        for(int b = 0; b < z; b++) {
            if(j > r) break;
            if(j >= l) {
                if(j + arr[b].size() - 1 <= r) {
                    ans += freq[b][x];
                    j += int(arr[b].size());
                }
                else {
                    for(int i = 0; i < arr[b].size() && j <= r; j++, i++) {
                        ans += arr[b][i] == x;
                    }
                }
            }
            else if(j + arr[b].size() - 1 >= l) {
                int i = l - j;
                j = l;
                for(; i < arr[b].size() && j <= r; j++, i++) {
                    ans += arr[b][i] == x;
                }
            }
            else {
                j += int(arr[b].size());
            }
        }
        return ans;
    }
};

void moAlgo() {
    int n, q;
    cin >> n >> q;
    int z = int(sqrt(n)) + 1;

    vector<int> arr(n);
    for(int i = 0; i < n; i++) {
        cin >> arr[i];
    }

    vector<int> ans(q);
    vector<array<int, 2>> qu(q);
    vector<vector<int>> _mo(z);
    for(int i = 0; i < q; i++) {
        cin >> qu[i][0] >> qu[i][1];
        _mo[qu[i][0] / z].push_back(i);
    }

    int curr = 0;
    vector<int> freq(100001), f_f(100001);
    auto add = [&](int i) {
        f_f[++freq[arr[i]]]++;
        curr = max(curr, freq[arr[i]]);
    };
    auto del = [&](int i) {
        if(!--f_f[freq[arr[i]]] && curr == freq[arr[i]])
            curr--;
        --freq[arr[i]];
    };

    int c = 0, l = 0, r = -1;
    for(auto &mo : _mo) {
        if(mo.empty()) continue;
        c? std::sort(mo.begin(), mo.end(), [&](int i, int j){return qu[i][1] < qu[j][1];}):
        std::sort(mo.begin(), mo.end(), [&](int i, int j){return qu[i][1] > qu[j][1];});
        c ^= 1;

        for(int i : mo) {
            while(r < qu[i][1]) add(++r);
            while(l > qu[i][0]) add(--l);
            while(r > qu[i][1]) del(r--);
            while(l < qu[i][0]) del(l++);
            ans[i] = curr;
        }
    }
    for(int i : ans)
        cout << i << '\n';
}

class LCA {
public:
    int LOG, n;
    vector<vector<int>> up;
    vector<int> lvl;
    explicit LCA(const vector<vector<int>> &g, int root = 0) : n(int(g.size())), LOG(__lg(int(g.size())) + 1), lvl(n), up(n, vector<int>(LOG, 0)) {
        function<void(int)> dfs = [&](int u) -> void {
            for(auto nxt : g[u]) if(nxt != up[u][0]) {
                    up[nxt][0] = u;
                    lvl[nxt] = lvl[u] + 1;
                    for(int i = 1; i < LOG; i++) {
                        up[nxt][i] = up[up[nxt][i - 1]][i - 1];
                    }
                    dfs(nxt);
                }
        };
        dfs(root);
    }
    int get_k_ancestor(int v, int k) {
        while(k > 0) {
            v = up[v][__lg(k & -k)];
            k ^= k & -k;
        }
        return v;
    }
    int lca(int a, int b) {
        if(lvl[a] < lvl[b]) swap(a, b);
        a = get_k_ancestor(a, lvl[a] - lvl[b]);
        if(a == b)
            return a;

        for(int i = LOG - 1; i >= 0; i--) {
            if(up[a][i] != up[b][i]) {
                a = up[a][i];
                b = up[b][i];
            }
        }
        return up[a][0];
    }
};

template<int bits = 20>
struct Basis {
    int sz = 0;
    array<int, bits> arr{};
    void push(int x) {
        if(sz == bits) return; //can make any number
        int i;
        while(x) {
            i = __lg(x & -x);
            if(!arr[i])
                return sz++, void(arr[i] = x);
            x ^= arr[i];
        }
    }
    bool find(int x) {
        if(sz == bits) return true;
        int i;
        while(x) {
            i = __lg(x & -x);
            if(arr[i])
                x ^= arr[i];
            else
                return false;
        }
        return true;
    }
    void clear() {
        if(!sz) return;
        for(int i = 0; i < bits; i++) arr[i] = 0;
        sz = 0;
    }
    void operator+=(const Basis o) {
        if(sz == bits) return;
        if(o.sz == bits) { *this = o; return; }
        for(int i = 0; i < bits; i++) {
            if(o.arr[i]) {
                push(o.arr[i]);
            }
        }
    }
};

struct suffix {
    int n;
//    string s;
    vector<int> p, c, lcp;

    explicit suffix(string &s) : n(int(s.size()) + 1), p(n), c(n), lcp(n) {
        s.push_back(0);
        iota(p.begin(), p.end(), 0);
        sort(p.begin(), p.end(), [&](int i, int j) {
            return s[i] < s[j];
        });
        for (int i = 1; i < n; i++) c[p[i]] = c[p[i - 1]] + (s[p[i]] != s[p[i - 1]]);

        int k = 0;
        while ((1 << k) < n) {
            vector<int> freq(n + 2);
            for (int i = 0; i < n; i++)
                p[i] = (p[i] - (1 << k) + n) % n, freq[c[i] + 1]++;
            for (int i = 1; i <= n + 1; i++)
                freq[i] += freq[i - 1];

            vector<int> new_p(n);
            for (int i = 0; i < n; i++)
                new_p[freq[c[p[i]]]++] = p[i];
            swap(p, new_p);

            vector<int> new_c(n);
            for (int i = 1; i < n; i++) {
                new_c[p[i]] = new_c[p[i - 1]] +
                              (c[p[i]] != c[p[i - 1]] || c[(p[i] + (1 << k)) % n] != c[(p[i - 1] + (1 << k)) % n]);
            }
            swap(c, new_c);
            k++;
        }
        k = 0;
        for(int i = 0; i < n - 1; i++) {
            int j = p[c[i] - 1];
            for(; s[i + k] == s[j + k]; k++);
            if(c[i]) lcp[c[i] - 1] = k;
            k = max(k - 1, 0);
        }
    }
    vector<vector<int>> table;
    void buildLcp() {
        int LOG = __lg(n) + 1;
        table.resize(LOG, vector<int>(n));
        table[0] = lcp;
        for(int l = 1; l < LOG; l++) {
            for(int i = 0; i + (1 << (l - 1)) < n; i++) {
                table[l][i] = min(table[l - 1][i], table[l - 1][i + (1 << (l - 1))]);
            }
        }
    }
    int query(int l, int r) { // 0-based
        if(l == r) return n - 1 - l;
        l = c[l], r = c[r];
        if(l > r) swap(l, r);
        r--;
        int len = __lg(r - l + 1);
        return min(table[len][l], table[len][r - (1 << len) + 1]);
    }
};

struct corasick {
    struct node {
        array<int, 26> nxt{}, go{};
        vector<int> idx; // all string's indexes have any suffix
        int p, link;
        char ch;
        explicit node(int p = -1, char ch = '?') : p(p), ch(ch), link(-1) {
            nxt.fill(-1);
            go.fill(-1);
        }
    };
    vector<node> tr;
    explicit corasick(vector<string> &v) : tr(1) {
        for(int i = 0; i < v.size(); i++) {
            int x = 0;
            for(char c : v[i]) {
                if(tr[x].nxt[c - 'a'] == -1) {
                    tr[x].nxt[c - 'a'] = int(tr.size());
                    tr.emplace_back(x, c);
                }
                x = tr[x].nxt[c - 'a'];
            }
            tr[x].idx.push_back(i);
        }
        for(int i = 0; i < tr.size(); i++) {
            mxSuffix(i);
        }
    }
    int plus(int x, char c) {
        if(tr[x].go[c - 'a'] == -1) {
            if(tr[x].nxt[c - 'a'] != -1)
                tr[x].go[c - 'a'] = tr[x].nxt[c - 'a'];
            else
                tr[x].go[c - 'a'] = x == 0? 0: plus(mxSuffix(x), c);
        }
        return tr[x].go[c - 'a'];
    }
    int mxSuffix(int x) {
        if(tr[x].link == -1) {
            if(!x || !tr[x].p)
                tr[x].link = 0;
            else
                tr[x].link = plus(mxSuffix(tr[x].p), tr[x].ch);

            mxSuffix(tr[x].link);
            tr[x].idx.reserve(tr[x].idx.size() + tr[tr[x].link].idx.size());
            for(int y : tr[tr[x].link].idx)
                tr[x].idx.push_back(y);
        }
        return tr[x].link;
    }
};

auto manacher(const string &t) {
    string s = "%#";
    s.reserve(t.size() * 2 + 3);
    for(char c : t)
        s += c + string("#");
    s.push_back('$');
    // t = aabaacaabaa -> s = %#a#a#b#a#a#c#a#a#b#a#a#$

    vector<int> res(s.size());
    for(int i = 1, l = 1, r = 1; i < s.size(); i++) {
        res[i] = max(0, min(r - i, res[l + r - i]));
        while(s[i + res[i]] == s[i - res[i]])
            res[i]++;
        if(i + res[i] > r) {
            l = i - res[i];
            r = i + res[i];
        }
    }
    return vector<int>(res.begin() + 2, res.end() - 2); // a#a#b#a#a#c#a#a#b#a#a
    //get max odd len = res[2 * i] - 1; aba -> i = b
    //get max even len = res[2 * i + 1]; abba -> i = first b
}

template<int numOfChar = 26, char firstChar = 'a'>
struct suffix_automaton {
    struct state {
        array<int, numOfChar> nxt{};
        int link = -1;
        int len{}, cnt = 1;
        bool isSuffix = false;
        state() {
            for(auto &i : nxt) i = -1;
        }
    };
    int lst;
    vector<state> tr;
    explicit suffix_automaton(const string &s = "") : tr(1), lst(0) {
        tr.reserve(s.size() * 2 + 1);
        for(char i : s) {
            add(i - firstChar);
        }
        if(!s.empty()) buildCnt();
        for(int p = lst; p != -1; tr[p].isSuffix = true, p = tr[p].link);
    }

    void add(char c) {
        int curr = int(tr.size());
        tr.emplace_back();
        tr[curr].len = tr[lst].len + 1;
        int p = lst;
        while(~p && !~tr[p].nxt[c]) {
            tr[p].nxt[c] = curr;
            p = tr[p].link;
        }
        if(p == -1) {
            tr[curr].link = 0;
        }
        else {
            int q = tr[p].nxt[c];
            if(tr[p].len + 1 == tr[q].len) {
                tr[curr].link = q;
            }
            else {
                int clone = int(tr.size());
                tr.emplace_back();
                tr[clone] = tr[q];
                tr[clone].cnt = 0;
                tr[clone].len = tr[p].len + 1;
                while(~p && tr[p].nxt[c] == q) {
                    tr[p].nxt[c] = clone;
                    p = tr[p].link;
                }
                tr[curr].link = tr[q].link = clone;
            }
        }
        lst = curr;
    }

    void buildCnt() {
        vector<int> srt(tr.size());
        std::iota(srt.begin(), srt.end(), 0);
        std::sort(srt.begin(), srt.end(), [&](int i, int j) -> bool {
            return tr[i].len > tr[j].len;
        });
        for(int i : srt) {
            if(~tr[i].link) {
                tr[tr[i].link].cnt += tr[i].cnt;
            }
        }
    }
};

void solve() {

}

int32_t main() {
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout << fixed << setprecision(10);
//    freopen("output.txt", "w", stdout); freopen("input.txt", "r", stdin);
    int test = 1;
    //cin >> test;
    while(test-- > 0) {
        solve();
    }
    cerr << clock() / 1000.0 << " Secs";
    return 0;
}

/*
 sum of divisors
 prime^power * prime2^power2 * ...

 ((prime^(power + 1)) / (prime - 1)) * ((prime2^(power2 + 1)) / (prime2 - 1)) * ...
 ===================================================================================================
 num ^ (num2 ^ p) % mod = num ^ ((num2 ^ p) % (mod - 1)) % mod

 ===================================================================================================
 biggest divisors
 735134400 1344 => 2^6 3^3 5^2 7 11 13 17
 73513440 768
 */