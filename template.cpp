#include <bits/stdc++.h>
#include <utility>

#define all(x) x.begin(), x.end()
#define fun(return, ...) function<return(__VA_ARGS__)>
#define debug(x) cout << (#x) << " = " << (x) << '\n'
//#define int long long

//typedef long long ll;
const int MOD = 1e9 + 7, Inf = (1 << 30) - 1;
const int64_t INF = (1LL << 62) - 1;
const short dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
const short dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
const char dc[] = {'U', 'L', 'R', 'D'};
std::mt19937 rnd(time(nullptr));
#define rng(l, r) uniform_int_distribution<int64_t>(l, r)(rnd)
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
    template<typename T = int>
    struct equation { // n0 * x + n1 * y == n
        bool valid;
        T x, y, n0, n1, n, g;
        short sign_n0g{}, sign_n1g{};
        explicit equation(T a, T b, T n) : n0(a), n1(b), n(n), x(1), y(0) { // must a != 0 && b != 0
            T q, x1 = 0, y1 = 1, t;
            while(b) {
                q = a / b;
                t = b, b = a - q * b, a = t;
                t = x1, x1 = x - q * x1, x = t;
                t = y1, y1 = y - q * y1, y = t;
            }
            g = a;

            valid = n % g == 0;
            if(valid){
                x *= n / g;
                y *= n / g;
                stepX = n1 / g;
                stepY = n0 / g;
                sign_n0g = (stepY < 0 ? -1 : 1);
                sign_n1g = (stepX < 0 ? -1 : 1);
            }
        }
        T stepX{}, stepY{};
        void shift(int64_t cnt) {
            // n0 * (x + n1 / g) + n1 * (y - n0 / g) == n
            x += stepX * cnt;
            y -= stepY * cnt;
        }
        void toX(int64_t new_x, bool f = true) {
            // f == 0? x <= new_x: x >= new_x
            if(stepX == 0) return;
            int64_t dif = (new_x - x) / stepX;
            shift(dif);
            if(x < new_x && f) {
                shift(sign_n1g);
                assert(x >= new_x);
            }
            else if(x > new_x && !f) {
                shift(-sign_n1g);
                assert(x <= new_x);
            }
        }

        void toY(int64_t new_y, bool f = true) {
            // f == 0? y <= new_y: y >= new_y
            if(stepY == 0) return;
            int64_t dif = (y - new_y) / stepY;
            shift(dif);
            if(y < new_y && f) {
                shift(-sign_n0g);
                assert(y >= new_y);
            }
            else if(y > new_y && !f) {
                shift(sign_n0g);
                assert(y <= new_y);
            }
        }
        array<T, 3> count(T lx, T rx, T ly, T ry) { // {cnt, lx, rx}
            toX(lx);
            if(x > rx) return {};
            lx = x;
            toX(rx, false);
            rx = x;

            toY(ly);
            if(y > ry) return {};
            ly = x;
            toY(ry, false);
            ry = x;

            if(ly > ry) swap(ly, ry);
            lx = max(lx, ly);
            rx = min(rx, ry);
            if(lx > rx) return {};
            return {(rx - lx) / abs(stepX) + 1, lx, rx};
        }
    };
    map<int64_t, int> dpFib;
    int fib(int64_t n) {
        if(n == 0) return 0;
        if(n <= 2) return 1;
        if(dpFib.count(n))
            return dpFib[n];
        if(n & 1) {
            int a = fib(n / 2);
            int b = fib(n / 2 + 1);
            int &ret = dpFib[n] = int(a * 1LL * a % mod) + int(b * 1LL * b % mod);
            return ret = (ret >= mod? ret - mod: ret);
        }
        int a = fib(n - 1);
        int c = fib(n - 3);
        int b = a - c;
        if(b < 0) b += mod;
        a += b;
        return dpFib[n] = (a >= mod ? a - mod : a);
    }
}
//using namespace numberTheory;

template<class T = int64_t>
class lazySegment {
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
    inline static void push(node *x, const int &lx, const int &rx) {
        if(x->E) {
            if(x->l) x->l->E += x->E;
            if(x->r) x->r->E += x->E;
            x->v += x->E * (rx - lx + 1);
            x->E = 0;
        }
    }

    template<class U>
    void build(node *x, int lx, int rx, U &arr) {
        if(lx == rx) return void(x->v = arr[lx]);
        x->build();
        int m = (lx + rx) >> 1;
        build(x->l, lx, m, arr);
        build(x->r, m + 1, rx, arr);
        merge(x);
    }

    T get(node *x, int lx, int rx, int l, int r) {
        if(lx != rx) x->build();
        push(x, lx, rx);
        if(lx > r || l > rx) return 0;
        if(lx >= l && rx <= r) return x->v;
        int m = (lx + rx) >> 1;
        return merge(get(x->l, lx, m, l, r), get(x->r, m + 1, rx, l, r));
    }
    void set(node *x, int lx, int rx, int i, T val) {
        if(lx != rx) x->build();
        push(x, lx, rx);
        if (i < lx || i > rx) return;
        if(lx == rx) return void(x->v = val);
        int m = (lx + rx) >> 1;
        set(x->l, lx, m, i, val), set(x->r, m + 1, rx, i, val);
        merge(x);
    }
    void Range(node *x, int lx, int rx, int l, int r, T val) {
        if(lx != rx) x->build();
        push(x, lx, rx);
        if(lx > r || l > rx) return;
        if(lx >= l && rx <= r) return x->E = val, push(x, lx, rx);
        int m = (lx + rx) >> 1;
        Range(x->l, lx, m, l, r, val), Range(x->r, m + 1, rx, l, r, val);
        merge(x);
    }
    void del(node *x) {
        if(x){
            del(x->l), del(x->r);
            delete x;
        }
    }
public://based index 0
    explicit lazySegment(int n = 1000000000) : size(n), root(new node()) { }

    template<class U>
    explicit lazySegment(U &arr) : size(int(arr.size()) - 1), root(new node()) {
        build(root, 0, size, arr);
    }
    ~lazySegment(){
        del(root);
    }
    void set(int i, T v) {
        set(root, 0, size, i, v);
    }
    T get(int l, int r) {
        return get(root, 0, size, l, r);
    }
    T operator[](int i) {
        return get(root, 0, size, i, i);
    }
    void Range(int l, int r, T val) {
        Range(root, 0, size, l, r, val);
    }
    void clear() {
        del(root);
        root = new node();
    }
    void resize(int sz) {
        size = sz;
    }
};

template<class info = int64_t>
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
    static info defaultVal;

    template<class U>
    void build(node *x, int lx, int rx, U &arr) {
        if(lx == rx) return void(x->v = arr[lx]);
        x->create();
        int m = (lx + rx) >> 1;
        build(x->l, lx, m, arr);
        build(x->r, m + 1, rx, arr);
        x->v = x->l->v + x->r->v;
    }

    info get(node *x, int lx, int rx, int l, int r) {
        if(lx != rx) x->create();
        if(lx > r || l > rx) return defaultVal;
        if(lx >= l && rx <= r) return x->v;
        int m = (lx + rx) >> 1;
        return get(x->l, lx, m, l, r) + get(x->r, m + 1, rx, l, r);
    }

    void set(node *x, int lx, int rx, int i, info val) {
        if(lx != rx) x->create();
        if (i < lx || i > rx) return;
        if(lx == rx) return void(x->v = val);
        int m = (lx + rx) >> 1;
        set(x->l, lx, m, i, val), set(x->r, m + 1, rx, i, val);
        x->v = x->l->v + x->r->v;
    }

    void del(node *x) {
        if(x){
            del(x->l), del(x->r);
            delete x;
        }
    }
public://0-based
    explicit segmentTree(int n = 1000000000) : size(n), root(new node()) { }

    template<class U>
    explicit segmentTree(U &arr) : size(int(arr.size()) - 1), root(new node()) {
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
    void resize(int sz) {
        size = sz;
    }
};

struct info {
    int64_t sum;
    info(int64_t x = 0LL) {
        sum = x;
    }
    info operator+(const info &o) const {
        return sum + o.sum;
    }
};
template<> info segmentTree<info>::defaultVal = info();

template<typename T>
struct sparse{
    int Log, n;
    vector<vector<T>> table;
    static T merge(T &x, T &y) {
        return __gcd(x, y);
    }
    explicit sparse(vector<T> &arr) : n((int)arr.size()), Log(__lg(arr.size()) + 1), table(Log, vector<T>(n)) {
        table[0] = arr;
        for(int l = 1; l < Log; l++) {
            for(int i = 0; i + (1 << (l - 1)) < n; i++) {
                table[l][i] = merge(table[l - 1][i], table[l - 1][i + (1 << (l - 1))]);
            }
        }
    }
    T query(int l, int r) {
        if(l > r) return {};
        int len = __lg(r - l + 1);
        return merge(table[len][l], table[len][r - (1 << len) + 1]);
    }
};

namespace RollingHash {
    int b1 = 31, b2 = 69, mod = 1e9 + 7, b1I = 129032259, b2I = 579710149;
    vector<int> Pb1, Pb2;
    using pi = pair<int, int>;

    void pre(unsigned maxSize) {
        Pb1 = Pb2 = vector<int>(maxSize + 1, 1);
        Pb1[1] = b1, Pb2[1] = b2;
        for (int i = 2; i <= maxSize; i++) {
            Pb1[i] = int(1LL * Pb1[i - 1] * b1 % mod);
            Pb2[i] = int(1LL * Pb2[i - 1] * b2 % mod);
        }
    }
    struct Hash {
        pair<int, int> code;
        int size;
        explicit Hash(pair<int, int> x = {}, int sz = {}) : code(std::move(x)), size(sz) { }

        Hash(int x) : code({x % mod, x % mod}), size(1) { }

        Hash(const string &x) : code(), size(0) {
            for(char c : x) *this = *(this) + c;
        }

        void pop_front(int x) {
            code.first = int((code.first - 1LL * Pb1[--size] * x % mod + mod) % mod);
            code.second = int((code.second - 1LL * Pb2[size] * x % mod + mod) % mod);
        }

        void pop_back(int x) {
            code.first = int((1LL * (code.first - x + mod) * b1I) % mod);
            code.second = int((1LL * (code.second - x + mod) * b2I) % mod);
            size--;
        }

        void clear() {
            code = {}, size = 0;
        }

        friend Hash operator+(const Hash &f, const Hash &o) {
            return Hash({int((1LL * f.code.first * Pb1[o.size] + o.code.first) % mod),
                         int((1LL * f.code.second * Pb2[o.size] + o.code.second) % mod)}
                    , f.size + o.size);
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

    struct HashRange {
        vector<Hash> p, s;
        HashRange(const string &t) : p(t.size()), s(t.size()) {
            p.front() = t.front();
            for(int i = 1; i < t.size(); i++) {
                p[i] = p[i - 1] + t[i];
            }
            s.back() = t.back();
            for(int i = int(t.size()) - 2; i >= 0; i--) {
                s[i] = s[i + 1] + t[i];
            }
        }
        Hash get(int l, int r) {
            if(l > r) return Hash();
            if(!l) return p[r];
            return Hash({(p[r].code.first - p[l - 1].code.first * 1LL * Pb1[r - l + 1] % mod + mod) % mod,
                         (p[r].code.second - p[l - 1].code.second * 1LL * Pb2[r - l + 1] % mod + mod) % mod}
                    , r - l + 1);
        }
        Hash inv(int l, int r) {
            if(l > r) return Hash();
            if(r + 1 == s.size()) return s[l];
            return Hash({(s[l].code.first - s[r + 1].code.first * 1LL * Pb1[r - l + 1] % mod + mod) % mod,
                         (s[l].code.second - s[r + 1].code.second * 1LL * Pb2[r - l + 1] % mod + mod) % mod}
                    , r - l + 1);
        }
    };
}
//using namespace RollingHash;

template<int Log = 30>
class trie_xor{
    struct node{
        int cnt{};
        node *mp[2]{};
    } *root = new node;

    void clear(node *x) {
        if(!x) return;
        for(auto &i : x->mp)
            clear(i);
        delete x;
    }
public:
    ~trie_xor() {
        clear(root);
    }

    void add(int num, int c = 1) {
        node *x = root;
        for(int i = Log; i >= 0; i--) {
            x->cnt += c;
            bool b = num & (1 << i);
            if(!x->mp[b])
                x->mp[b] = new node;
            x = x->mp[b];
        }
        x->cnt += c;
    }

    int get(int num, bool max = true) {
        if(root->cnt <= 0)
            return 0; // trie is empty
        node *x = root;
        int ans = 0;
        for(int i = Log; i >= 0; i--) {
            bool b = bool(num & (1 << i)) ^ max;
            if(x->mp[b] && x->mp[b]->cnt > 0) {
                if(b) ans |= 1 << i;
                x = x->mp[b];
            }
            else {
                if(!b) ans |= 1 << i;
                x = x->mp[!b];
            }
        }
        return ans ^ num;
    }

    void clear() {
        clear(root);
        root = new node;
    }
};

template<class T>
struct BIT { // 1-based
    int n;
    vector<T> tree;
    explicit BIT(int size) : n(size), tree(size + 1) { }

    void add(int i, T val) {
        for (; i <= n; i += i & -i)
            tree[i] += val;
    }

    T query(int i) {
        T sum = 0;
        for (; i > 0; i -= i & -i)
            sum += tree[i];
        return sum;
    }

    T range(int l, int r) {
        return query(r) - query(l - 1);
    }

    int lower_bound(T target) {
        int i = 0;
        T curr = 0;
        for (int mask = 1 << __lg(n); mask > 0; mask >>= 1) {
            if (i + mask <= n && curr + tree[i + mask] < target) {
                curr += tree[i += mask];
            }
        }
        return i + 1;
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

struct tree {
    int root = 0;
    vector<vector<int>> g;
    explicit tree(int n) : g(n) { }
    void add(int u, int v) {
        g[u].push_back(v);
        g[v].push_back(u);
    }

    vector<int> &operator[](int u) {
        return g[u];
    }

    int lg = 17, cntDfs = 0;
    vector<int> in, out, lvl, sz, Log, par;
    vector<vector<int>> up;
    void build(int rt = 0) {
        root = rt;
        in = out = lvl = sz = par = Log = vector<int>(g.size());
        par[root] = -1;
        Log[0] = -1;
        for(int i = 2; i < g.size(); i++)
            Log[i] = Log[i >> 1] + 1;
        lg = Log[((int)g.size()) >> 1] + 2;
        up = vector<vector<int>>(g.size(), vector<int>(lg, -1));
        dfs(root);
    }

    void dfs(int u) {
        if(u != root) {
            g[u].erase(find(g[u].begin(), g[u].end(), par[u]));
        }
        in[u] = cntDfs++;
        sz[u] = 1;
        for(int &v : g[u]) {
            lvl[v] = lvl[u] + 1;
            up[v][0] = u;
            for(int i = 1; i < lg && ~up[v][i - 1]; i++) {
                up[v][i] = up[up[v][i - 1]][i - 1];
            }
            par[v] = u;
            dfs(v);
            sz[u] += sz[v];
            if(sz[v] > sz[g[u][0]])
                swap(v, g[u][0]);
        }
        out[u] = cntDfs - 1;
    }

    int jump(int u, int k) {
        if(k > lvl[u]) return -1;
        while(k) {
            u = up[u][Log[k]];
            k ^= 1 << Log[k];
        }
        return u;
    }

    bool isAncester(int u, int v) {
        return in[u] <= in[v] && in[v] <= out[u];
    }

    int lca(int u, int v) {
        if(lvl[u] > lvl[v]) swap(u, v);
        if(isAncester(u, v)) return u;
        v = jump(v, lvl[v] - lvl[u]);
        for(int j = lg - 1; j >= 0; j--) {
            if(up[u][j] != up[v][j]) {
                u = up[u][j];
                v = up[v][j];
            }
        }
        return up[u][0];
    }

    int dis(int u, int v) {
        return lvl[u] + lvl[v] - 2 * lvl[lca(u, v)];
    }
};

const int bits = __lg(100000) + 1;
struct basis {
    int sz = 0;
    array<int, bits> arr{};
    void add(int x) {
        if(sz == bits) return;
        for(int i = __lg(x); x; i = __lg(x)) {
            if(!arr[i])
                return sz++, void(arr[i] = x);
            x ^= arr[i];
        }
    }
    bool find(int x) {
        if(sz == bits) return true;
        for(int i = __lg(x); x; i = __lg(x)) {
            if(arr[i])
                x ^= arr[i];
            else
                return false;
        }
        return !x;
    }
    void clear() {
        if(!sz) return;
        arr.fill(0);
        sz = 0;
    }
    int getMax() {
        int maxXor = 0;
        for (int i = bits - 1; i >= 0; i--) {
            if ((maxXor ^ arr[i]) > maxXor) {
                maxXor ^= arr[i];
            }
        }
        return maxXor;
    }
    basis& operator+=(const basis &o) {
        if(sz == bits) return *this;
        if(o.sz == bits) { return *this = o; }
        for(int i = 0; i < bits; i++) {
            if(o.arr[i]) {
                add(o.arr[i]);
            }
        }
        return *this;
    }
};

vector<int> z_algo(string s) {
    vector<int> z(s.size());
    for(int i = 1, l = 0, r = 0; i < s.size(); i++) {
        if(i < r) {
            z[i] = min(r - i, z[i - l]);
        }
        while(i + z[i] < s.size() && s[z[i]] == s[z[i] + i])
            z[i]++;
        if(i + z[i] > r) {
            r = i + z[i];
            l = i;
        }
    }
    return z;
}

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

string hashGraph(vector<vector<int>> &g) {
    int n = int(g.size()), rem = n;
    vector<int> deg(n);
    queue<int> q;

    for(int i = 0; i < n; i++) {
        if(g[i].size() <= 1)
            q.push(i);
        else
            deg[i] = int(g[i].size());
    }
    vector<vector<string>> hash(n);
    auto calc = [&](int i) {
        std::sort(hash[i].begin(), hash[i].end());
        string res = "(";
        for(string &s : hash[i])
            res += s;
        res += ')';
        return res;
    };
    while(rem > 2) {
        int sz = int(q.size());
        rem -= sz;
        while(sz--) {
            int u = q.front(); q.pop();
            string curr = calc(u);
            for(int nxt : g[u]) {
                hash[nxt].push_back(curr);
                if (--deg[nxt] == 1) {
                    q.push(nxt);
                }
            }
        }
    }
    int h1 = q.front();
    string s1 = calc(q.front()); q.pop();
    if(q.empty())
        return s1;
    int h2 = q.front();
    string s2 = calc(q.front()); q.pop();
    hash[h1].push_back(s2);
    hash[h2].push_back(s1);
    return min(calc(h1), calc(h2));
}

int max_flow(vector<vector<int>> g, int start, int end) {
    if(start == end) return INT_MAX;
    int n = int(g.size());
    vector<int> par(n);
    int mxFlow = 0;
    auto bfs = [&]() {
        std::fill(par.begin(), par.end(), -1);
        queue<int> q;
        q.emplace(start);
        while(!q.empty()) {
            auto u = q.front(); q.pop();
            for(int v = 0; v < n; v++) {
                if(par[v] == -1 && g[u][v] > 0) {
                    par[v] = u;
                    if(v == end) return true;
                    q.emplace(v);
                }
            }
        }
        return false;
    };
    while(bfs()) {
        int res = INT_MAX, v = end;
        while(v != start) {
            int u = par[v];
            res = min(res, g[u][v]);
            v =  u;
        }
        mxFlow += res;
        v = end;
        while(v != start) {
            int u = par[v];
            g[u][v] -= res;
            g[v][u] += res;
            v =  u;
        }
    }
    return mxFlow;
}

struct edge {
    int from, to;
    int cap;
    int64_t cost;
    explicit edge(int u, int v, int cap, int64_t cost) : from(u), to(v), cap(cap), cost(cost) { }
};

pair<int, int64_t> min_cost_max_flow(const vector<edge> &edges, int start, int end, int n) { // {max flow, min cost}
    if(start == end) return {INT_MAX, 0};
    vector<int> par(n);
    int mxFlow = 0;
    int64_t mnCost = 0, inf = 1e17;
    vector<vector<int>> g(n, vector<int>(n)); // cap
    vector<vector<int64_t>> c(n, vector<int64_t>(n)); // cost
    vector<vector<int>> adj(n);

    for(auto [u, v, cap, cost] : edges) {
        adj[u].push_back(v);
        adj[v].push_back(u);
        g[u][v] = cap;
        c[u][v] = cost;
        c[v][u] = -cost;
    }

    auto bfs = [&]() -> bool {
        std::fill(par.begin(), par.end(), -1);
        vector<int64_t> d(n, inf);
        d[start] = 0;
        vector<bool> inq(n, false);
        queue<int> q;
        q.push(start);

        while (!q.empty()) {
            int u = q.front();
            q.pop();
            inq[u] = false;
            for (int v : adj[u]) {
                if (g[u][v] > 0 && d[v] > d[u] + c[u][v]) {
                    d[v] = d[u] + c[u][v];
                    par[v] = u;
                    if (!inq[v]) {
                        inq[v] = true;
                        q.push(v);
                    }
                }
            }
        }
        return ~par[end];
    };
    while(bfs()) {
        int res = INT_MAX, v = end;
        while(v != start) {
            int u = par[v];
            res = min(res, g[u][v]);
            v =  u;
        }
        v = end;
        mxFlow += res;
        while(v != start) {
            int u = par[v];
            g[u][v] -= res;
            mnCost += res * c[u][v];
            g[v][u] += res;
            v =  u;
        }
    }
    return {mxFlow, mnCost};
}

struct matching {
    int nl, nr;
    vector<vector<int>> g;
    vector<int> dis, ml, mr;
    explicit matching(int nl, int nr) : nl(nl), nr(nr), g(nl), dis(nl), ml(nl, -1), mr(nr, -1) { }

    void add(int l, int r) {
        g[l].push_back(r);
    }

    void bfs() {
        queue<int> q;
        for(int u = 0; u < nl; u++) {
            if(ml[u] == -1) {
                q.push(u);
                dis[u] = 0;
            }
            else {
                dis[u] = -1;
            }
        }
        while(!q.empty()) {
            int l = q.front(); q.pop();
            for(int r : g[l]) {
                if(mr[r] != -1 && dis[mr[r]] == -1) {
                    q.push(mr[r]);
                    dis[mr[r]] = dis[l] + 1;
                }
            }
        }
    }

    bool canMatch(int l) {
        for(int r : g[l]) {
            if(mr[r] == -1) {
                mr[r] = l, ml[l] = r;
                return true;
            }
        }
        for(int r : g[l]) {
            if(dis[l] + 1 == dis[mr[r]] && canMatch(mr[r])) {
                mr[r] = l, ml[l] = r;
                return true;
            }
        }
        return false;
    }

    int maxMatch() {
        int ans = 0, turn = 1;
        while(turn) {
            bfs();
            turn = 0;
            for(int l = 0; l < nl; l++) {
                if(ml[l] == -1) {
                    turn += canMatch(l);
                }
            }
            ans += turn;
        }
        return ans;
    }
    int maxMatchKarp() {
        int ans = 0, visid = 0;
        vector<int> vis(nl);
        for(int l = 0; l < nl; l++) {
            for(int r : g[l]) {
                if(mr[r] == -1) {
                    mr[r] = l, ml[l] = r, ans++;
                    break;
                }
            }
        }
        function<bool(int)> Karp = [&](int l) -> bool {
            if(vis[l] == visid) return false;
            vis[l] = visid;
            for(int r : g[l]) {
                if(mr[r] == -1 || Karp(mr[r])) {
                    mr[r] = l, ml[l] = r;
                    return true;
                }
            }
            return false;
        };

        for(int l = 0; l < nl; l++) {
            if(ml[l] == -1) {
                visid++;
                ans += Karp(l);
            }
        }
        return ans;
    }
    pair<vector<int>, vector<int>> minCover() {
        vector<int> L, R;
        for (int u = 0; u < nl; ++u) {
            if (dis[u] == -1)
                L.push_back(u);
            else if (ml[u] != -1)
                R.push_back(ml[u]);
        }
        return {L, R};
    }
};

struct Centroid {
    vector<vector<int>> g;
    vector<int> siz, prevCen;
    vector<bool> removed;
    void add(int u, int v) {
        g[u].emplace_back(v);
        g[v].emplace_back(u);
    }
    int dfs_sz(int u, int p = -1) {
        siz[u] = 1;
        for(auto v : g[u]) {
            if(!removed[v] && v != p) {
                siz[u] += dfs_sz(v, u);
            }
        }
        return siz[u];
    }
    int calcCentroid(int u) {
        int p = -1, sz = dfs_sz(u);
        bool done = false;
        while(!done) {
            done = true;
            for(auto v : g[u]) {
                if(!removed[v] && v != p && siz[v] << 1 > sz) {
                    done = false;
                    p = u, u = v;
                    break;
                }
            }
        }
        removed[u] = true;
        return u;
    }

    explicit Centroid(int n) : g(n), siz(n), prevCen(n), removed(n), d(n) {}
    struct data {
        int a;
        int len;
    };
    vector<vector<data>> d;

    void dfs(int u, int centroid, int lvl = 1, int p = -1) {
        d[u].push_back({centroid, lvl});
        for(auto v : g[u]) {
            if(!removed[v] && v != p) {
                dfs(v, centroid, lvl + 1, u);
            }
        }
    }

    void build(int u = 0, int p = -1) {
        u = calcCentroid(u);
        prevCen[u] = p;
        // do something...
        for(auto v : g[u]) if(!removed[v]) {
            dfs(v, u);
        }
        // ...
        for(auto v : g[u]) {
            if(!removed[v]) {
                build(v, u);
            }
        }
    }
};

namespace matrices {
    int mod = 1'000'000'007;
    struct matrix : public vector<vector<int>> {
        size_t n;
        matrix(size_t n, bool d = false) : n(n), vector(n, vector<int>(n)) {
            for(int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    (*this)[i][j] = i == j ? d : 0;
                }
            }
        }
        matrix operator*(const matrix &B) const {
            matrix C(n);
            for(int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    for (int k = 0; k < n; k++) {
                        C[i][j] = (C[i][j] + (*this)[i][k] * B[k][j]) % mod;
                    }
                }
            }
            return C;
        }
        matrix& operator^=(int64_t p) {
            matrix res(n, true);
            while(p > 0) {
                if(p & 1) res = res * *this;
                *this = *this * *this;
                p >>= 1;
            }
            return *this = res;
        }
    };

/*
    f(n) = a * f(n - 1) + b * f(n - 3) + c
    T = {a, 0, b, 1},
        {1, 0, 0, 0},
        {0, 1, 0, 0},
        {0, 0, 0, 1}
    T ^= n - 3
    res = T[0][0] * f(3) + T[0][1] * f(2) + T[0][2] * f(1) + T[0][3] * c
*/

    int f(int64_t n) { // f(n) = f(n - 1) + f(n - 2) + 1
        if(n <= 1) return 1;
        if(n == 2) return 3;
        matrix t(3);
        t[0] = {1, 1, 1};
        t[1] = {1, 0, 0};
        t[2] = {0, 0, 1};
        t ^= n - 2;
        // f(2), f(1), const
        return (t[0][0] * 3 % mod + t[0][1] * 1 + t[0][2] * 1) % mod;
    }
}
//using namespace matrices;

void sos(vector<int> &dp, bool Do = true) {
    // do -> sum of subsets, !do -> undo pre operation
    for (int i = 0; 1 << i < dp.size(); i++) {
        for (int mask = 0; mask < dp.size(); mask++) {
            if (mask & (1 << i)) {
                dp[mask] += Do ? dp[mask ^ (1 << i)] : -dp[mask ^ (1 << i)];
//                dp[mask] >= mod? dp[mask] -= mod: dp[mask] < 0? dp[mask] += mod: 0;
            }
        }
    }
}

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

 ((prime^(power + 1) - 1) / (prime - 1)) * ((prime2^(power2 + 1) - 1) / (prime2 - 1)) * ...
 ===================================================================================================
 num ^ (num2 ^ p) % mod = num ^ ((num2 ^ p) % (mod - 1)) % mod

 ===================================================================================================
 biggest divisors
 735134400 1344 => 2^6 3^3 5^2 7 11 13 17
 73513440 768
 ===================================================================================================
 for (int x = mask; x > 0; x = (x - 1) & mask)
 get all x such that mask = mask | x
 */