#include <bits/stdc++.h>
using namespace std;

/*
 sum of divisors
 prime^power * prime2^power2 * ...

 ((prime^(power + 1) - 1) / (prime - 1)) * ((prime2^(power2 + 1) - 1) / (prime2 - 1)) * ...
 ===================================================================================================
 a % m == b
 a and m not coprime
 g = gcd(a, m)
 (a / g) % (m / g) = b / g

 a^x % m == b
 a and m not coprime
 g = gcd(a, m)
 (a^(x-1) * (a / g)) % (m / g) = b / g
 ===================================================================================================
 a^(power%phi(m)) % m;
 ===================================================================================================
 count balanced brackets
 r=n/2
 nCr(n, r) - nCr(n, r-1)
 ===================================================================================================
 biggest divisors
 735134400 1344 => 2^6 3^3 5^2 7 11 13 17
 73513440 768
 ===================================================================================================
 for (int x = mask; x > 0; x = (x - 1) & mask)
 get all x such that mask = mask | x
 ==================================================================================================
  g++ main.cpp -o main "-Wl,--stack,16777216"
 */

const int mod = 1'000'000'007, N = 200'000;

auto sieve = [](int n){
    vector sieve(n + 1, 0);
    for (int i = 2; i <= n; i++){
        if(!sieve[i]) {
            sieve[i] = i;
            if(i * 1LL * i > n) continue;
            for(int j = i * i; j <= n; j += i) if(!sieve[j])
                sieve[j] = i;
        }
    }
    return sieve;
}(N);

vector<array<int, 2>> getFac(int n) {
    if(n < 2) return {};
    vector<array<int, 2>> res;
    int p = sieve[n];
    while(p > 1) {
        int c = 0;
        while(n % p == 0) n /= p, c++;
        res.push_back({p, c});
        p = sieve[n];
    }
    return res;
}

vector<int> getDivisors(int _n) {
    auto _fac = getFac(_n);
    int cnt = 1;
    for(auto [pr, pw] : _fac) cnt *= pw + 1;
    vector<int> res(1, 1); res.reserve(cnt);

    for(auto [pr, pw] : _fac)
        for(int i = int(res.size()) - 1; i >= 0; i--)
            for(int b = pr, j = 0; j < pw; j++, b *= pr)
                res.push_back(res[i] * b);
    sort(res.begin(), res.end());
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

int eGcd(int r0, int r1, int &x0, int &y0) {
    auto go = [](int &a, int &b, int q) {
        int next = a - b * q;
        a = b;
        b = next;
    };
    int x1 = y0 = 0, y1 = x0 = 1;
    while (r1 > 0) {
        int q = r0 / r1;
        go(r0, r1, q);
        go(x0, x1, q);
        go(y0, y1, q);
    }
    return r0;
}

int modularInverse(int num, int m = mod) {
    int x0 = 1, x1 = 0, q, t;
    while(m) {
        q = num / m;
        num -= q * m, t = num, num = m, m = t;
        x0 -= q * x1, t = x0, x0 = x1, x1 = t;
    }
    assert(num == 1);
    return (x0 + mod) % mod;
}

namespace combinatorics {
    int mod = 1e9 + 7, MXS_ = 1;
    vector<int> fac_(1, 1), inv_(1, 1);

    int fp(int b, int p = mod - 2) {
        int ans = 1;
        while(p) {
            if(p & 1) ans = int(ans * 1LL * b % mod);
            b = int(b * 1LL * b % mod);
            p >>= 1;
        }
        return ans;
    }

    void up_(int nw) {
        nw = max(MXS_ << 1, 1 << (__lg(nw) + 1));
        fac_.resize(nw), inv_.resize(nw);
        for(int i = MXS_; i < fac_.size(); i++)
            fac_[i] = int(fac_[i - 1] * 1LL * i % mod);

        inv_.back() = fp(fac_.back(), mod - 2);
        for(int i = int(inv_.size()) - 2; i >= MXS_; i--)
            inv_[i] = int(inv_[i + 1] * 1LL * (i + 1) % mod);
        MXS_ = nw;
    }

    inline int nCr(int n, int r) {
        if(r < 0 || r > n) return 0;
        if(n >= MXS_) up_(n);
        return int(fac_[n] * 1LL * inv_[r] % mod * inv_[n - r] % mod);
    }
    inline int nCr1(int n, int r) {
        if(r < 0 || r > n) return 0;
        r = min(r, n - r);
        if(r >= MXS_) up_(r);
        int ans = inv_[r];
        for(int i = n - r + 1; i <= n; i++) {
            ans = int(ans * 1LL * i % mod);
        }
        return ans;
    }
    inline int nPr(int n, int r) {
        if(r < 0 || r > n) return 0;
        if(n >= MXS_) up_(n);
        return int(fac_[n] * 1LL * inv_[n - r] % mod);
    }

    inline int add(int x, int y) {
        x = y < 0? x + y + mod: x + y;
        return x >= mod? x - mod: x;
    }
    inline int mul(int x, int y) {
        return int(x * 1LL * y % mod);
    }
}
//using namespace combinatorics;

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

template<int Log = 30>
class trie_xor{
    struct node{
        int cnt{};
        node *mp[2]{};
    } *root = new node;

    void clear(node *x) {
        if(!x) return;
        for(auto &i : x->mp) clear(i);
        delete x;
    }
public:
    ~trie_xor() { clear(root); }

    void add(int num, int c = 1) {
        node *x = root;
        for(int i = Log; i >= 0; i--) {
            x->cnt += c;
            bool b = num >> i & 1;
            if(!x->mp[b]) x->mp[b] = new node;
            x = x->mp[b];
        }
        x->cnt += c;
    }

    int get(int num, bool max = true) {
        if(root->cnt <= 0) return max? 0: INT_MAX; // trie is empty
        node *x = root;
        int ans = 0;
        for(int i = Log; i >= 0; i--) {
            bool b = bool(num >> i & 1) ^ max;
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

    void clear() { clear(root), root = new node; }
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
            if(arr[i]) x ^= arr[i];
            else return false;
        }
        return true;
    }
    void clear() {
        if(!sz) return;
        arr.fill(0);
        sz = 0;
    }
    int getMax() {
        int maxXor = 0;
        for(int i = bits - 1; i >= 0; i--) maxXor = max(maxXor ^ arr[i], maxXor);
        return maxXor;
    }
    basis& operator+=(const basis &o) {
        if(sz == bits) return *this;
        if(o.sz == bits) return *this = o;
        for(int i = 0; i < bits; i++) if(o.arr[i])
            add(o.arr[i]);
        return *this;
    }
};

namespace matrices {
    const int mod = 1'000'000'007, Z = 3;
    using matrix = array<array<int, Z>, Z>;
    using vec = array<int, Z>;

    inline int add(int x, int y) {
        return x + y >= mod? x + y - mod: x + y;
    }
    inline int mul(int x, int y) {
        return int(x * 1LL * y % mod);
    }

    matrix mul(matrix const &a, matrix const &b) {
        matrix c{};
        for(int i = 0; i < Z; i++)
            for(int j = 0; j < Z; j++)
                for(int k = 0; k < Z; k++)
                    c[i][j] = add(c[i][j], mul(a[i][k], b[k][j]));
        return c;
    }

    vec mul(matrix const &a, vec const &v) {
        vec res{};
        for(int i = 0; i < Z; i++)
            for(int j = 0; j < Z; j++)
                res[i] = add(res[i], mul(v[j], a[i][j]));
        return res;
    }

    matrix fp(matrix a, int64_t p) {
        matrix res{};
        for(int i = 0; i < Z; i++) res[i][i] = 1;
        while(p) {
            if(p & 1) res = mul(res, a);
            a = mul(a, a);
            p >>= 1;
        }
        return res;
    }

    matrix add(matrix const &a, matrix b) {
        for(int i = 0; i < Z; i++)
            for(int j = 0; j < Z; j++)
                b[i][j] = add(b[i][j], a[i][j]);
        return b;
    }
}
using namespace matrices;

namespace FFT {
    const int mod = 998244353;
    const int root = 3;
    const int invRoot = 332748118;

    int fp(int b, int e) {
        int res = 1;
        while(e) {
            if (e & 1) res = int(b * 1LL * res % mod);
            b = int(b * 1LL * b % mod), e >>= 1;
        }
        return res;
    }
    void primitiveRoot() {
        int phi = mod - 1;
        vector<int> fac;
        for(int i = 2; i * 1LL * i < phi; i++) {
            if(phi % i == 0) {
                fac.push_back(i);
                while(phi % i == 0) phi /= i;
            }
        }
        if(phi > 1) fac.push_back(phi);

        for(int g = 2; g < mod; g++) {
            for(int pr : fac) if(fp(g, (mod - 1) / pr) == 1)
                goto bad;
            cout << "const int root = " << g << ";\n";
            cout << "const int invRoot = " << fp(g, mod - 2) << ";\n";
            return;
            bad:;
        }
        cerr << "404\n";
    }

    using cd = complex<double>;
    double pi = acos(-1);

    void fft(vector<cd> &a, bool invert) {
        int n = (int)a.size();

        for (int i = 1, j = 0; i < n; i++) {
            int bit = n >> 1;
            for(; j & bit; bit >>= 1) j ^= bit;
            j ^= bit;
            if(i < j) swap(a[i], a[j]);
        }

        for (int len = 2; len <= n; len <<= 1) {
            double ang = 2 * pi / len * (invert ? -1 : 1);
            cd w1(cos(ang), sin(ang));
            for (int i = 0; i < n; i += len) {
                cd w(1);
                for(int j = 0; j * 2 < len; j++) {
                    cd u = a[i + j], v = a[i + j + len / 2] * w;
                    a[i + j] = u + v;
                    a[i + j + len / 2] = u - v;
                    w *= w1;
                }
            }
        }
        if(invert) for(cd & x : a) x /= n;
    }
    vector<int64_t> mul(vector<int> &a, vector<int> &b) {
        int N = 1 << (__lg(a.size() + b.size()) + 1);

        vector<cd> ta(a.begin(), a.end()), tb(b.begin(), b.end());
        ta.resize(N);
        tb.resize(N);

        fft(ta, false), fft(tb, false);

        for(int i = 0; i < N; i++)
            ta[i] *= tb[i];

        fft(ta, true);

        vector<int64_t> ans(N);
        for(int i = 0; i < N; i++) {
            ans[i] = (int64_t)round(ta[i].real());
        }

        return ans;
    }

    vector<int> string_matching(string &s, string &t) {
        int n = s.size(), m = t.size();
        vector<int> s1(n), s2(n), s3(n);
        for(int i = 0; i < n; i++) {
            s1[i] = s[i] == '?' ? 0 : s[i] - 'a' + 1; // assign any non-zero number for non '?'s
            s2[i] = s1[i] * s1[i];
            s3[i] = s1[i] * s2[i];
        }
        vector<int> t1(m), t2(m), t3(m);
        for(int i = 0; i < m; i++) {
            t1[i] = t[m - i - 1] == '?' ? 0 : t[m - i - 1] - 'a' + 1;
            t2[i] = t1[i] * t1[i];
            t3[i] = t1[i] * t2[i];
        }
        auto s1t3 = mul(s1, t3);
        auto s2t2 = mul(s2, t2);
        auto s3t1 = mul(s3, t1);
        vector<int> oc;
        for(int i = m - 1; i < n; i++) if(s1t3[i] - s2t2[i] * 2 + s3t1[i] == 0) oc.push_back(i - m + 1);
        return oc;
    }

    void ntt(vector<int> &a, bool invert) {
        int n = (int)a.size();

        for (int i = 1, j = 0; i < n; i++) {
            int bit = n >> 1;
            for (; j & bit; bit >>= 1) j ^= bit;
            j ^= bit;
            if (i < j) swap(a[i], a[j]);
        }

        for (int len = 2; len <= n; len <<= 1) {
            int w1 = fp(invert ? invRoot : root, (mod - 1) / len);

            for (int i = 0; i < n; i += len) {
                int w = 1;
                for (int j = 0; j < len / 2; j++) {
                    int u = a[i + j], v = int(a[i + j + len / 2] * 1LL * w % mod);
                    a[i + j] = u + v < mod ? u + v : u + v - mod;
                    a[i + j + len / 2] = u - v >= 0 ? u - v : u - v + mod;
                    w = int(w * 1LL * w1 % mod);
                }
            }
        }

        if (invert) {
            int n_1 = fp(n, mod - 2);
            for(int & x : a) x = int(x * 1LL * n_1 % mod);
        }
    }
    vector<int> mulMod(vector<int> a, vector<int> b) {
        int N = 1 << (__lg(a.size() + b.size()) + 1);
        a.resize(N);
        b.resize(N);

        ntt(a, false), ntt(b, false);

        for(int i = 0; i < N; i++)
            a[i] = int(a[i] * 1LL * b[i] % mod);

        ntt(a, true);

        return a;
    }
}

namespace bigNumber {
    using u128 = __uint128_t;

    static inline istream& operator>>(istream &is, u128 &x) {
        string s; is >> s;
        x = 0;
        for (char c : s) if (isdigit(c)) x = x * 10 + (c - '0');
        return is;
    }
    static inline ostream& operator<<(ostream &os, u128 x) {
        if (x == 0) return os << '0';
        string s;
        while (x > 0) s += char('0' + (x % 10)), x /= 10;
        reverse(s.begin(), s.end());
        return os << s;
    }

    static inline u128 mul128(u128 a, u128 b, u128 mod) {
        if(mod <= LLONG_MAX) return a % mod * b % mod;
        u128 r = 0;
        a %= mod, b %= mod;
        if(a < b) swap(a, b);
        while (b) {
            if (b & 1) r = r + a >= mod? r + a - mod: r + a;
            a = a + a >= mod? a + a - mod: a + a;
            b >>= 1;
        }
        return r;
    }

    static inline u128 modexp(u128 base, u128 exp, u128 mod) {
        u128 res = 1;
        base %= mod;
        while (exp) {
            if (exp & 1) res = mul128(res, base, mod);
            base = mul128(base, base, mod);
            exp >>= 1;
        }
        return res;
    }

    static inline bool millerRabin(u128 n) {
        if (n < 2) return false;
        for (u128 p : {2, 3, 5, 7, 11, 13, 17, 19, 23})
            if(n % p == 0) return n == p;
        u128 d = n - 1, s = 0;
        while ((d & 1) == 0) d >>= 1, s++;
        auto check = [&](u128 a) {
            u128 x = modexp(a, d, n);
            if (x == 1 || x == n - 1) return true;
            for (u128 r = 1; r < s; r++) {
                x = mul128(x, x, n);
                if (x == n - 1) return true;
                if (x == 1) return false;
            }
            return false;
        };
        for (u128 a : {2, 325, 9375, 28178, 450775, 9780504, 1795265022}) {
            if(a % n == 0) return true;
            if(!check(a)) return false;
        }
        return true;
    }

    static u128 pollardBrent(u128 N) {
        if(N & 1 ^ 1) return 2;
        auto f = [&](u128 &x, u128 c) {
            x = (mul128(x, x, N) + c) % N;
        };

        static u128 rng = 0xdeafbeefff;
        uint64_t a = rng * 6364136223846793005ull + 1442695040888963407ull;
        uint64_t b = a * 6364136223846793005ull + 1442695040888963407ull;
        rng = (a + b) ^ (a * b);

        u128 X0 = 1 + a % (N - 1), X = X0, C = 1 + b % (N - 1), g = 1, q = 1, Xs, Xt;
        int m = 128, L = 1;
        while(g == 1) {
            Xt = X;
            for (int i = 1; i < L; i++) f(X, C);
            int k = 0;
            while (k < L && g == 1) {
                Xs = X;
                for (int i = 0; i < m && i < L - k; i++)
                    f(X, C), q = mul128(q, Xt > X? Xt - X: X - Xt, N);
                g = __gcd(q, N), k += m;
            }
            L += L;
        }
        if(g == N) {
            do f(Xs, C), g = __gcd(Xs > Xt ? Xs - Xt : Xt - Xs, N);
            while (g == 1);
        }
        return g;
    }

    static void factorRec(u128 n, vector<u128>& fac) {
        if (n == 1) return;
        if(millerRabin(n)) fac.push_back(n);
        else {
            u128 d = pollardBrent(n);
            factorRec(d, fac), factorRec(n / d, fac);
        }
    }

    static inline vector<pair<u128,int>> primeFactor(u128 n) {
        vector<u128> facs;
        factorRec(n, facs);
        sort(facs.begin(), facs.end());
        vector<pair<u128,int>> res;
        for (u128 p : facs) {
            if (res.empty() || res.back().first != p)
                res.emplace_back(p, 1);
            else res.back().second++;
        }
        return res;
    }
}
//using namespace bigNumber;
