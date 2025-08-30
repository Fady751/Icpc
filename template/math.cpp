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
 // be careful if a and m not co prime you should take mod like that
 void MOD(int x, int mod) { return x < mod? x: x % mod + mod; } or
 void MOD(int x, int mod) { return x < mod? x: (x - log2(mod) ) % mod + log2(mod); }
 ===================================================================================================
 for all  1 <= i <= n, sum[n] += gcd(i, n)
 sum[a * b] = sum[a] * sum[b] if and only if a and b are coprime
 ===================================================================================================
 sum of numbers 1 <= i <= n | if(gcd(n, i) == d): sum += i, cnt++
 sum = n * phi(n / d) / 2
 cnt = phi(n / d)
 ===================================================================================================
 count balanced brackets
 r=n/2  ||  or r = number of opened brackets
 nCr(n, r) - nCr(n, r-1)
 ===================================================================================================
 // different n*n grids whose each square have m colors
 // if possible to rotate one of them so that they look the same then they same
 t = n * n;
 total = (fp(m, t)
     + fp(m, (t + 1) / 2)
     + 2 * fp(m, (t / 4) + (n % 2))) % mod;
 total = mul(total, fp(4, mod - 2));
 ===================================================================================================
 biggest divisors
 735134400 1344 => 2^6 3^3 5^2 7 11 13 17
 73513440 768
 ===================================================================================================
 for (int x = mask; x > 0; x = (x - 1) & mask)
 get all x such that mask = mask | x
 ===================================================================================================
 sum from 1 to n: i * nCr(n, i) = n * (1LL << (n - 1))
 ==================================================================================================
  g++ main.cpp -o main "-Wl,--stack,16777216"
 */

using ll = int64_t;
const int mod = 1'000'000'007;
const int N = 1e5 + 1;
int pc, spf[N], prm[N];

auto pre_Sieve = []() {
    for (int i = 2; i < N; i++){
        if(!spf[i]) spf[i] = prm[pc++] = i;
        for(int j = 0; i * prm[j] < N; j++) {
            spf[i * prm[j]] = prm[j];
            if(spf[i] == prm[j]) break;
        }
    }
    return 0;
}();

auto factors(int n) {
    vector<array<int, 2>> res;
    if(n < 2) return res;
    int p = spf[n];
    while(p > 1) {
        res.push_back({p, 0});
        while(n % p == 0) n /= p, res.back()[1]++;
        p = spf[n];
    }
    return res;
}

auto getDivisors(int _n) {
    auto _fac = factors(_n);
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

vector<int> sieve(const int BN, const int Q = 17, const int L = 1 << 15) {
    static const int rs[] = {1, 7, 11, 13, 17, 19, 23, 29};
    struct P {
        P(int p) : p(p) {}

        int p;
        int pos[8];
    };
    auto approx_prime_count = [](const int N) -> int {
        return N > 60184 ? N / (log(N) - 1.1)
                         : max(1., N / (log(N) - 1.11)) + 1;
    };

    const int v = sqrt(BN), vv = sqrt(v);
    vector<bool> isp(v + 1, true);
    for (int i = 2; i <= vv; ++i)
        if (isp[i]) {
            for (int j = i * i; j <= v; j += i) isp[j] = false;
        }

    const int rsize = approx_prime_count(BN + 30);
    vector<int> primes = {2, 3, 5};
    int psize = 3;
    primes.resize(rsize);

    vector<P> sprimes;
    size_t pbeg = 0;
    int prod = 1;
    for (int p = 7; p <= v; ++p) {
        if (!isp[p]) continue;
        if (p <= Q) prod *= p, ++pbeg, primes[psize++] = p;
        auto pp = P(p);
        for (int t = 0; t < 8; ++t) {
            int j = (p <= Q) ? p : p * p;
            while (j % 30 != rs[t]) j += p << 1;
            pp.pos[t] = j / 30;
        }
        sprimes.push_back(pp);
    }

    vector<unsigned char> pre(prod, 0xFF);
    for (size_t pi = 0; pi < pbeg; ++pi) {
        auto pp = sprimes[pi];
        const int p = pp.p;
        for (int t = 0; t < 8; ++t) {
            const unsigned char m = ~(1 << t);
            for (int i = pp.pos[t]; i < prod; i += p) pre[i] &= m;
        }
    }

    const int block_size = (L + prod - 1) / prod * prod;
    vector<unsigned char> block(block_size);
    unsigned char *pblock = block.data();
    const int M = (BN + 29) / 30;
    for (int beg = 0; beg < M; beg += block_size, pblock -= block_size) {
        int end = min(M, beg + block_size);
        for (int i = beg; i < end; i += prod) {
            copy(pre.begin(), pre.end(), pblock + i);
        }
        if (beg == 0) pblock[0] &= 0xFE;
        for (size_t pi = pbeg; pi < sprimes.size(); ++pi) {
            auto &pp = sprimes[pi];
            const int p = pp.p;
            for (int t = 0; t < 8; ++t) {
                int i = pp.pos[t];
                const unsigned char m = ~(1 << t);
                for (; i < end; i += p) pblock[i] &= m;
                pp.pos[t] = i;
            }
        }
        for (int i = beg; i < end; ++i) {
            for (int m = pblock[i]; m > 0; m &= m - 1) {
                primes[psize++] = i * 30 + rs[__builtin_ctz(m)];
            }
        }
    }
    assert(psize <= rsize);
    while (psize > 0 && primes[psize - 1] > BN) --psize;
    primes.resize(psize);
    return primes;
}

bool isPrime(ll n) {
    if(n < 4) return n > 1;
    if(n % 2 == 0 || n % 3 == 0) return false;
    for (ll i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0)
            return false;
    return true;
}

ll phi(ll x) {
    ll ans = x;
    for(ll i = 2; i * i <= x; i++) {
        if(x % i == 0) {
            while(x % i == 0) x /= i;
            ans -= ans / i;
        }
    }
    if(x > 1) ans -= ans / x;
    return ans;
}

array<ll, 3> eGcd(ll a, ll b) {
    if (b == 0) return {a, 1, 0};
    auto [g, x1, y1] = eGcd(b, a % b);
    return {g, y1, x1 - (a / b) * y1};
}

array<ll, 2> CRT(ll a1, ll m1, ll a2, ll m2) {
    a1 = (a1 % m1 + m1) % m1, a2 = (a2 % m2 + m2) % m2;
    auto [g, x, y] = eGcd(m1, m2);
    if ((a2 - a1) % g) return {-1, -1};
    ll lcm = m1 / g * m2;
    ll m = m2 / g;
    ll k = ((a2 - a1) / g % m + m) % m;
    k = (k * (x % m + m) % m) % m;
    ll res = (a1 + m1 * k) % lcm;
    if (res < 0) res += lcm;
    return {res, lcm};
}

ll modInv(ll a, ll m) {
    ll x = 1, x1 = 0, q, t, b = m;
    while(b) {
        q = a / b;
        a -= q * b, t = a, a = b, b = t;
        x -= q * x1, t = x, x = x1, x1 = t;
    }
    assert(a == 1);
    return (x + m) % m;
}

ll BSGS(ll a, ll b, ll p) {
    a %= p, b %= p;
    if(b == 1 || p == 1) return 0;
    if(a == 0) return b == 0? 1: -1;
    int add = 0;
    ll g, tmp = 1;
    while ((g = gcd(a, p)) > 1) {
        if(b % g) return -1;
        p /= g, b /= g, tmp = tmp * (a / g) % p, ++add;
        if(tmp == b) return add;
    }
    b = b * modInv(tmp, p) % p;
    int n = (int)sqrtl(p) + 1;
    unordered_map<ll, int> mp;
    for (ll q = 0, cur = 1; q <= n; ++q)
        mp.emplace(cur, q), cur = cur * a % p;
    ll an = 1;
    for (ll i = 0; i < n; ++i) an = an * a % p;
    an = modInv(an, p);
    for (ll i = 0, cur = b; i <= n; ++i) {
        auto it = mp.find(cur);
        if(it != mp.end()) return i * n + it->second + add;
        cur = cur * an % p;
    }
    return -1;
}

int fp(int b, int p) {
    int res = 1;
    while(p) {
        if(p & 1) res = int(res * 1LL * b % mod);
        b = int(b * 1LL * b % mod), p >>= 1;
    }
    return res;
}

int sumNPowerM(int n, int m) { // 1^m + 2^m ... n^m
    int k = m + 3;
    vector<int> res(k);
    for(int i = 1; i < k; i++) res[i] = (res[i - 1] + fp(i, m)) % mod;
    if(n < k) return res[n];
    int facK = k;
    vector<int> p(k); p[0] = 1;
    for(int i = 1; i < k; i++) {
        p[i] = int(p[i - 1] * 1LL * (n - i) % mod);
        facK = int(facK * 1LL * i % mod);
    }
    vector<int> inv(k + 1), s(k + 1);
    inv[k] = fp(facK, mod - 2), s[k] = 1;
    for(int i = k - 1; i >= 0; i--) {
        s[i] = int(s[i + 1] * 1LL * (n - i) % mod);
        inv[i] = int(inv[i + 1] * 1LL * (i + 1) % mod);
    }
    int ans = 0;
    for(int i = 1; i < k; i++) {
//        int cur = res[i];
//        for(int j = 1; j < k; j++) {
//            if(i == j) continue;
//            cur = int(cur * 1LL * (n - j) % mod);
//            cur = int(cur * 1LL * fp(abs(i - j), mod - 2) % mod);
//        }
//        if((k - i + 1) & 1) cur = (mod - cur) % mod;
        int cur = int(res[i] * 1LL * p[i - 1] % mod * s[i + 1] % mod * inv[i - 1] % mod * inv[k - i - 1] % mod);
        if((k - i + 1) & 1) cur = (mod - cur) % mod;
        ans = (ans + cur) % mod;
    }
    return ans;
}

ll fac[21];
void preFac() {
    fac[0] = 1;
    for(int i = 1; i <= 20; ++i)
        fac[i] = fac[i - 1] * i;
}

vector<int> kth_permutation(int n, ll k) {
    vector<int> a(n), ans;
    iota(a.begin(), a.end(), 1);
    for (int i = n; i >= 1; i--) {
        ll f = fac[i - 1];
        ans.push_back(a[k / f]);
        a.erase(a.begin() + k / f);
        k %= f;
    }
    return ans;
}

ll permutation_index(vector<int>& p) {
    int n = int(p.size());
    vector<int> a(n);
    iota(a.begin(), a.end(), 1);

    ll k = 0;
    for (int i = 0; i < n; ++i) {
        int j = int(find(a.begin(), a.end(), p[i]) - a.begin());
        k += j * fac[n - 1 - i];
        a.erase(a.begin() + j);
    }
    return k;
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
    array<int, bits> a{};
    void add(int x) {
        if(sz == bits) return;
        for(int i = __lg(x); x; x ^= a[i], i = __lg(x)) {
            if(!a[i]) return sz++, void(a[i] = x);
        }
    }
    bool find(int x) {
        if(sz == bits) return true;
        for(int i = __lg(x); x; i = __lg(x)) {
            if(a[i]) x ^= a[i];
            else return false;
        }
        return true;
    }
    void clear() {
        if(sz) a.fill(0), sz = 0;
    }
    int getMax() {
        int r = 0;
        for(int i = bits - 1; i >= 0; i--) r = max(r ^ a[i], r);
        return r;
    }
    int find_k(int k) { // index-0
        assert(k >= 0 && k < 1 << sz);
        int curr = 0;
        for(int i = bits - 1, b = sz - 1; i >= 0; i--) {
            if(a[i]) {
                if((k >> b & 1) ^ (curr >> i & 1)) curr ^= a[i];
                b--;
            }
        }
        return curr;
    }
    basis& operator+=(const basis &o) {
        if(sz == bits) return *this;
        if(o.sz == bits) return *this = o;
        for(int i = 0; i < bits; i++) if(o.a[i])
                add(o.a[i]);
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
//using namespace matrices;

namespace FFT {
    const int mod = 998244353; // 998244353 754974721 167772161
    const int root = 3; // 3 11 3
    const int invRoot = 332748118; // 332748118 617706590 55924054

    inline int mul(int x, int y) { return int(x * 1LL * y % mod); }
    inline int add(int x, int y) { return x + y < mod? x + y: x + y - mod; }
    inline int sub(int x, int y) { return x - y < 0? x - y + mod: x - y; }
    int fp(int b, int e) {
        int res = 1;
        while(e) {
            if(e & 1) res = mul(res, b);
            b = mul(b, b), e >>= 1;
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
            j ^= ((1 << __lg(n - 1 ^ j)) - 1) ^ (n - 1);
            if(i < j)swap(a[i], a[j]);
        }
        double ang = pi * (invert ? -1 : 1);
        for (int len = 1; len < n; len <<= 1, ang /= 2) {
            cd w1(cos(ang), sin(ang));
            for (int i = 0; i < n; i += len * 2) {
                cd w(1), u, v;
                for(int j = 0; j < len; j++) {
                    u = a[i + j], v = a[i + j + len] * w, w *= w1;
                    a[i + j] = u + v, a[i + j + len] = u - v;
                }
            }
        }
        if(invert) for(cd &x : a) x /= n;
    }
    vector<int64_t> mul(vector<int> const &a, vector<int> const &b) {
        int N = 1;
        while (N < a.size() + b.size() - 1) N <<= 1;
        vector<cd> t(N);
        for(int i = 0; i < a.size(); i++) t[i].real(a[i]);
        for(int i = 0; i < b.size(); i++) t[i].imag(b[i]);
        fft(t, false);
        for(auto &x : t) x *= x;
        fft(t, true);
        vector<int64_t> ans(N);
        for(int i = 0; i < N; i++) ans[i] = (int64_t)round(t[i].imag() / 2.0);
        return ans;
    }

    vector<int> string_matching(string &s, string &t) {
        if (t.size() > s.size()) return {};
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
            j ^= ((1 << __lg(n - 1 ^ j)) - 1) ^ (n - 1);
            if(i < j)swap(a[i], a[j]);
        }
        for(int len = 2, l2 = 1, w1, w, u, v; len <= n; len <<= 1, l2 <<= 1) {
            w1 = fp(invert? invRoot: root, (mod - 1) / len);
            for(int i = 0; i < n; i += len) {
                w = 1;
                for(int j = 0; j < l2; j++) {
                    u = a[i + j], v = mul(a[i + j + l2], w), w = mul(w, w1);
                    a[i + j] = add(u, v), a[i + j + l2] = sub(u, v);
                }
            }
        }
        if (invert) {
            int n_1 = fp(n, mod - 2);
            for(int & x : a) x = mul(x, n_1);
        }
    }
    vector<int> mulMod(vector<int> a, vector<int> b) {
        int N = 1;
        while (N < a.size() + b.size() - 1) N <<= 1;
        a.resize(N);
        b.resize(N);
        ntt(a, false), ntt(b, false);
        for(int i = 0; i < N; i++)
            a[i] = int(a[i] * 1LL * b[i] % mod);
        ntt(a, true);
        return a;
    }

    void fwht_and(vector<ll>& a, bool invert) {
        int n = a.size();
        for (int len = 1; 2 * len <= n; len <<= 1) {
            for (int i = 0; i < n; i += 2 * len) {
                for (int j = 0; j < len; ++j) {
                    a[i + j] = (a[i + j] + (invert? -1: 1) * a[i + j + len] + mod) % mod;
                }
            }
        }
    }
    void fwht_or(vector<ll>& a, bool invert) {
        int n = a.size();
        for (int len = 1; 2 * len <= n; len <<= 1) {
            for (int i = 0; i < n; i += 2 * len) {
                for (int j = 0; j < len; ++j) {
                    a[i + j + len] = (a[i + j + len] + (invert? -1: 1) * a[i + j] + mod) % mod;
                }
            }
        }
    }
    void fwht_xor(vector<ll>& a, bool invert) {
        int n = a.size();
        for (int len = 1; 2 * len <= n; len <<= 1) {
            for (int i = 0; i < n; i += 2 * len) {
                for (int j = 0; j < len; ++j) {
                    ll u = a[i + j], v = a[i + j + len];
                    a[i + j] = (u + v) % mod;
                    a[i + j + len] = (u - v + mod) % mod;
                }
            }
        }
        if (invert) {
            ll inv2 = (mod + 1) / 2;
            ll inv_n = 1;
            for(int i = 1; i < n; i <<= 1)
                inv_n = inv_n * inv2 % mod;
            for (ll &x : a) x = x * inv_n % mod;
        }
    }
    template<typename F>
    vector<ll> convolution(vector<ll> a, vector<ll> b, F const &fun) {
        int n = 1;
        while (n < max(a.size(), b.size())) n <<= 1;
        a.resize(n), b.resize(n);
        fun(a, false);
        fun(b, false);
        for (int i = 0; i < n; ++i) a[i] = a[i] * b[i] % mod;
        fun(a, true);
        return a;
    }
}

namespace bigNumber {
    using u128 = __uint128_t;

    istream& operator>>(istream &is, u128 &x) {
        string s; is >> s, x = 0;
        for(char c:s) x = x * 10 + (c - '0');return is;
    }
    ostream& operator<<(ostream &os, u128 x) {
        if (x == 0) return os << 0;
        string s; while (x > 0)s+='0'+x%10,x/=10;
        reverse(s.begin(), s.end());
        return os << s;
    }

    u128 mul(u128 a, u128 b, u128 m) {
        if(m <= ULLONG_MAX) return a % m * b % m;
        u128 r = 0;a %= m, b %= m;
        if(a < b)swap(a, b);
        while(b) {
            if(b & 1) r = r + a >= m ? r + a - m : r + a;
            a = a + a >= m ? a + a - m : a + a, b >>= 1;
        }
        return r;
    }
    u128 fp(u128 b, u128 p, u128 m) {
        u128 res = 1;b %= m;
        while (p) {
            if (p & 1) res = mul(res, b, m);
            b = mul(b, b, m), p >>= 1;
        }
        return res;
    }

    int ctz(u128 x) {
        int a = __builtin_ctzll(x);
        return a + (a == 64? __builtin_ctzll(x >> 64): 0);
    }
    bool isPrime(u128 n) { // millerRabin
        if (n < 2 || n % 6 % 4 != 1) return (n | 1) == 3;
        u128 s = ctz(n-1), d = n >> s;
        for(u128 a : {2, 325, 9375, 28178, 450775, 9780504, 1795265022}) {
            u128 p = fp(a%n, d, n), i = s;
            while(p != 1 && p != n - 1 && a % n && i--) p = mul(p, p, n);
            if (p != n-1 && i != s) return false;
        }
        return true;
    }

    u128 pollardRho(u128 n) {
        u128 x = 0, y = 0, t = 30, prd = 2, i = 1, q;
        auto f = [&](u128 x) { return mul(x, x, n) + i; };
        while (t++%40 || __gcd(prd, n)==1) {
            if(x == y) x = ++i, y = f(x);
            if((q = mul(prd, x>y?x-y:y-x, n))) prd = q;
            x = f(x), y = f(f(y));
        }
        return __gcd(prd, n);
    }

    auto primeFactor(u128 n) {
        vector<pair<u128,int>> res;
        if(n==1) return res;
        vector<u128> f;
        function<void(u128)> slv=[&](u128 x) {
            if(isPrime(x)) return f.push_back(x);
            u128 d = pollardRho(x);
            slv(d), slv(x/d);
        };
        slv(n);
        sort(f.begin(), f.end());
        for (u128 p : f) {
            if(res.empty() || res.back().first != p) res.emplace_back(p, 1);
            else res.back().second++;
        }
        return res;
    }
}
//using namespace bigNumber;