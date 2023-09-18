#include <bits/stdc++.h>
#define Nigga_ ios::sync_with_stdio(false), cin.tie(0), cout.tie(0);
#define all(x) x.begin(), x.end()
//#define int long long
//test
typedef long long ll;
const int MOD = 1e9 + 7;
const short dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
const short dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
const char dc[] = {'U', 'L', 'R', 'D'};
using namespace std;
template<typename T> using min_queue = priority_queue<T, vector<T>, greater<>>;

struct segtree {
    int size = 1;
    vector<ll> sums;
    explicit segtree(vector<int> &arr) {
        while(size < arr.size()) size <<= 1;
        sums.resize(size << 1, 0LL);
        build(arr, 0, 0, size);
    }
    void build(vector<int> &arr, int x, int lx, int rx) {
        if(lx + 1 == rx) {
            sums[x] = arr[lx];
            return;
        }
        int m = (lx + rx) >> 1;
        build(arr, 2 * x + 1, lx, m);
        build(arr, 2 * x + 2, m, rx);
        sums[x] = sums[2 * x + 1] + sums[2 * x + 2];
    }
    void set(int i, int v, int x, int lx, int rx) {
        if(lx + 1 == rx) {
            sums[x] = v;
            return;
        }
        int m = (lx + rx) >> 1;
        if(i < m)
            set(i, v, 2 * x + 1, lx, m);
        else
            set(i, v, 2 * x + 2, m, rx);
        sums[x] = sums[2 * x + 1] + sums[2 * x + 2];
    }
    ll sum(int l, int r, int x, int lx, int rx) {
        if(r <= lx || rx <= l) return 0;
        if(lx >= l && rx <= r) return sums[x];

        int m = (lx + rx) >> 1;
        return sum(l, r, 2 * x + 1, lx, m) + sum(l, r, 2 * x + 2, m, rx);
    }
};

template<typename T> struct nT {
    T mod;
    vector <T> fac;
    vector<bool> Sieve;
    vector<int> primes;

    explicit nT(T m = 1e9 + 7) : mod(m) {}
    void buildFac(int numberOfFactorial){
        fac.resize(numberOfFactorial + 1);
        fac[0] = 1;
        for (int i = 1; i <= numberOfFactorial; i++)
            fac[i] = ((__int128) fac[i - 1] * i) % mod;
    }
    void buildSieve(int sieve){
        Sieve.resize(sieve + 1, true);
        for (int i = 2; i * i <= sieve; i++)
            if (Sieve[i]) {
                primes.push_back(i);
                for(int j = i + i; j <= sieve; j += i)
                    Sieve[j] = false;
            }
        int m = (int)sqrt(sieve);
        for(int i = m % 2 == 1?m:m + 1; i <= sieve; i += 2)
            if(Sieve[i]) primes.push_back(i);
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

void go() {
    
}

int32_t main()
{
    Nigga_
    cout << fixed << setprecision(6);
    //freopen("output.txt", "w", stdout); freopen("input.txt", "r", stdin);
    int test = 1; //cin >> test;
    while (test-- > 0){
        go();
    }
    return 0;
}
