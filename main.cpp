#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

//vector<bool> sieve;
//vector<int> pr;
//void buildSieve(int n){
//    sieve.resize(n + 1, true);
//    for (int i = 2; i <= n; i++){
//        if(sieve[i]) {
//            pr.push_back(i);
//            for(ll j = ll(i) * i; j <= n; j += i)
//                sieve[j] = false;
//        }
//    }
//}

void Uwu() {
    ll n, q, x, y;
    cin >> n;
    map<ll, int> mp;
    for(int i = 0, a; i < n; i++)
        cin >> a, mp[a]++;

    cin >> q;
    while(q--) {
        cin >> x >> y;
        ll l = 1, r = abs((int)sqrt(y) + 1);
        if(r < l)
            l = -1, swap(l, r);
        ll xx = x, yy = y;
        x = abs(x);
        y = abs(y);
        while (r > l + 1) {
            ll m = (r + l) >> 1;
            if (y / m + (yy < 0? -m: m) < x)
                r = m;
            else
                l = m;

        }
        r = y / l;
        if(xx < 0)
            l = -l, r = -r;
        x = xx;
        if(y % l != 0 || r + l != x || mp.find(r) == mp.end() || mp.find(l) == mp.end())
            cout << "0 ";
        else if(l == r)
            cout << 1LL * mp[l] * (mp[l] - 1) / 2 << ' ';
        else
            cout << 1LL * mp[l] * mp[r] << ' ';
    }
    cout << '\n';
}

int32_t main() {
    notToday
//    buildSieve(sqrt(1e9) + 1);
    int tt = 1;
    cin >> tt;
    for (int test = 1; test <= tt; ++test) {
        Uwu();
    }
    cerr << clock() / 1000.0 << " Secs";
    return 0;
}
