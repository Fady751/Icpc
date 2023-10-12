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
        cin >> x >> y;/*
        bool f = x < 0;
        x = ans(x);*/
        ll l = -1e9, r = 1e9;
        while(r > l + 1) {
        	ll m = (l + r) >> 1;
        	ll mm = m + 1;
        	//if(mm == r) mm--;
        	if(abs(m * x - m * m - y) >= abs(mm * x - mm * mm - y))
        	     l = mm;
            else
            	r = m;
        }
        ll a = l, b = x - l;
	if(a * b != y)
	    a = r, b = x - r;
        if(a * b != y || mp.find(a) == mp.end() || mp.find(b) == mp.end())
        	cout << "0 ";
        else if(a == b)
        	cout << 1LL * mp[a] * (mp[a] - 1) / 2 << " ";
        else
        	cout << 1LL * mp[a] * mp[b] << ' ';
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
