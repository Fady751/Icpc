#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

//https://codeforces.com/contest/1437/problem/D
void T() {
    int n, pre;
    cin >> n >> pre >> pre;
    vector<int> d(n);
    int ans = 1;
    d[ans]++;
    for(int i = 2, cur; i < n; i++) {
        cin >> cur;
        if(cur < pre)
            d[ans - 1] > 0? d[ans - 1]--: d[ans++]--;
        d[ans]++, pre = cur;
    }
    cout << ans << '\n';
}

int32_t main() {
    notToday
    int tc = 1;
    cin >> tc;
    for (int test = 1; test <= tc; ++test) {
        T();
    }
//    cerr << clock() / 1000.0 << " Secs";
    return 0;
}