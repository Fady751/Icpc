#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

void T() {
    int n;
    cin >> n;
    int k = 1 << 29;
    bool f = n / 2 % 2;
    int o = 0, e = 0;
    if(n % 2) cout << (f? k: 0) << ' ', n--, o = (f? k: 0), f = 0;
    for(int i = 0, c = 1; i < n; i++) {
        int x = c;
        if(f && i % 2 == 0) x |= k;
        else if(!f && i % 2) x |= k;
        cout << x << ' ';
        if(i % 2) o ^= x;
        else e ^= x;
        if(i % 2) c++;
    }
    cout << (o == e) << '\n';
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
