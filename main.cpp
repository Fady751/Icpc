#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

void T() {
    int n, m;
    scanf("%d %d", &n, &m);
    int arr[n];
    for(int i = 0; i < n; i++)
        scanf("%d", arr + i);

    int l = 0, r = 0;
    ll sum = 0;
    while(m--) {
        int x;
        scanf("%d", &x);
        while(l < n && arr[l] < x) l++;
        while(r < n && arr[r] <= x) r++;
        sum += r - l;
    }
    cout << sum << '\n';
}

int32_t main() {
    notToday
    int tc = 1;
//    cin >> tc;
    for (int test = 1; test <= tc; ++test) {
        T();
    }
//    cerr << clock() / 1000.0 << " Secs";
    return 0;
}