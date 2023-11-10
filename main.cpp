#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

//https://codeforces.com/contest/1620/problem/C
void T() {
    int n, k;
    ll x;
    string s;
    cin >> n >> k >> x >> s;
    vector<int> arr;
    for (int i = 0, f = 0; i < n; i++) {
        if (f)
            s[i] == '*'? arr.back()++: f = 0;
        else if (s[i] == '*')
            arr.push_back(1), f = 1;
    }
//    ll p = 1, sum = 1;
    for (int &i : arr) i *= k;
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