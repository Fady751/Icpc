#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

vector<int> solve(vector<int> arr) {
    vector<bool> vis(arr.size());
    vector<int> ans(arr.size());
    int i;
    for(i = 1; i < arr.size(); i++) {
        if(arr[i] < arr[i - 1]) {
            if(!vis[i - 1] && upper_bound(arr.begin(), arr.begin() + i, arr[i]) - arr.begin() >= i - 1)
                vis[i] = true, ans[i] = 1, swap(arr[i], arr[i - 1]);
            else
                break;
        }
        ans[i] += ans[i - 1];
    }
    while(i < arr.size())
        ans[i++] = 1e8;
    return ans;
}
void Uwu() {
    int n;
    cin >> n;
    vector<int> arr(n);
    for(auto &i : arr)
	cin >> i;
    vector<int> l = solve(arr);
    reverse(all(arr));
    vector<int> r = solve(arr);
    reverse(all(r));
    /*
    for(int i : l)
	cout << i << ' ';
    cout << endl;
    for(int i : r)
        cout << i << ' ';*/
    int ans = min(l.back(), r[0]);
    for(int i = 0; i < n - 1; i++) 
        ans = min(ans, l[i] + r[i + 1]);
    cout << (ans > 1e7? -1: ans) << '\n';
}

int32_t main() {
    notToday
    int tt = 1;
    //cin >> tt;
    for (int test = 1; test <= tt; ++test) {
        Uwu();
    }
    cerr << clock() / 1000.0 << " Secs";
    return 0;
}
