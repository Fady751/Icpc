#include <bits/stdc++.h>
#define notToday ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

namespace Trie{
    struct node{
        int cnt = 0, cnt1 = 0;
        node *mp[2];
        node(){for(auto &i: mp)i=nullptr;}
    };
    node *root = new node();
    void insert(node *x, int num, int i = 30) {
        x->cnt++;
        if(i == -1)
            return void(x->cnt1++);
        bool l = num & (1 << i);
        if(!x->mp[l])
            x->mp[l] = new node();
        insert(x->mp[l], num, i - 1);
    }
    void pop(node *x, int num, int i = 30) {
        x->cnt--;
        if(i == -1)
            return void(x->cnt1--);
        bool l = num & (1 << i);
        pop(x->mp[l], num, i - 1);
    }
    int ans(node *x, int num, int j, int i = 30, int rem = 0) {
        if(!x)
            return 0;
	if(i == -1)
	    return x->cnt;
        bool l = num & (1 << i);
        
        if(rem + (1 << i) >= j)
            return ans(x->mp[l], num, j, i - 1, rem);
        return (x->mp[l]? x->mp[l]->cnt: 0) + ans(x->mp[!l], num, j, i - 1, rem | (1 << i));
    }
}
using namespace Trie;

void Uwu() {
    int n;
    cin >> n;
    while(n--) {
        
    }
}

int32_t main() {
    notToday
    int tt = 1;
    //cin >> tt;
    for (int test = 1; test <= tt; ++test) {
        Uwu();
    }
    return 0;
}
