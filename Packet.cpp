#include <bits/stdc++.h>
#define Packet ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
//#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;


class SegmentTree {
    struct node {
        node *l, *r;
        int v, o{};
        bool e = false;
        explicit node(int v = {}, node *l = nullptr, node *r = nullptr)
                : v(v), r(r), l(l) {
        }
    };
    vector<int> &arr;
    node *root = nullptr;
    int size;
    void E(node *x, int lx, int rx) {
        if(x->e) {
            x->v = (rx - lx + 1) * x->o;
            if(x->l)
                x->l->e = true, x->l->o = x->o;
            if(x->r)
                x->r->e = true, x->r->o = x->o;
            x->e = false;
        }
    }
    void merge(node *x) {
        x->v = x->l->v + x->r->v;
    }
    node *build(int lx, int rx) {
        if(lx == rx)
            return new node(arr[lx]);

        int m = (lx + rx) >> 1;
        node *l = build(lx, m),
                *r = build(m + 1, rx),
                *x = new node({}, l, r);
        merge(x);
        return x;
    }
    int get(node *x, int lx, int rx, int l, int r) {
        E(x, lx, rx);
        if(lx > r || l > rx)
            return 0;
        if(lx >= l && rx <= r)
            return x->v;
        int m = (lx + rx) >> 1;
        return get(x->l, lx, m, l, r) + get(x->r, m + 1, rx, l, r);
    }
    void set(node *x, int lx, int rx, int l, int r, int o) {
        E(x, lx, rx);
        if(lx > r || l > rx)
            return ;
        if(lx >= l && rx <= r) {
            x->e = true;
            x->o = o;
            E(x, lx, rx);
            return;
        }
        int m = (lx + rx) >> 1;
        set(x->l, lx, m, l, r, o);
        set(x->r, m + 1, rx, l, r, o);
        merge(x);
    }
    void del(node *x) {
        if(x){
            del(x->l);
            del(x->r);
            delete x;
        }
    }
public://based index 1
    explicit SegmentTree(vector<int> &arr) : size((int)arr.size() - 1), arr(arr) {
        root = build(1, size);
    }
    ~SegmentTree(){
        del(root);
    }
    void set(int l, int r, int v) {
        if(l > r)
            return;
        set(root, 1, size, l, r, v);
    }
    int get(int l, int r) {
        return get(root, 1, size, l, r);
    }
};

void packet() {
    int n, m, x, idx;
    cin >> n >> m >> x;
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++) {
        cin >> arr[i];
        if(arr[i] == x)
            idx = i;
        arr[i] = (arr[i] >= x);
    }
    SegmentTree st(arr);

    while(m--) {
        int t, l, r;
        cin >> t >> l >> r;
        int sum = st.get(l, r);
        if(t == 1) {
            st.set(l, r  - sum, 0);
            st.set(r - sum + 1, r, 1);
            if(idx >= l && idx <= r)
                idx = r - sum + 1;
        }
        else {
            st.set(l, l + sum - 1, 1);
            st.set(l + sum, r, 0);
            if(idx >= l && idx <= r)
                idx = l + sum - 1;
        }
    }
    cout << idx << '\n';
}

int32_t main() {
    Packet
    int tt = 1;
    //cin >> tt;
    for (int test = 1; test <= tt; ++test) {
        packet();
    }
    return 0;
}
