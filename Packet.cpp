#include <bits/stdc++.h>
#define Packet ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
#define all(x) x.begin(), x.end()
using ll = long long;
using namespace std;

class SegmentTree {
    struct node {
        node *l, *r;
        ll v;
        explicit node(ll v = 0, node *l = nullptr, node *r = nullptr)
            : v(v), r(r), l(l) {
        }
    };
    vector<ll> &arr;
    node *root = nullptr;
    int size;
    void merge(node *x) {
        x->v = x->l->v + x->r->v;
    }
    node *build(int lx, int rx) {
        if(lx == rx)
            return new node(arr[lx]);

        int m = (lx + rx) >> 1;
        node *l = build(lx, m),
            *r = build(m + 1, rx),
            *x = new node(0, l, r);
        merge(x);
        return x;
    }
    void set(node *x, int lx, int rx, int i, ll &v) {
        if(!x->v || !v || rx < i) return;
        if(lx == rx) {
            ll mn = min(v, x->v);
            v -= mn;
            x->v -= mn;
            return;
        }
        int m = (lx + rx) >> 1;
        set(x->l, lx, m, i, v);
        set(x->r, m + 1, rx, i, v);
        merge(x);
    }
    ll get(node *x, int lx, int rx, int i) {
        if(lx == rx) return arr[lx] - x->v;
        int m = (lx + rx) >> 1;
        return i <= m? get(x->l, lx, m, i): get(x->r, m + 1, rx, i);
    }
public:
    explicit SegmentTree(vector<ll> &arr) : size((int)arr.size() - 1), arr(arr) {
        root = build(1, size);
    }
    void set(int i, ll v) {
        set(root, 1, size, i, v);
    }
    ll ans(int i) {
        return get(root, 1, size, i);
    }
};

void packet() {

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
