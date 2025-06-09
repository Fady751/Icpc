#include <bits/stdc++.h>
using namespace std;

struct tree {
    int root = 0;
    vector<vector<int>> g;
    explicit tree(int n) : g(n) { }
    void add(int u, int v) {
        g[u].push_back(v);
        g[v].push_back(u);
    }

    vector<int> &operator[](int u) {
        return g[u];
    }

    int cntDfs = 0;
    vector<int> in, out, lvl, sz, top, par, seq;

    void init(int rt = 0) {
        root = rt;
        in = out = lvl = top = par = seq = vector<int>(g.size());
        sz.resize(g.size(), 1);
        par[root] = top[root] = root;
        dfs(root);
        dfs2(root);
    }

    void dfs(int u) {
        for(int &v : g[u]) {
            lvl[v] = lvl[u] + 1;
            par[v] = u;
            g[v].erase(find(g[v].begin(), g[v].end(), u));
            dfs(v);
            sz[u] += sz[v];
            if(sz[v] > sz[g[u][0]])
                swap(v, g[u][0]);
        }
    }
    void dfs2(int u) {
        in[u] = cntDfs++;
        seq[in[u]] = u;
        for(int v : g[u]) {
            top[v] = v == g[u][0]? top[u]: v;
            dfs2(v);
        }
        out[u] = cntDfs - 1;
    }

    int jump(int u, int k) {
        if(k > lvl[u]) return -1;

        int d = lvl[u] - k;
        while (lvl[top[u]] > d) {
            u = par[top[u]];
        }

        return seq[in[u] - lvl[u] + d];
    }

    bool isAncestor(int u, int v) {
        return in[u] <= in[v] && in[v] <= out[u];
    }

    int lca(int u, int v) {
        if(lvl[u] > lvl[v]) swap(u, v);
        if(isAncestor(u, v)) return u;
        while (top[u] != top[v]) {
            if (lvl[top[u]] > lvl[top[v]]) {
                u = par[top[u]];
            } else {
                v = par[top[v]];
            }
        }
        return lvl[u] < lvl[v]? u: v;
    }

    int dis(int u, int v) {
        return lvl[u] + lvl[v] - 2 * lvl[lca(u, v)];
    }
};

struct Centroid {
    vector<vector<int>> g;
    vector<int> siz, prevCen;
    vector<bool> removed;
    void add(int u, int v) {
        g[u].emplace_back(v);
        g[v].emplace_back(u);
    }
    int dfs_sz(int u, int p = -1) {
        siz[u] = 1;
        for(auto v : g[u]) {
            if(!removed[v] && v != p) {
                siz[u] += dfs_sz(v, u);
            }
        }
        return siz[u];
    }
    int calcCentroid(int u) {
        int p = -1, sz = dfs_sz(u);
        con:
        for(auto v : g[u]) {
            if(!removed[v] && v != p && siz[v] << 1 > sz) {
                p = u, u = v;
                goto con;
            }
        }
        removed[u] = true;
        return u;
    }

    explicit Centroid(int n) : g(n), siz(n), prevCen(n), removed(n), d(n) {}
    vector<vector<pair<int, int>>> d;

    void dfs(int u, int centroid, int lvl = 1, int p = -1) {
        d[u].emplace_back(centroid, lvl);
        for(auto v : g[u]) {
            if(!removed[v] && v != p) {
                dfs(v, centroid, lvl + 1, u);
            }
        }
    }

    void build(int u = 0, int p = -1) {
        u = calcCentroid(u);
        prevCen[u] = p;
        // do something...
        for(auto v : g[u]) if(!removed[v]) {
                dfs(v, u);
            }
        // ...
        for(auto v : g[u]) {
            if(!removed[v]) {
                build(v, u);
            }
        }
    }
};
