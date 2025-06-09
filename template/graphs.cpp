#include <bits/stdc++.h>
using namespace std;

int dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
int dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
string dc = "ULRD"s;

class DSU {
    vector<int> p;
public: //0-based
    explicit DSU(int _n) : p(_n + 1, -1) { }
    int find(int i) {
        return p[i] < 0? i: p[i] = find(p[i]);
    }
    bool merge(int u, int v) {
        u = find(u);
        v = find(v);
        if(u == v)
            return false;
        if(p[u] < p[v]) swap(u, v);
        p[v] += p[u];
        p[u] = v;
        return true;
    }
    int size(int i) {
        return -p[find(i)];
    }
    bool same(int u, int v) {
        return find(u) == find(v);
    }
};

class flattenGraph {
public:
    int n, Log{};
    vector<int> g, lvl, cycleId, index;
    // lvl[u] == 0? u in loop
    // if u in cycle: cycles[cycleId[u]][index[u]] == u
    // if u not in cycle: index[u] == give me first node in cycle
    vector<vector<int>> up, cycles;

    explicit flattenGraph(vector<int> const &a) : n(int(a.size())), g(a), lvl(n), cycleId(n, -1), index(n) {
        iota(index.begin(), index.end(), 0);
        vector<int> in(n);
        for(int i = 0; i < n; i++) in[g[i]]++;

        queue<int> q;
        for(int i = 0; i < n; i++)
            if (!in[i]) q.push(i);

        vector<int> v;
        while(!q.empty()) {
            int u = q.front(); q.pop();
            v.push_back(u);
            if(!--in[g[u]]) q.push(g[u]);
        }

        reverse(v.begin(), v.end());
        for(int u : v) lvl[u] = lvl[g[u]] + 1, index[u] = index[g[u]];

        for(int i = 0; i < n; i++) {
            if(in[i]) {
                int u = i;
                vector<int> x;
                do {
                    index[u] = int(x.size());
                    cycleId[u] = int(cycles.size());
                    x.push_back(u);
                    in[u] = 0;
                    u = g[u];
                } while(u != i);
                cycles.emplace_back(std::move(x));
            }
        }
    }

    void build_up() {
        Log = __lg(n) + 1;
        up.resize(n, vector(Log, 0));
        for(int u = 0; u < n; u++) up[u][0] = g[u];

        for(int l = 1; l < Log; l++) {
            for(int u = 0; u < n; u++) {
                up[u][l] = up[up[u][l - 1]][l - 1];
            }
        }
    }

    int up_to_k(int u, int k) {
        while(k) {
            if(~cycleId[u]) {
                int i = cycleId[u];
                return cycles[i][(index[u] + k) % cycles[i].size()];
            }
            if(k <= lvl[u]) {
                u = up[u][__builtin_ctz(k)];
                k ^= k & -k;
            }
            else k -= lvl[u], u = index[u];
        }
        return u;
    }

    int go(int from, int to) { // minimum steps
        if(lvl[from] < lvl[to]) return -1;
        if(lvl[from] && !lvl[to]) {
            if(cycleId[index[from]] != cycleId[to]) return -1;
            return int(lvl[from] + (index[to] - index[index[from]] + cycles[cycleId[to]].size()) % cycles[cycleId[to]].size());
        }
        if(!lvl[from] && !lvl[to]) {
            if(cycleId[from] != cycleId[to]) return -1;
            return int((index[to] - index[from] + cycles[cycleId[to]].size()) % cycles[cycleId[to]].size());
        }
        return up_to_k(from, lvl[from] - lvl[to]) == to? lvl[from] - lvl[to]: -1;
    }
};

int max_flow(vector<vector<int>> g, int start, int end) {
    if(start == end) return INT_MAX;
    int n = int(g.size());
    vector<int> par(n);
    int mxFlow = 0;
    auto bfs = [&]() {
        fill(par.begin(), par.end(), -1);
        queue<int> q;
        q.emplace(start);
        while(!q.empty()) {
            auto u = q.front(); q.pop();
            for(int v = 0; v < n; v++) {
                if(par[v] == -1 && g[u][v] > 0) {
                    par[v] = u;
                    if(v == end) return true;
                    q.emplace(v);
                }
            }
        }
        return false;
    };
    while(bfs()) {
        int res = INT_MAX, v = end;
        while(v != start) {
            int u = par[v];
            res = min(res, g[u][v]);
            v = u;
        }
        mxFlow += res;
        v = end;
        while(v != start) {
            int u = par[v];
            g[u][v] -= res, g[v][u] += res;
            v = u;
        }
    }
    return mxFlow;
}

struct edge {
    int from, to;
    int cap;
    int64_t cost;
    explicit edge(int u, int v, int cap, int64_t cost) : from(u), to(v), cap(cap), cost(cost) { }
};

pair<int, int64_t> min_cost_max_flow(const vector<edge> &edges, int start, int end, int n) { // {max flow, min cost}
    if(start == end) return {INT_MAX, 0};
    vector<int> par(n);
    int mxFlow = 0;
    int64_t mnCost = 0, inf = 1e17;
    vector<vector<int>> g(n, vector<int>(n)); // cap
    vector<vector<int64_t>> c(n, vector<int64_t>(n)); // cost
    vector<vector<int>> adj(n);

    for(auto [u, v, cap, cost] : edges) {
        adj[u].push_back(v);
        adj[v].push_back(u);
        g[u][v] = cap;
        c[u][v] = cost;
        c[v][u] = -cost;
    }

    auto bfs = [&]() -> bool {
        fill(par.begin(), par.end(), -1);
        vector<int64_t> d(n, inf);
        d[start] = 0;
        vector<bool> inq(n, false);
        queue<int> q;
        q.push(start);

        while (!q.empty()) {
            int u = q.front(); q.pop();
            inq[u] = false;
            for (int v : adj[u]) {
                if (g[u][v] > 0 && d[v] > d[u] + c[u][v]) {
                    d[v] = d[u] + c[u][v];
                    par[v] = u;
                    if(!inq[v]) inq[v] = true, q.push(v);
                }
            }
        }
        return ~par[end];
    };
    while(bfs()) {
        int res = INT_MAX, v = end;
        while(v != start) {
            int u = par[v];
            res = min(res, g[u][v]);
            v = u;
        }
        v = end, mxFlow += res;
        while(v != start) {
            int u = par[v];
            g[u][v] -= res;
            mnCost += res * c[u][v];
            g[v][u] += res;
            v = u;
        }
    }
    return {mxFlow, mnCost};
}

struct matching {
    int nl, nr;
    vector<vector<int>> g;
    vector<int> dis, ml, mr;
    explicit matching(int nl, int nr) : nl(nl), nr(nr), g(nl), dis(nl), ml(nl, -1), mr(nr, -1) { }

    void add(int l, int r) {
        g[l].push_back(r);
    }

    void bfs() {
        queue<int> q;
        for(int u = 0; u < nl; u++) {
            if(ml[u] == -1) q.push(u), dis[u] = 0;
            else dis[u] = -1;
        }
        while(!q.empty()) {
            int l = q.front(); q.pop();
            for(int r : g[l]) {
                if(mr[r] != -1 && dis[mr[r]] == -1)
                    q.push(mr[r]), dis[mr[r]] = dis[l] + 1;
            }
        }
    }

    bool canMatch(int l) {
        for(int r : g[l]) if(mr[r] == -1)
            return mr[r] = l, ml[l] = r, true;
        for(int r : g[l]) if(dis[l] + 1 == dis[mr[r]] && canMatch(mr[r]))
            return mr[r] = l, ml[l] = r, true;
        return false;
    }

    int maxMatch() {
        int ans = 0, turn = 1;
        while(turn) {
            bfs(), turn = 0;
            for(int l = 0; l < nl; l++) if(ml[l] == -1)
                turn += canMatch(l);
            ans += turn;
        }
        return ans;
    }
    int maxMatchKarp() {
        int ans = 0, visid = 0;
        vector<int> vis(nl);
        for(int l = 0; l < nl; l++) {
            for(int r : g[l]) {
                if(mr[r] == -1) {
                    mr[r] = l, ml[l] = r, ans++;
                    break;
                }
            }
        }
        function<bool(int)> Karp = [&](int l) -> bool {
            if(vis[l] == visid) return false;
            vis[l] = visid;
            for(int r : g[l]) if(mr[r] == -1 || Karp(mr[r]))
                return mr[r] = l, ml[l] = r, true;
            return false;
        };

        for(int l = 0; l < nl; l++) if(ml[l] == -1)
            visid++, ans += Karp(l);
        return ans;
    }
    pair<vector<int>, vector<int>> minCover() {
        vector<int> L, R;
        for (int u = 0; u < nl; ++u) {
            if(dis[u] == -1) L.push_back(u);
            else if(ml[u] != -1) R.push_back(ml[u]);
        }
        return {L, R};
    }
};

string hashGraph(vector<vector<int>> &g) {
    int n = int(g.size()), rem = n;
    vector<int> deg(n);
    queue<int> q;

    for(int i = 0; i < n; i++) {
        if(g[i].size() <= 1) q.push(i);
        else deg[i] = int(g[i].size());
    }
    vector<vector<string>> hash(n);
    auto calc = [&](int i) {
        sort(hash[i].begin(), hash[i].end());
        string res = "(";
        for(string &s : hash[i]) res += s;
        res += ')';
        return res;
    };
    while(rem > 2) {
        int sz = int(q.size()); rem -= sz;
        while(sz--) {
            int u = q.front(); q.pop();
            string curr = calc(u);
            for(int nxt : g[u]) {
                hash[nxt].push_back(curr);
                if(--deg[nxt] == 1) q.push(nxt);
            }
        }
    }
    int h1 = q.front();
    string s1 = calc(q.front()); q.pop();
    if(q.empty()) return s1;
    int h2 = q.front();
    string s2 = calc(q.front()); q.pop();
    hash[h1].push_back(s2);
    hash[h2].push_back(s1);
    return min(calc(h1), calc(h2));
}
