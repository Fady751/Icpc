#include <bits/stdc++.h>
using namespace std;

int dx[] = {-1, 0, 0, 1, 1, -1, 1, -1};
int dy[] = {0, -1, 1, 0, 1, -1, -1, 1};
string dc = "ULRD"s;

/*
 subGraph that have all nodes of the original graph and some of its edges.
 A subgraph is called Eulerian if each node has even degree.
 Eulerian of n nodes and m edges = power(2, m - n - numberOfConnectedGraph)
 */

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

struct TarjanSCC {
    bool directed;
    int n, timer, sccCount;
    vector<int> in, low, sccId;
    vector<bool> inStack, isArticulation;
    stack<int> st;
    vector<pair<int, int>> bridges;
    vector<vector<int>> graph, sccs, dag;

    explicit TarjanSCC(int n, bool directed = false) : directed(directed), n(n), timer(0), sccCount(0) {
        graph.resize(n);
        in = low = sccId = vector(n, -1);
        inStack = isArticulation = vector(n, false);
    }

    void addEdge(int u, int v) {
        graph[u].push_back(v);
        if(!directed) graph[v].push_back(u);
    }

    void dfs(int u, int parent = -1) {
        in[u] = low[u] = ++timer;
        st.push(u), inStack[u] = true;

        int children = 0;
        for (int v : graph[u]) if(directed || v != parent) {
            if (in[v] == -1) {
                children++;
                dfs(v, u);

                if(low[v] > in[u]) bridges.emplace_back(u, v);
                if(parent != -1 && low[v] >= in[u]) isArticulation[u] = true;
                low[u] = min(low[u], low[v]);
            }
            else if(inStack[v])
                low[u] = min(low[u], in[v]);
        }
        if(parent == -1 && children > 1) isArticulation[u] = true;

        if (low[u] == in[u]) {
            sccs.emplace_back();
            int v;
            do {
                v = st.top(), st.pop(), inStack[v] = false;
                sccId[v] = sccCount;
                sccs.back().push_back(v);
            } while (v != u);
            ++sccCount;
        }
    }

    void init() { for(int i = 0; i < n; ++i) if(in[i] == -1) dfs(i); }

    void buildDAG() {
        dag.assign(sccCount, {});
        set<pair<int, int>> edgeSet;

        for (int u = 0, su, sv; u < n; ++u) {
            su = sccId[u];
            for(int v : graph[u]) {
                sv = sccId[v];
                if(su != sv && edgeSet.insert({su, sv}).second)
                    dag[su].push_back(sv);
            }
        }
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

const int inf = 1e9;
class MinCostMaxFlow {
    struct Edge { int to, rev, cap, cost; };
    int n;
    vector<vector<Edge>> g;
    vector<int> dis, pru, pri, h;

public:
    MinCostMaxFlow(int n) : n(n), g(n), dis(n), pru(n), pri(n), h(n) {}

    void addEdge(int u, int v, int cap, int cost) {
        g[u].push_back({v, (int)g[v].size(), cap, cost});
        g[v].push_back({u, (int)g[u].size() - 1, 0, -cost});
    }

    pair<int, int> flow(int s, int t, int maxF = inf) {
        int res = 0, flow = 0;
        fill(h.begin(), h.end(), 0);

        while (maxF > 0) {
            priority_queue<pair<int, int>, vector<pair<int, int>>, greater<>> q;
            fill(dis.begin(), dis.end(), inf);
            dis[s] = 0, q.emplace(0, s);

            while (!q.empty()) {
                auto [d, v] = q.top(); q.pop();
                if (dis[v] < d) continue;
                for (int i = 0; i < g[v].size(); i++) {
                    auto& e = g[v][i];
                    if (e.cap > 0 && dis[e.to] > dis[v] + e.cost + h[v] - h[e.to]) {
                        dis[e.to] = dis[v] + e.cost + h[v] - h[e.to];
                        pru[e.to] = v, pri[e.to] = i;
                        q.emplace(dis[e.to], e.to);
                    }
                }
            }
            if(dis[t] == inf) break;

            for(int v = 0; v < n; ++v) h[v] += dis[v];
            int d = maxF;
            for(int v = t; v != s; v = pru[v]) d = min(d, g[pru[v]][pri[v]].cap);

            maxF -= d, flow += d, res += d * h[t];
            for (int v = t; v != s; v = pru[v]) {
                auto& e = g[pru[v]][pri[v]];
                e.cap -= d, g[v][e.rev].cap += d;
            }
        }
        return {flow, res};
    }
};

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
