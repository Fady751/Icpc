#include <bits/stdc++.h>
using namespace std;

namespace RollingHash {
    const int N = 200'000, b1 = 31, b2 = 69, mod = 1e9 + 7, b1I = 129032259, b2I = 579710149;

    vector<int> Pb1(N + 1), Pb2(N + 1);
    char init = []() {
        Pb1[0] = Pb2[0] = 1;
        for (int i = 1; i <= N; i++) {
            Pb1[i] = int(1LL * Pb1[i - 1] * b1 % mod);
            Pb2[i] = int(1LL * Pb2[i - 1] * b2 % mod);
        }
        return char();
    }();

    struct Hash : array<int, 3> {
#define a (*this)
        Hash() : array() { }
        Hash(const array<int, 3> &x) : array(x) { }
        Hash(int x) : array({x % mod, x % mod, 1}) { }

        Hash(const string &x) : array() {
            for(char c : x) *this = *(this) + c;
        }

        void pop_front(int x) {
            a[0] = int((a[0] - 1LL * Pb1[--a[2]] * x % mod + mod) % mod);
            a[1] = int((a[1] - 1LL * Pb2[a[2]] * x % mod + mod) % mod);
        }

        void pop_back(int x) {
            a[0] = int((1LL * (a[0] - x + mod) * b1I) % mod);
            a[1] = int((1LL * (a[1] - x + mod) * b2I) % mod);
            a[2]--;
        }

        void clear() { a[0] = a[1] = a[2] = 0; }

        friend Hash operator+(const Hash &f, const Hash &o) {
            return array{int((1LL * f[0] * Pb1[o[2]] + o[0]) % mod),
                         int((1LL * f[1] * Pb2[o[2]] + o[1]) % mod)
                    , f[2] + o[2]};
        }
#undef a
    };

    struct HashRange {
        vector<Hash> p, s;
        HashRange(const string &t) : p(t.size()), s(t.size()) {
            p.front() = t.front();
            for(int i = 1; i < t.size(); i++) p[i] = p[i - 1] + t[i];
            s.back() = t.back();
            for(int i = int(t.size()) - 2; i >= 0; i--) s[i] = s[i + 1] + t[i];
        }
        Hash get(int l, int r) {
            if(l > r) return {};
            if(!l) return p[r];
            return array{int((p[r][0] - p[l - 1][0] * 1LL * Pb1[r - l + 1] % mod + mod) % mod),
                         int((p[r][1] - p[l - 1][1] * 1LL * Pb2[r - l + 1] % mod + mod) % mod)
                    , r - l + 1};
        }
        Hash inv(int l, int r) {
            if(l > r) return {};
            if(r + 1 == s.size()) return s[l];
            return array{int((s[l][0] - s[r + 1][0] * 1LL * Pb1[r - l + 1] % mod + mod) % mod),
                         int((s[l][1] - s[r + 1][1] * 1LL * Pb2[r - l + 1] % mod + mod) % mod)
                    , r - l + 1};
        }
    };
}
//using namespace RollingHash;

vector<int> z_algo(string s) {
    vector<int> z(s.size());
    for(int i = 1, l = 0, r = 0; i < s.size(); i++) {
        if(i < r) z[i] = min(r - i, z[i - l]);
        while(i + z[i] < s.size() && s[z[i]] == s[z[i] + i]) z[i]++;
        if(i + z[i] > r) r = i + z[i], l = i;
    }
    return z;
}

// O(n log(n))
struct suffix {
    int n;
    vector<int> p, c, lcp;

    explicit suffix(string &s) : n(int(s.size()) + 1), p(n), c(n), lcp(n) {
        s += char(0);
        iota(p.begin(), p.end(), 0);
        sort(p.begin(), p.end(), [&](int i, int j) {
            return s[i] < s[j];
        });
        for (int i = 1; i < n; i++) c[p[i]] = c[p[i - 1]] + (s[p[i]] != s[p[i - 1]]);

        vector<int> nc(n), np(n);
        int k = 1;
        while (k < n) {
            vector<int> f(n + 2);
            for (int i = 0; i < n; i++) p[i] = (p[i] - k + n) % n, f[c[i] + 1]++;
            for (int i = 1; i <= n + 1; i++) f[i] += f[i - 1];

            for(int i = 0; i < n; i++) np[f[c[p[i]]]++] = p[i];
            swap(p, np);

            nc[p[0]] = 0;
            for (int i = 1; i < n; i++)
                nc[p[i]] = nc[p[i - 1]] +
                           (c[p[i]] != c[p[i - 1]]
                            || c[(p[i] + k) % n] != c[(p[i - 1] + k) % n]);
            swap(c, nc);
            k <<= 1;
        }
        k = 0;
        for(int i = 0; i < n - 1; i++) {
            int j = p[c[i] - 1];
            for(; s[i + k] == s[j + k]; k++);
            if(c[i]) lcp[c[i] - 1] = k;
            k = max(k - 1, 0);
        }
    }
    vector<vector<int>> table;
    void buildLcp() {
        int LOG = __lg(n) + 1;
        table.resize(LOG, vector<int>(n));
        table[0] = lcp;
        for(int l = 1; l < LOG; l++) {
            for(int i = 0; i + (1 << (l - 1)) < n; i++) {
                table[l][i] = min(table[l - 1][i], table[l - 1][i + (1 << (l - 1))]);
            }
        }
    }
    int query(int l, int r) { // 0-based
        if(l == r) return n - 1 - l;
        l = c[l], r = c[r];
        if(l > r) swap(l, r);
        r--;
        int len = __lg(r - l + 1);
        return min(table[len][l], table[len][r - (1 << len) + 1]);
    }
};

// O(n)
class SuffixArray {
public:
    SuffixArray(const string &input, char first = 'a') {
        int n = (int) input.size();
        s_.resize(n + 1);
        for (int i = 0; i < n; i++) s_[i] = (input[i] - first) + 1;
        s_[n] = 0;
        sa_.assign(n + 1, -1);
        sa_is(s_, sa_, 27);
    }

    auto getSA() {
        return vector(sa_.begin() + 1, sa_.end());
    }

private:
    vector<int> s_;
    vector<int> sa_;

    void sa_is(const vector<int> &s, vector<int> &sa, int alphabet) {
        int n = (int) s.size();
        if (n == 1)
            return void(sa[0] = 0);
        if (n == 2) {
            if (s[0] == 0) sa[0] = 0, sa[1] = 1;
            else sa[0] = 1, sa[1] = 0;
            return;
        }

        vector<bool> t(n);
        t[n - 1] = true;
        for (int i = n - 2; i >= 0; i--) {
            if (s[i] < s[i + 1]) t[i] = true;
            else if (s[i] > s[i + 1]) t[i] = false;
            else t[i] = t[i + 1];
        }
        auto isLMS = [&](int i) {
            return (i > 0 && t[i] && !t[i - 1]);
        };

        vector<int> bucket(alphabet, 0);
        for (int x : s) bucket[x]++;
        vector<int> bkt_head(alphabet), bkt_tail(alphabet);
        bkt_head[0] = 0;
        bkt_tail[0] = bucket[0] - 1;
        for (int c = 1; c < alphabet; c++) {
            bkt_head[c] = bkt_head[c - 1] + bucket[c - 1];
            bkt_tail[c] = bkt_head[c] + bucket[c] - 1;
        }

        auto induceL = [&]() {
            vector<int> pos = bkt_head;
            for (int i = 0; i < n; i++) {
                int j = sa[i] - 1;
                if (j >= 0 && !t[j]) {
                    sa[pos[s[j]]] = j;
                    pos[s[j]]++;
                }
            }
        };
        auto induceS = [&]() {
            vector<int> pos = bkt_tail;
            for (int i = n - 1; i >= 0; i--) {
                int j = sa[i] - 1;
                if (j >= 0 && t[j]) {
                    sa[pos[s[j]]] = j;
                    pos[s[j]]--;
                }
            }
        };

        fill(sa.begin(), sa.end(), -1);
        {
            vector<int> pos = bkt_tail;
            for (int i = 0; i < n; i++) {
                if (isLMS(i)) {
                    sa[pos[s[i]]] = i;
                    pos[s[i]]--;
                }
            }
        }
        induceL();
        induceS();

        vector<int> LMS;
        LMS.reserve(n / 2);
        for (int i = 0; i < n; i++) {
            if (isLMS(i))
                LMS.push_back(i);
        }
        if (LMS.empty()) {
            iota(sa.begin(), sa.end(), 0);
            sort(sa.begin(), sa.end(), [&](int a, int b) {
                while (a < n && b < n) {
                    if (s[a] < s[b]) return true;
                    if (s[a] > s[b]) return false;
                    a++, b++;
                }
                return a == n;
            });
            return;
        }

        vector<int> sortedLMS;
        sortedLMS.reserve(LMS.size());
        for (int i = 0; i < n; i++) {
            if (sa[i] >= 0 && isLMS(sa[i]))
                sortedLMS.push_back(sa[i]);
        }

        vector<int> name(n, -1);
        int curName = 0;
        name[sortedLMS[0]] = 0;

        auto equalLMS = [&](int a, int b) {
            int i = 0;
            while (true) {
                if (s[a + i] != s[b + i])
                    return false;
                bool aIsL = isLMS(a + i);
                bool bIsL = isLMS(b + i);
                if (aIsL && bIsL && i > 0)
                    return true;
                if (aIsL != bIsL)
                    return false;
                i++;
            }
        };

        for (int i = 1; i < (int) sortedLMS.size(); i++) {
            int prev = sortedLMS[i - 1];
            int curr = sortedLMS[i];
            if (!equalLMS(prev, curr))
                ++curName;
            name[curr] = curName;
        }

        vector<int> reducedStr;
        reducedStr.reserve(LMS.size());
        for (int idx: LMS)
            reducedStr.push_back(name[idx]);

        vector<int> reducedSA(LMS.size(), -1);
        if (curName + 1 == (int) LMS.size()) {
            for (int i = 0; i < (int) LMS.size(); i++) {
                reducedSA[reducedStr[i]] = i;
            }
        } else {
            sa_is(reducedStr, reducedSA, curName + 1);
        }

        vector<int> LMS_order(LMS.size());
        for (int i = 0; i < (int) LMS.size(); i++) {
            LMS_order[i] = LMS[reducedSA[i]];
        }

        fill(sa.begin(), sa.end(), -1);
        {
            vector<int> pos = bkt_tail;
            for (int i = (int) LMS_order.size() - 1; i >= 0; i--) {
                int idx = LMS_order[i];
                sa[pos[s[idx]]] = idx;
                pos[s[idx]]--;
            }
        }
        induceL();
        induceS();
    }
};

string largestLexSubstring(const string &s) {
    int n = int(s.size());
    int i = 0, j = 1, k = 0;

    while (j + k < n) {
        if (s[i + k] == s[j + k]) k++;
        else if (s[i + k] < s[j + k])
            i = max(i + k + 1, j), j = i + 1, k = 0; /* change it to > if you want lowest */
        else j = j + k + 1, k = 0;
    }

    return s.substr(i);
}

struct corasick {
    struct node {
        int fail = -1;
        array<int, 26> nxt{};
        vector<int> idx;
        explicit node() { nxt.fill(-1); }
    };
    vector<node> tr;
    explicit corasick() : tr(1) { }
    int add(const string &s, int id) {
        int x = 0;
        for (char ch: s) {
            if(tr[x].nxt[ch - 'a'] == -1)
                tr[x].nxt[ch - 'a'] = int(tr.size()), tr.emplace_back();
            x = tr[x].nxt[ch - 'a'];
        }
        if(tr[x].idx.empty()) tr[x].idx.push_back(id);
        return tr[x].idx.back();
    }
    void build() {
        queue<int> q;
        tr[0].fail = 0;
        for (int c = 0; c < 26; c++) {
            int u = tr[0].nxt[c];
            if(u != -1) tr[u].fail = 0, q.push(u);
            else tr[0].nxt[c] = 0;
        }
        while (!q.empty()) {
            int v = q.front();
            q.pop();
            for (int c = 0; c < 26; c++) {
                int u = tr[v].nxt[c];
                if (u != -1) {
                    tr[u].fail = tr[tr[v].fail].nxt[c];
                    tr[u].idx.reserve(tr[u].idx.size() + tr[tr[u].fail].idx.size());
                    for(int x : tr[tr[u].fail].idx) tr[u].idx.push_back(x);
                    q.push(u);
                }
                else tr[v].nxt[c] = tr[tr[v].fail].nxt[c];
            }
        }
    }
};

auto manacher(const string &t) {
    string s = "%#";
    s.reserve(t.size() * 2 + 3);
    for(char c : t) s += c + "#"s;
    s += '$';
    // t = aabaacaabaa -> s = %#a#a#b#a#a#c#a#a#b#a#a#$

    vector<int> res(s.size());
    for(int i = 1, l = 1, r = 1; i < s.size(); i++) {
        res[i] = max(0, min(r - i, res[l + r - i]));
        while(s[i + res[i]] == s[i - res[i]]) res[i]++;
        if(i + res[i] > r) {
            l = i - res[i];
            r = i + res[i];
        }
    }
    for(auto &i : res) i--;
    return vector(res.begin() + 2, res.end() - 2); // a#a#b#a#a#c#a#a#b#a#a
    // get max odd len = res[2 * i]; aba -> i = b
    // get max even len = res[2 * i + 1]; abba -> i = first b
}

struct suffix_automaton {
    struct state : map<int, int> {
        int fail = -1, len{}, cnt = 1;
        bool ed = false;
    };
    int lst, n{};
    vector<state> tr;
    explicit suffix_automaton(const string& s = ""s) : tr(1), lst(0) {
        tr.reserve(s.size() * 2);
        for(auto i : s) add(i);
    }
    void add(int c) {
        int x = int(tr.size());
        tr.emplace_back(), n++;
        tr[x].len = tr[lst].len + 1;
        int p = lst, q;
        while(~p && (q = tr[p].emplace(c, x).first->second) == x) p = tr[p].fail;
        if(p == -1) tr[x].fail = 0;
        else {
            if(tr[p].len + 1 == tr[q].len) tr[x].fail = q;
            else {
                int y = int(tr.size()); tr.emplace_back(tr[q]);
                tr[y].cnt = 0, tr[y].len = tr[p].len + 1;
                while(~p && tr[p][c] == q) tr[p][c] = y, p = tr[p].fail;
                tr[x].fail = tr[q].fail = y;
            }
        }
        lst = x;
    }
    void init() { // to build cnt, end
        for(int p = lst; ~p; tr[p].ed = true, p = tr[p].fail);
        vector b(n + 1, vector(0, 0));
        for(int i = 0; i < tr.size(); ++i) b[tr[i].len].push_back(i);
        for(int l = n; l >= 1; --l)
            for(int u : b[l])
                tr[tr[u].fail].cnt += tr[u].cnt;
    }
};
