#include <bits/stdc++.h>
using namespace std;
#define debug(x) cout << (#x) << " = " << (x) << '\n'

mt19937 rnd(time(nullptr));

template<typename T>
T rng(T l, T r) { return uniform_int_distribution<T>(l, r)(rnd); }

template<class U, typename T>
U& operator >> (U &input, vector<T> &x){
    x.clear();
    T element;
    while(input >> element) {
        x.push_back(element);
        if(input.peek() == '\n') break;
    }
    return input;
}

// monotonic stack
template<typename T, typename F>
auto monP(const vector<T> &a, const F &fun) {
    int n = int(a.size());
    stack<int> st;
    vector<int> res(n);
    for(int i = 0; i < n; i++) {
        while(!st.empty() && !fun(a[st.top()], a[i])) st.pop();
        res[i] = st.empty()? -1: st.top();
        st.push(i);
    }
    return res;
}

template<typename T, typename F>
auto monS(const vector<T> &a, const F &fun) {
    auto res = monP(vector(a.rbegin(), a.rend()), fun);
    reverse(res.begin(), res.end());
    for(auto &i : res) i = int(a.size()) - i - 1;
    return res;
}

// dp tricks
void sos(vector<int> &dp, bool invert = false) {
    // !invert -> sum of subsets, invert -> undo pre operation
    for (int i = 0; 1 << i < dp.size(); i++) {
        for (int mask = 0; mask < dp.size(); mask++) {
            if (mask & (1 << i)) {
                dp[mask] += invert? -dp[mask ^ (1 << i)] : dp[mask ^ (1 << i)];
//                dp[mask] >= mod? dp[mask] -= mod: dp[mask] < 0? dp[mask] += mod: 0;
            }
        }
    }
/*
 f[x]++;
 f1[(N - 1) & ~x]++;
 ================== number of y such that
 x | y = x   => f[x]
 x & y = x   => f1[(N - 1) & ~x]
 x & y = 0   => f[(N - 1) & ~x]
*/
}

struct Line {
    mutable int64_t m, c, p;
    bool operator<(const Line& o) const { return m < o.m; }
    bool operator<(int64_t x) const { return p < x; }
};
struct HullDynamic : multiset<Line, less<>> { // for max value
    const int64_t inf = 2e18;
    int64_t div(int64_t a, int64_t b) {
        return a / b - ((a ^ b) < 0 && a % b); }
    bool isect(iterator x, iterator y) {
        if (y == end()) { x->p = inf; return false; }
        if (x->m == y->m) x->p = x->c > y->c ? inf : -inf;
        else x->p = div(y->c - x->c, x->m - y->m);
        return x->p >= y->p;
    }
    void add(int64_t k, int64_t m) {
        auto z = insert({k, m, 0}), y = z++, x = y;
        while(isect(y, z)) z = erase(z);
        if(x != begin() && isect(--x, y)) isect(x, y = erase(y));
        while((y = x) != begin() && (--x)->p >= y->p) isect(x, erase(y));
    }
    int64_t query(int64_t x) {
        assert(!empty());
        auto l = *lower_bound(x);
        return l.m * x + l.c;
    }
};
