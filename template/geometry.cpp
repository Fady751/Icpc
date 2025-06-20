#include <bits/stdc++.h>
using namespace std;

/*
 conj(a) -> a.imag() *= -1
 abs(point) distance between (0,0) to this point
 norm(point) squared magnitude -> real² + imag²
 hypot(x, y) -> sqrt(x² + y²)
 arg(vector) angle between this vector and x-axis
 clamp(a, l, r) == min(r, max(l, a))
 polar(rho, theta) -> make vector with length rho and angle theta
 internal angle = (n - 2) * 180 / n
 number of diagonals n * (n - 3) / 2
 Area(p) = internal_points_cnt + (boundary_points/2) - 1
 boundary_point in vector = gcd(|x2-x1|, |y2-y1|) + 1
 line have infinity point, segment have to end points
 vector(x, y) perpendicular to vector(-y, x) and (y, -x)
*/

using ll = int64_t;
using ld = double;
using point = complex<ld>;

const ll inf = 7e18;
const ld EPS = 1e-9;
const ld pi = acos(-1);

#define X real()
#define Y imag()

#define dot(a, b) (conj(a) * (b)).X
#define cross(a, b) (conj(a) * (b)).Y

struct compX{
    bool operator()(point a, point b) const {
        return a.X != b.X ? a.X < b.X : a.Y < b.Y;
    }
};
struct compY{
    bool operator()(point a, point b) const {
        return a.Y != b.Y ? a.Y < b.Y : a.X < b.X;
    }
};

int sign(ld x) {
    return (x > EPS) - (x < -EPS);
}

// ================ line, segment ==========================

// projection of point p onto line ab
point project(point a, point b, point p) {
    point ab = b - a;
    return a + ab * dot(p - a, ab) / norm(ab);
}

// works for any orientation
bool onSegment(point a, point b, point p) {
    return sign(cross(b - a, p - a)) == 0 &&
           sign(dot(p - a, p - b)) <= 0;
}

// ccw: >0 left, <0 right, =0 collinear
int ccw(point a, point b, point c) {
    return sign(cross(b - a, c - a));
}

// works for any points
ld distanceToLine(point a, point b, point p) {
    return fabs(cross(b - a, p - a)) / abs(b - a);
}

// works for any points
ld distanceToSegment(point a, point b, point p) {
    if (dot(b - a, p - a) < 0) return abs(p - a);
    if (dot(a - b, p - b) < 0) return abs(p - b);
    return distanceToLine(a, b, p);
}

// works for intersecting lines (not parallel)
point lineIntersect(point a, point b, point c, point d) {
    point ab = b - a, cd = d - c;
    return a + ab * (cross(c - a, cd) / cross(ab, cd));
}

// works for all segments (returns intersection point if exists)
bool segmentsIntersect(point a, point b, point c, point d, point &inter) {
    int d1 = ccw(a, b, c), d2 = ccw(a, b, d);
    int d3 = ccw(c, d, a), d4 = ccw(c, d, b);

    if(d1 * d2 < 0 && d3 * d4 < 0)
        return inter = lineIntersect(a, b, c, d), true;

    if(d1 == 0 && onSegment(a, b, c)) return inter = c, true;
    if(d2 == 0 && onSegment(a, b, d)) return inter = d, true;
    if(d3 == 0 && onSegment(c, d, a)) return inter = a, true;
    if(d4 == 0 && onSegment(c, d, b)) return inter = b, true;

    return false;
}

// works for any triangle
ld triangleArea(point a, point b, point c) {
    return 0.5 * fabs(cross(b - a, c - a));
}

bool pointInTriangle(point a, point b, point c, point p) {
    ld s1 = cross(b - a, p - a);
    ld s2 = cross(c - b, p - b);
    ld s3 = cross(a - c, p - c);
    return (sign(s1) >= 0 && sign(s2) >= 0 && sign(s3) >= 0) ||
           (sign(s1) <= 0 && sign(s2) <= 0 && sign(s3) <= 0);
}

// angle abc in radians
ld angle_abc(point a, point b, point c) {
    return acos(clamp<ld>(dot(a - b, c - b) / (abs(a - b) * abs(c - b)), -1, 1));
}

// ============================= Circles ================================

pair<ld, point> findCircle(point a, point b, point c) {
    point m1 = (a + b) / 2.0, m2 = (b + c) / 2.0;
    point ab = b - a, bc = c - b;
    point center = lineIntersect(m1, m1 + point(-ab.Y, ab.X),
                                 m2, m2 + point(-bc.Y, bc.X));
    return {abs(center - a), center};
}

vector<point> lineCircleIntersect(point a, point b, point center, ld r) {
    point ab = b - a, ao = center - a;
    point proj = a + ab * dot(ao, ab) / norm(ab);
    ld d = abs(proj - center);
    if (d > r + EPS) return {};
    if (abs(d - r) < EPS) return {proj};
    ld h = (ld)sqrtl(r*r - d*d);
    point dir = ab / abs(ab);
    return {proj + dir * h, proj - dir * h};
}

// in 0, 1, 2 points
vector<point> circleCircleIntersect(point c1, ld r1, point c2, ld r2) {
    ld d = abs(c2 - c1);
    if(d > r1 + r2 + EPS || d < abs(r1 - r2) - EPS) return {};
    if(abs(d) < EPS && abs(r1 - r2) < EPS) return vector(3, c1); // infinity intersection

    ld a = (r1*r1 - r2*r2 + d*d) / (2 * d), h2 = r1*r1 - a*a;
    if (h2 < -EPS) return {};

    point dir = (c2 - c1) / d, p = c1 + dir * a;
    if (abs(h2) < EPS) return {p};
    ld h = sqrt(h2);
    point offset = dir * point(0, 1) * h;
    return {p + offset, p - offset};
}

pair<ld, point> minimumEnclosingCircle(vector<point> p) {
    using circle = pair<ld, point>;
    shuffle(p.begin(), p.end(), mt19937(random_device{}()));
    auto contains = [](circle c, const vector<point>& pts) {
        return all_of(pts.begin(), pts.end(),
                      [&](auto p) {return abs(p - c.second) <= c.first + EPS;});
    };
    auto circleFrom2 = [](point a, point b) {
        point c = (a + b) / 2.0;
        return circle{abs(a - c), c};
    };
    auto circleFrom3 = [](point a, point b, point c) {
        point ab = (a + b) / 2.0, ac = (a + c) / 2.0;
        point ab_perp = (b - a) * point(0, 1), ac_perp = (c - a) * point(0, 1);
        point o = lineIntersect(ab, ab + ab_perp, ac, ac + ac_perp);
        return circle{abs(o - a), o};
    };
    vector<point> R;
    function<circle(int)> welzl = [&](int n) -> circle {
        if (n == 0 || R.size() == 3) {
            if (R.empty()) return {};
            if (R.size() == 1) return {0, R[0]};
            if (R.size() == 2) return circleFrom2(R[0], R[1]);
            return circleFrom3(R[0], R[1], R[2]);
        }
        point q = p[n - 1];
        circle D = welzl(n - 1);
        if (contains(D, {q})) return D;
        R.push_back(q);
        auto res = welzl(n - 1);
        R.pop_back();
        return res;
    };
    return welzl((int)p.size());
}

// ===================== polygon ============================

// works for any polygon (returns +1 for ccw, -1 for cw)
ld polygonSign(vector<point>& p) {
    ld area = 0;
    int n = (int)p.size();
    p.push_back(p[0]);
    for(int i = 0; i < n; ++i) area += cross(p[i], p[i + 1]);
    p.pop_back();
    return sign(0.5 * area);
}

// works for any polygon (removes dups, enforces ccw order)
void normPolygon(vector<point>& p) {
    vector<point> res;
    for(auto i : p) if(res.empty() || abs(i - res.back()) > EPS)
            res.push_back(i);

    if(res.size() > 1 && abs(res.front() - res.back()) < EPS)
        res.pop_back();

    if(polygonSign(res) < 0) reverse(res.begin(), res.end());

    p = res;
}

// works for simple polygons with integer coordinates
ll internalPointsCount(vector<point>& p) {
    ll A2 = 0, B = 0;
    int n = (int)p.size();
    p.push_back(p[0]);
    for (int i = 0; i < n; ++i) {
        point a = p[i], b = p[i + 1];
        A2 += ll(a.X * b.Y - a.Y * b.X);
        B += __gcd((ll)abs(b.X - a.X), (ll)abs(b.Y - a.Y));
    }
    p.pop_back();
    return (abs(A2) - B + 2) / 2;
}

// works for any polygon (cw or ccw, convex or not)
ld polygonArea(vector<point> &p) {
    int n = (int)p.size();
    p.push_back(p[0]);
    ld area = 0;
    for (int i = 0; i < n; ++i) area += cross(p[i], p[i + 1]);
    p.pop_back();
    return fabs(area) / 2.0;
}

// works for any polygon (cw or ccw, convex or not)
bool pointInPolygon(vector<point> &p, point o) {
    int in = 0, n = (int)p.size();
    p.push_back(p[0]);
    for (int i = 0; i < n; ++i) {
        point a = p[i], b = p[i + 1];
        if (onSegment(a, b, o)) return p.pop_back(), true;
        if ((a.Y > o.Y) != (b.Y > o.Y)) {
            ld x = a.X + (b.X - a.X) *
                             (o.Y - a.Y) / (b.Y - a.Y);
            if(x > o.X) in ^= 1;
        }
    }
    p.pop_back();
    return in;
}

// work for simple convex polygon
bool pointInConvex(vector<point> &poly, point p) {
    int n = int(poly.size());
    if(n == 1) return sign(abs(poly[0] - p)) == 0;
    if(n == 2) return onSegment(poly[0], poly[1], p);

    point f = poly[0];

    if(sign(cross(poly[1] - f, p - f)) < 0 || sign(cross(poly[n - 1] - f, p - f)) > 0) return false;

    int l = 1, r = n - 1;
    while(r > l + 1) {
        int mid = (l + r) >> 1;
        if(sign(cross(poly[mid] - f, p - f)) > 0) l = mid;
        else r = mid;
    }
    return pointInTriangle(f, poly[l], poly[r], p);
}

// works for any simple polygon (cw or ccw)
point polygonCentroid(vector<point>& p) {
    ld A = 0, c;
    point C(0, 0);
    int n = (int)p.size();
    p.push_back(p[0]);
    for (int i = 0; i < n; ++i) {
        point cur = p[i], nxt = p[i + 1];
        c = cross(cur, nxt);
        A += c;
        C += (cur + nxt) * c;
    }
    p.pop_back();
    A *= 0.5;
    if (abs(A) < EPS) return C;
    return C / (6.0 * A);
}

// ccw convex polygon (cuts polygon into left/right of directed line)
auto polygonCut(vector<point> &p, point a, point b) {
    vector<point> l, r;
    point inter;
    int n = int(p.size());
    p.push_back(p[0]);
    auto f = [](auto &x, auto p) {return (x.empty() || sign(abs(x.back() - p)));};
    for(int i = 0; i < n; i++) {
        point curr = p[i], nxt = p[i + 1];
        if(ccw(a, b, curr) <= 0 && f(r, curr)) r.push_back(curr);
        if(ccw(a, b, curr) >= 0 && f(l, curr)) l.push_back(curr);
        if(segmentsIntersect(a, b, curr, nxt, inter)) {
            if(f(l, inter)) l.push_back(inter);
            if(f(r, inter)) r.push_back(inter);
        }
    }

    p.pop_back();
    return pair{l, r};
}

// convex hull return (CCW, convex polygon)
void convexHull(vector<point> &p) {
    int n = (int)p.size(), k = 0;
    if (n <= 1) return;
    sort(p.begin(), p.end(), compX());
    vector<point> hull(2 * n);
    for (int i = 0; i < n; ++i) {
        while (k >= 2 && ccw(hull[k - 2], hull[k - 1], p[i]) <= 0) --k;
        hull[k++] = p[i];
    }
    for (int i = n - 2, t = k; i >= 0; --i) {
        while (k > t && ccw(hull[k - 2], hull[k - 1], p[i]) <= 0) --k;
        hull[k++] = p[i];
    }
    hull.resize(k - 1), p = hull;
    if(p.size() > 1 && sign(abs(p[p.size() - 1] - p[p.size() - 2])) == 0) p.pop_back();
}

struct Line {
    ll a = 0, b = -inf;
    inline ll eval(ll x) { return a * x + b; }
};
// Li Chao Tree
struct LiChao {
    int n;
    vector<Line> tr;

    LiChao(int size) : n(size), tr(n << 2) { }

    void update(int x, int lx, int rx, int l, int r, Line v) {
        if (l > rx || lx > r) return;
        if (lx == rx) {
            if (tr[x].eval(lx) < v.eval(lx)) swap(tr[x], v);
            return;
        }
        int mdx = (lx + rx) >> 1;
        if (lx >= l && rx <= r) {
            bool good_L = v.eval(lx) > tr[x].eval(lx);
            bool good_M = v.eval(mdx) > tr[x].eval(mdx);
            if (good_M) swap(tr[x], v);
            good_L != good_M? update(x << 1, lx, mdx, l, r, v):
            update(x << 1 | 1, mdx + 1, rx, l, r, v);
            return;
        }
        update(x << 1, lx, mdx, l, r, v);
        update(x << 1 | 1, mdx + 1, rx, l, r, v);
    }

    ll query(int x, int lx, int rx, int i) {
        if (lx == rx) return tr[x].eval(i);
        int mdx = (lx + rx) >> 1;
        return max(tr[x].eval(i),
                   i <= mdx? query(x << 1, lx, mdx, i):
                   query(x << 1 | 1, mdx + 1, rx, i));
    }

    void add_line(int l, int r, Line v) {
        update(1, 0, n, l, r, v);
    }

    ll get_max(int i) {
        return query(1, 0, n, i);
    }
};
