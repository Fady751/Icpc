#include <bits/stdc++.h>
using namespace std;

/*
 conj(a) -> a.imag() *= -1
 abs(point) distance between (0,0) to this point
 hypot(x, y) -> sqrt(x * x + y * y)
 arg(vector) angle between this vector and x-axis
 clamp(a, l, r) == min(r, max(l, a))
 polar(rho, theta) -> make vector with length rho and angle theta
 */

using ld = double;
using point = complex<ld>;

const ld pi = acos(-1);

#define dot(a, b) (conj(a) * (b)).real()

#define cross(a, b) (conj(a) * (b)).imag()

auto comp(point a, point b) { return pair{a.real(), a.imag()} < pair{b.real(), b.imag()}; }

istream &operator>>(istream &is, point &p) {
    ld x, y; is >> x >> y;
    return p.real(x), p.imag(y), is;
}

point line_inter(point a, point b, point c, point d) { // a / sin(a) == b / sin(b) == c / sin(c)
    point ab = b - a, cd = d - c, ac = c - a;
    return a + ab * (cross(ac, cd) / cross(ab, cd));
}

ld triangleArea(point a, point b, point c) {
    return 0.5 * abs(cross(b - a, c - a));
}
