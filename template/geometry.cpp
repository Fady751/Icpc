#include <bits/stdc++.h>
using namespace std;

using ld = long double;

ld pi = acos(-1);

struct point : public array<ld, 2> {
    ld dis(point x) {
        return sqrt((x[0] - (*this)[0]) * (x[0] - (*this)[0])
                    + (x[1] - (*this)[1]) * (x[1] - (*this)[1]));
    }
    void move(ld x, point v) {
        v[0] *= x;
        v[0] += (*this)[0];
        v[1] *= x;
        v[1] += (*this)[1];
        (*this) = v;
    }
    point V(point o) {
        if(o == *this)
            return point{0, 0};
        ld ds = this->dis(o);
        return {(o[0] - (*this)[0]) / ds, (o[1] - (*this)[1]) / ds};
    }
    friend istream &operator>>(istream &is, point &o) {
        return is >> o[0] >> o[1];
    }
};

ld triangleArea(ld x1, ld y1, ld x2, ld y2, ld x3, ld y3) {
    return 0.5 * abs(x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2));
}
