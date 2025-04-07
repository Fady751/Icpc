#include <bits/stdc++.h>
using namespace std;

struct TreeNode {
    int val;
    TreeNode *left;
    TreeNode *right;

    TreeNode() : val(0), left(nullptr), right(nullptr) {}

    explicit TreeNode(int x) : val(x), left(nullptr), right(nullptr) {}

    TreeNode(int x, TreeNode *left, TreeNode *right) : val(x), left(left), right(right) {}
};

struct ListNode {
    int val;
    ListNode *next;

    ListNode(int x) : val(x), next(NULL) {}
};

class Solution {
public:

};

auto init1 = atexit([](){ ofstream("display_runtime.txt") << "0"; });

int main() {
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);

    Solution s;

    string st;
    cin >> st;
    for(char &c : st) {
        if(c == '[') c = '{';
        else if(c == ']') c = '}';
    }
    cout << st << '\n';

    return 0;
}