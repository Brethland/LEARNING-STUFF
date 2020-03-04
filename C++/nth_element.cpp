#include <bits/stdc++.h>
using namespace std;

// C++20 Required
int nth_element(vector<int> &num, int k) {
    int s = num[k - 1];
    auto filtered = num | view::filter([](int a){ return a < s; });
    if(filtered.size() == k) return filtered[k - 1];
    else if(filtered.size() > k) return nth_element(filtered, k);
    else {
        int len = filtered.size();
        filtered = num | view::filter([](int a){ return a >= s; });
        return nth_element(filtered, k - len);
    }
}