#include <bits/stdc++.h>
using namespace std;
void test(int** p) {
    *p = new int(10);
}
int main() {
    int *p = NULL;
    test(&p);
    cout << *p << endl;
}