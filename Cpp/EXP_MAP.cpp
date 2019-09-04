// A experiment for map performance.

#include <bits/stdc++.h>
using namespace std;
int main() {
    for(int k = 1;k<=100;k++) {
    clock_t st,et;
    st = clock();
    map<int,map<int,map<int,int> > > mp;
    for(int i = 1; i<=1000000;i++) {
        mp[i][i][i] = i;
    }
    et = clock();
    cout << (double)(et-st) << endl;
    }
    return 0;
}