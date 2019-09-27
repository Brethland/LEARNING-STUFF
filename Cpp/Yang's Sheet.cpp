#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
const ll mod = 998244353;
ll inv[1005],a[1005],n,ans;
ll pow_mod(ll a, ll b) {
    ll res = 1;
    while(b) {
        if(b & 1) res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
void dfs(int x, int y) {
    if(!x) {
        ll res = 1;
        for(int i = 1; i <= n; i++) res = res * i % mod;
        for(int i = 1; i < y; i++) for(int j = 1; j <= a[i]; j++) {
            int ct = a[i] - j;
            for(int k = i; k < y; k++) if(a[k] >= j) ct++;
            res = res * inv[ct] % mod;
        }
        ans = (ans + res * res % mod * a[1] % mod) % mod;
    }
    for(int i = 1; i <= x; i++) {
        if(y != 1 && i > a[y - 1]) continue;
        a[y] = i; dfs(x - i, y + 1);
    }
}
int main() {
    cin >> n;
    for(int i = 1; i <= n; i++) inv[i] = pow_mod(i,mod-2);
    dfs(n , 1);
    for(int i = 1; i <= n; i++) ans = ans * inv[i] % mod;
    cout << ans << endl;
    return 0;
}