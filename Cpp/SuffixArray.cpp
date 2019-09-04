#include <bits/stdc++.h>
using namespace std;
#define maxn 200005
int SA[maxn],height[maxn],id[maxn],rk[maxn],t[maxn],t2[maxn],c[maxn],str[maxn];
int n,maxlen,it,np,kase;
string tmp;
set<string> ans;
void build_sa(int m) {
	int i, *x = t, *y = t2;
	for (i = 0; i < m; i++) c[i] = 0;
	for (i = 0; i < n; i++) c[x[i] = str[i]]++;
	for (i = 1; i < m; i++) c[i] += c[i - 1];
	for (i = n - 1; i >= 0; i--) SA[--c[x[i]]] = i;
	for (int k = 1; k <= n; k <<= 1) {
	    int p = 0;
	    for (i = n - k; i < n; i++) y[p++] = i;
	    for (i = 0; i < n; i++) if (SA[i] >= k) y[p++] = SA[i] - k;
	    for (i = 0; i < m; i++) c[i] = 0;
	    for (i = 0; i < n; i++) c[x[y[i]]]++;
	    for (i = 0; i < m; i++) c[i] += c[i - 1];
	    for (i = n - 1; i >= 0; i--) SA[--c[x[y[i]]]] = y[i];
	    swap(x, y);
	    p = 1; x[SA[0]] = 0;
	    for (i = 1; i < n; i++)
		x[SA[i]] = y[SA[i - 1]] == y[SA[i]] && y[SA[i - 1] + k] == y[SA[i] + k] ? p - 1 : p++;
	    if (p >= n) break;
	    m = p;
	}
}
void calHeight() {
    int i, j, k = 0;
	for (i = 0; i < n; i++) rk[SA[i]] = i;
	for (i = 0; i < n; i++) {
	    if (k) k--;
	    if (rk[i] == 0) continue;
	    int j = SA[rk[i] - 1];
	    while (str[i + k] == str[j + k]) k++;
	    height[rk[i]] = k;
	}
}

bool check(int x, bool judge) {
    set<int>vis;
    vis.insert(id[SA[1]]);
    for(int i = 2; i<n;i++) {
        while(i<n&&height[i]>=x) vis.insert(id[SA[i++]]);
        if(vis.size()*2>np) {
            if(!judge) return true;
            // ans.insert(string(str[SA[i-1]],str[SA[i-1]+x-1]));
            for (int j = 0; j < x; j++)
		    printf("%c", str[SA[i - 1] + j]);
	        printf("\n");
        }
        vis.clear(),vis.insert(id[SA[i]]);
    }
    return false;
}

int main() {
    while(cin >> np && np) {
        if(kase) cout << endl;
        else kase = 1;
        maxlen = it = 0;
        for(int i = 0; i<np;i++) {
            cin >> tmp;
            maxlen = max(maxlen,(int)tmp.length());
            for(int j = 0; j<tmp.length(); j++) {
                id[it] = i;
                str[it++] = tmp[j];
            }
            id[it] =i;str[it++] = 'z'+i+1;
        }
        n = it;
        build_sa(np+'z'+1);
        calHeight();
        if(!check(1,0)) { printf("?\n"); continue;}
        int l=1,r=maxlen+1;
        while(l<r) {
            int mid = (l+r)>>1;
            if(check(mid,0)) l= mid+1;
            else r = mid;
        }
        l--;
        check(l,1);
    }
    return 0;
}