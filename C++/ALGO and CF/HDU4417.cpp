#include <bits/stdc++.h>
using namespace std;
const int maxn = 1e5 + 10;
struct node {
	int ls,rs,sum;
}seg[maxn<<5];
int n,m,T,ind[maxn],num[maxn],ran[maxn],it,len;
int update(int l, int r, int o, int root) {
	int mid = (l + r) >> 1, newo = ++it;
	seg[newo] = seg[root], seg[newo].sum ++;
	if(l == r) return newo;
	o <= mid ? (seg[newo].ls = update(l, mid, o ,seg[root].ls)) : (seg[newo].rs = update(mid + 1, r, o, seg[root].rs));
	return newo;
}
int query(int l, int r, int u, int v, int rank) {
	int mid = (l + r) >> 1, info = seg[seg[v].ls].sum - seg[seg[u].ls].sum, ans = seg[v].sum - seg[u].sum;
	if(l == r) return ans;
	return (rank <= mid ? query(l, mid, seg[u].ls, seg[v].ls, rank) : (info + query(mid + 1, r, seg[u].rs, seg[v].rs, rank)));
}
int main() {
	cin >> T;
	int kase = 1;
	while(T--) {
	scanf("%d%d", &n, &m);
	for(int i = 1; i <= n; i++) scanf("%d", &num[i]);
	memcpy(ran, num, sizeof ran), sort(ran + 1, ran + n + 1),len = 1;
	for(int i = 2; i <= n; i++) if(ran[i] != ran[i - 1]) ran[++len] = ran[i];
	it = 0, ind[0] = 0, seg[0] = {0, 0, 0};
	cout << "Case " << kase++ << ":" << endl;
	for(int i = 1; i <= n; i++) ind[i] = update(1, len, lower_bound(ran + 1, ran + len + 1, num[i]) - ran, ind[i - 1]);
	while(m--) {
		int l, r, k;
		scanf("%d%d%d", &l, &r, &k);
		l++, r++;
		int p = upper_bound(ran + 1, ran + len + 1, k) - ran - 1;
		if(p) printf("%d\n", query(1, len, ind[l -1], ind[r], p));
		else cout << 0 << endl;
	}
	}
	return 0;
}
