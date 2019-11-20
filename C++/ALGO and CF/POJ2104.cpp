#include <bits/stdc++.h>
using namespace std;
const int maxn = 1e5+10;
struct node {
	int ls,rs,sum;
	node(){}
	node(const node& a) { ls = a.ls,rs = a.rs, sum = a.sum; }
}seg[maxn<<5];
int num[maxn],ind[maxn],backup[maxn],len,n,m,it;
int build(int l, int r) {
	int root = ++it,mid = (l + r) >> 1;
	if(l == r) return root;
	seg[root].ls = build(l, mid), seg[root].rs = build(mid + 1, r);return root;
}
int update(int l ,int r, int o, int root) {
	int newo = ++it,mid = (l + r) >> 1;
	seg[newo] = seg[root], seg[newo].sum++;
	if(l == r) return newo;
	o <= mid ? (seg[newo].ls = update(l, mid, o, seg[newo].ls)) : (seg[newo].rs = update(mid + 1, r, o, seg[newo].rs));	
	return newo;
}
int query(int l, int r, int u, int v, int rank) {
	int mid = (l + r) >> 1, info = seg[seg[v].ls].sum - seg[seg[u].ls].sum;
	if(l == r) return l;
	return (rank <= info ? query(l, mid, seg[u].ls, seg[v].ls, rank) : query(mid + 1, r, seg[u].rs, seg[v].rs, rank - info));
}
int main() {
	scanf("%d%d", &n, &m);
	for(int i = 1; i <= n; i++) scanf("%d", &num[i]);
	memcpy(backup, num, sizeof backup), sort(num + 1, num + n + 1), len = unique(num + 1, num + n + 1) - num - 1;
	ind[0] = build(1, len);
	for(int i = 1; i <= n; i++) ind[i] = update(1, len, lower_bound(num + 1, num + len + 1, backup[i]) - num, ind[i-1]);
	while(m--) {
		int l, r, q;
		scanf("%d%d%d", &l, &r, &q);
		printf("%d\n", num[query(1, len, ind[l - 1], ind[r], q)]);
	}	
	return 0;
}

