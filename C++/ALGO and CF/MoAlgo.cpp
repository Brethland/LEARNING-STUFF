#include <bits/stdc++.h>
using namespace std;
#define GET c=getchar()
#define SHU ('0'<=c&&c<='9')
#define bi(a) ((a - 1) / part + 1)
int a[500005],n,q,ans[500005],part,top,mo[500005],st[500005],cnt[500005];
struct ask{
    int l,r,id,block;
}query[500005];
bool cmp(ask c,ask d){ return (c.block^d.block)?c.block<d.block:((c.block&1)?c.r<d.r:c.r>d.r); }
int read() {
	int x=0,f=1;char GET;
	while(!SHU) {
		if(c=='-') f=-1;
		GET;
	}
	while(SHU) {
		x=x*10+c-'0';
		GET;
	}
	return x*f;
}
void add(int pos) {
    cnt[pos]++;
    if(cnt[pos]==1) {
        st[++top] = pos;
        mo[pos] = top;
    }else if(cnt[pos]==2) {
        st[mo[pos]] = st[top];
        mo[st[top]] = mo[pos];
        st[top--] = mo[pos] = 0;
    }
}
void del(int pos) {
    cnt[pos]--;
    if(cnt[pos]==1) {
        st[++top] = pos;
        mo[pos] = top;
    }else if(!cnt[pos]) {
        st[mo[pos]] = st[top];
        mo[st[top]] = mo[pos];
        st[top--] = mo[pos] = 0;
    }
}
int main() {
    n=read(),part = sqrt(n);
    for(int i = 1; i <= n; i++) a[i]=read();
    q=read();
    for(int i = 1; i <= q; i++) query[i].l = read(),query[i].r=read(),query[i].id = i,query[i].block = query[i].l/part;
    sort(query+1,query+q+1,cmp);
    int l =1,r = 1;
    add(a[1]);
    for(int i = 1; i <=q; i++) {        
        while(r<query[i].r) add(a[++r]);
        while(r>query[i].r) del(a[r--]);
        while(l<query[i].l) del(a[l++]);
        while(l>query[i].l) add(a[--l]);
        ans[query[i].id] = st[top];
    }
    for(int i = 1; i<=q;i++) printf("%d\n",ans[i]);
    return 0;
}