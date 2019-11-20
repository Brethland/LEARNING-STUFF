#include <bits/stdc++.h>
using namespace std;
#define maxn 15000
struct Edge{
    int to,cap,flow,cost;
};
vector<Edge> e;
vector<int> head[maxn];
long long ans,dis[maxn];
int n,m,k,c,d,p[maxn],pe[maxn],inq[maxn],s=9998,t=9999,cur,i,j;
void add_edge(int x, int y, int c, int cost) {
	head[x].push_back(e.size()),e.push_back(Edge{y, c, 0, cost});
	head[y].push_back(e.size()),e.push_back(Edge{x, 0, 0, -cost});
}
void push_rebel() {
    fill(dis,dis+10000,(long long)1e18),fill(p,p+10000,-1),fill(pe,pe+10000,-1),fill(inq,inq+10000,0);
    dis[s] = 0;
    queue<int> q;
    q.push(s),inq[s] = 1,cur = t;
    while(!q.empty()) {
        int k = q.front();q.pop();
        inq[k] = 0;
        for(auto x: head[k]) {
            if(!(e[x].cap - e[x].flow)) continue;
            int c = e[x].cost,y = e[x].to;
            if(dis[y]>dis[k]+c) {
                dis[y] = dis[k] + c,p[y] = k,pe[y] = x;
                if(!inq[y]) inq[y] = 1,q.push(y);
            }
        }
    }
	while(cur != s) {
		e[pe[cur]].flow++;
		e[pe[cur] ^ 1].flow--;
		cur = p[cur];
    }
	ans += dis[t];
}
int main() {
    cin >> n >> m >> k >> c >> d;
    int x,y;
    for(int i = 1; i<=k;i++) { cin >> x;x--;add_edge(s,x,1,0);}
    for(int i = 1; i<=101;i++) add_edge((i-1)*n,t,k,(i-1)*c);
    for(int i = 1; i<=m; i++) {
		cin >> x >> y;x--,y--;
		for(int i = 1; i<=100; i++) for(int j = 1; j<=k; j++)
			add_edge(x+(i-1)*n,y+(i-1)*n+n,1,d*((j-1)*2+1)),add_edge(y+(i-1)*n,x+(i-1)*n+n,1,d*((j-1)*2+1));
 	}
 	for(int i = 1; i<=n; i++) for(int j = 1; j<=100; j++) add_edge(i-1+(j-1)*n,i-1+(j-1)*n+n,k,0);
    for(int i = 1;i<=k;i++) push_rebel();
    cout << ans << endl;
    return 0;
}