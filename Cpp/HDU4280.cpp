#include <bits/stdc++.h>
using namespace std;
#define INF 0x7fffffff
struct edge{
    int to,next,c;
}e[800005];
int d[100005],s,t,n,m,T,head[100005],pos,cur[100005],x,y,c;
bool vis[100005];
void addEdge(int a,int b,int c){ e[pos].to=b,e[pos].next=head[a],e[pos].c=c;head[a]=pos;pos++; }
void init() { memset(head,-1,sizeof(head)),pos=0; }
bool bfs() {
    queue<int>q;
    for(int i=1;i<=n;i++) vis[i]=0;
    d[s]=1,vis[s]=1;
    q.push(s);
    while(!q.empty()) {
        int u=q.front();q.pop();
        for(int i = head[u];i != -1;i = e[i].next) {
            int v = e[i].to;
            if(vis[v] || e[i].c <= 0) continue;
            d[v] = d[u]+1;
            vis[v] = 1;
            q.push(v);
        }
    }
    return vis[t];
}
int dfs(int u,int a) {
    if(u == t || !a)return a;
    int f,flow = 0;
    for(int &i = cur[u];i != -1;i = e[i].next) {
        int v = e[i].to;
        if(d[v] == d[u] + 1 && (f = dfs(v,min(a,e[i].c))) > 0) {
            e[i].c -= f;
            e[i^1].c += f;
            flow += f;
            a -= f;
            if(!a)break;
        }
    }
    return flow;
}
int Dinic() {
    int ans = 0;
    while(bfs()) {
        for(int i = 1;i <= n; i++) cur[i] = head[i];
        ans += dfs(s,0x7fffffff);
    }
    return ans;
}
int main() {
    scanf("%d",&T);
    while(T--) {
        scanf("%d%d",&n,&m);
        init();
        int minp = 0x7fffffff,maxp = -0x7fffffff;
        for (int i = 1; i <= n; i++) {
            scanf("%d%d",&x,&y);
            if(x > maxp) maxp = x,t = i;
            if(x < minp) minp = x,s = i;
        }
        for(int i = 1; i <= m; i++) {
            scanf("%d%d%d",&x,&y,&c);
            addEdge(x,y,c),addEdge(y,x,c);
        }
        printf("%d\n", Dinic());
    }
    return 0;
}