#include <bits/stdc++.h>
using namespace std;
struct Edge{
    int from,to,cap,f;
}edge[10005];
int a[1005],p[1005],cnt = 1,n,m;
vector<int> G[1005];
void init(int n) {
    cnt = 1;
    memset(p,0,sizeof(p));
    for(int i = 0; i<=n;i++) G[i].clear();
}
void addEdge(int u,int v,int cap) {
    edge[++cnt] = (Edge){u,v,cap,0};
    edge[++cnt] = (Edge){v,u,0,0};
    G[u].push_back(cnt-1);
    G[v].push_back(cnt);
}
long long Edmond_Karp(int s,int t) {
    long long res = 0;
    while(true) {
        memset(a,0,sizeof(a));
        queue<int> que;
        que.push(s);
        a[s] = 0x7fffffff;
        while(!que.empty()) {
            int pos = que.front();
            que.pop();
            for(auto i:G[pos]) {
                Edge e = edge[i];
                if(!a[e.to]&&e.cap>e.f) {
                    p[e.to] = i;
                    a[e.to] = min(a[pos],e.cap-e.f);
                    que.push(e.to);
                }
            }
            if(a[t]) break;
        }
        if(!a[t]) break;
        for(int u = t;u!=s;u = edge[p[u]].from) {
            edge[p[u]].f += a[t];
            edge[p[u]^1].f -= a[t];
        }
        res+=a[t];
    }
    return res;
}
int main() {
    cin >> n >> m;
    for(int i = 1; i<=m;i++) {
        int x,y,c;
        cin >> x >> y >> c;
        addEdge(x,y,c);
    }
    int st,ed;
    cin >> st >> ed;
    cout << Edmond_Karp(st,ed) << endl;
    return 0;
}