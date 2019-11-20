#include <iostream>
#include <cstring>
#include <vector>
#include <queue>
using namespace std;
struct Edge{
    int from,to,cap,f;
}edge[10005];
int a[1005],p[1005],cnt = 1,n,m,d;
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
            for(int i = 0; i < G[pos].size();i++) {
                Edge e = edge[G[pos][i]];
                if(!a[e.to]&&e.cap>e.f) {
                    p[e.to] = G[pos][i];
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
    cin >> n >> m >> d;
    init(n);
    for(int i = 1; i<=m;i++) addEdge(0,i+100,1);
    for(int i = 1; i<=d;i++) addEdge(i+200,500,1);
    for(int i = 1; i<=n;i++) {
        addEdge(i,i+300,1);
        int fn,dn;
        cin >> fn >> dn;
        for(int i = 1; i<=fn;i++) {
            int tmp;
            cin >> tmp;
            addEdge(tmp+100,i,1);
        }
        for(int i = 1; i<=dn;i++) {
            int tmp;
            cin >> tmp;
            addEdge(i+300,tmp+200,1);
        }
    }
    cout << Edmond_Karp(0,500) << endl;
    return 0;
}