#include <iostream>
#include <cstring>
#include <vector>
#include <queue>
using namespace std;
#define INF 0x7fffffff
struct Edge{
    int from,to,cap,f;
}edge[10005];
struct op {
    int in[15],out[15],weight;
}comp[65];
int a[1005],p[1005],cnt = 1,n,m,path[1005][5];
vector<int> G[1005];
void init(int n) {
    cnt = 1;
    memset(p,0,sizeof(p));
    memset(path,0,sizeof(path));
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
bool match(int x,int y) {
    for(int i = 1; i<=m;i++) if(comp[y].in[i]!=2&&comp[x].out[i]!=comp[y].in[i]) return false;
    return true;
}
int main() {
    while(cin >> m >> n) {
        init(n);
        int st = 0,ed = 2*n+1;
        for(int i = 1; i<=n;i++) {
            cin >> comp[i].weight;
            bool flag = true;
            for(int j = 1; j<=m;j++) {
                cin >> comp[i].in[j];
                if(comp[i].in[j]==1) flag = false;
            }
            if(flag) addEdge(st,i,INF);
            flag = true;
            for(int j = 1; j <=m;j++) {
                cin >> comp[i].out[j];
                if(!comp[i].out[j]) flag = false;
            }
            if(flag) addEdge(n+i,ed,INF);
        }
        for(int i = 1; i<=n;i++) {
            addEdge(i,n+i,comp[i].weight);
            for(int j = 1; j<=n;j++) if(j!=i&&match(i,j)) addEdge(n+i,j,INF);
        }
        long long it = 1,flow = Edmond_Karp(st,ed);
        for(int i = n+1;i<ed;i++) for(int j = 0 ; j < G[i].size();j++)
            if(edge[G[i][j]].f>0&&edge[G[i][j]].to<=n) path[it][0] = i - n,path[it][1] = edge[G[i][j]].to,path[it++][2] = edge[G[i][j]].f;
        cout << flow << " " <<  it-1 << endl;
        for(int i =1;i<it;i++) cout << path[i][0] << " " << path[i][1] << " " << path[i][2] << endl;
    }
    return 0;
}