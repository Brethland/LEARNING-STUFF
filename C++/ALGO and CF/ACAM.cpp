#include <bits/stdc++.h>
using namespace std;
const int maxn = 5e4+10;
struct node{
    int ptr[26],fail,len,id;
    node(int len = 0, int fail = 0,int id = 0) : len(len),fail(fail),id(id) { memset(ptr,0,sizeof(ptr)); }
}akam[maxn];
int it,n,val[maxn],cnt[maxn];
string buff[155],mode;
queue<int> que;
void init() {
    memset(val,0,sizeof(val));
    memset(cnt,0,sizeof(cnt));
    for(int i = 0; i <= n; i++) akam[i] = node();it = 0;
}
void build() {
    for(int i = 0; i < 26; i++) if(akam[0].ptr[i]) que.push(akam[0].ptr[i]);
    while(!que.empty()) {
        int u = que.front();que.pop();
        for(int i = 0;i < 26; i++) {
            if(akam[u].ptr[i]) akam[akam[u].ptr[i]].fail = akam[akam[u].fail].ptr[i],que.push(akam[u].ptr[i]);
            else akam[u].ptr[i] = akam[akam[u].fail].ptr[i];
        }
    }
}
void insert(string s,int id) {
    int u = 0,len = s.length();
    for(int i = 0; i < len; i++) {
        if(!akam[u].ptr[s[i]-'a']) akam[u].ptr[s[i]-'a'] = ++it;
        u = akam[u].ptr[s[i]-'a'];
    }akam[u].len++;
    akam[u].id = id;
}
int queryExist(string t) {
    int u = 0,res = 0,len = t.length();
    for(int i = 0; i < len; i++) {
        u = akam[u].ptr[t[i]-'a'];
        for(int j = u; j && akam[j].len != -1; j = akam[j].fail) res+=akam[j].len,akam[j].len = -1;
    }
    return res;
}
int queryMax(string t) {
    int u = 0,res = 0,len = t.length();
    for(int i = 0; i < len; i++) {
        u = akam[u].ptr[t[i]-'a'];
        for(int j = u; j; j = akam[j].fail) val[j]++;
    }
    for(int j = 0; j < it; j++) if(akam[j].id) res = max(res,val[j]),cnt[akam[j].id] = val[j];
    return res;
}
int main (){
    while(cin >> n) {
        if(!n) break;init();
        while(!que.empty()) que.pop();
        for(int i = 1; i <= n; i++) cin >> buff[i], insert(buff[i],i);
        cin >> mode,build();
        int x = queryMax(mode);
        cout << x << endl;
        for(int i = 1; i <= n; i++) if(cnt[i]==x) cout << buff[i] << endl;
    }
}