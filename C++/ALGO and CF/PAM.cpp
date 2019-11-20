#include <bits/stdc++.h>
using namespace std;
const int maxn = 3e5 + 10;
struct node {
    int len, fail, ptr[26];
    node(int len = 0,int fail = 0) : len(len), fail(fail) { memset(ptr,0,sizeof(ptr)); }
}pam[maxn];
char s[maxn],str[maxn];
int len,cnt,it,lens,cur,num[maxn],vis[35];
inline int getfail(int x) { return s[len-pam[x].len-1] != s[len]?getfail(pam[x].fail):x; }
inline void querynum() { for(int i = cnt; i >=0; i--) num[pam[i].fail] += num[i]; }
void init(){
    pam[cnt] = node(0,1);
    pam[++cnt] = node(-1),s[0] = '#';
}
void add(char c) {
    s[++len] = c,cur = getfail(it);
    if(!(it = pam[cur].ptr[c-'a'])) {
        pam[++cnt] = node(pam[cur].len + 2, pam[getfail(pam[cur].fail)].ptr[c-'a']);
        it = pam[cur].ptr[c-'a'] = cnt;
    }
    num[it]++;
}
long long ans;
void DFS(int pos, int nowc) {
    if(pos > 1) ans += 1LL * nowc * num[pos];
    for(int i = 0; i < 26; i++) {
        int to = pam[pos].ptr[i];
        if(to) {
            if(!vis[i]) { vis[i] ++;DFS(to,nowc+1),vis[i] --; }
            else { vis[i] ++; DFS(to,nowc); vis[i] --; }
        }
    }
}
int main() {
    init(),scanf("%s",str+1),lens = strlen(str+1);
    for(int i = 1; i <= lens; i++) add(str[i]);
    querynum(),DFS(0,0),memset(vis,0,sizeof(vis)),DFS(1,0);
    cout << ans;
}