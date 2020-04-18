// A Boring Test
#include <stdio>
#define fa(x) x/2

int heap[114514], int end;

void insert(int x) {
    heap[end++] = x;
    while(x < fa(x) && x >= 1) swap(heap[x], heap[fa(x)]), x = fa(x);
}
int pop() {
    int t = heap[1],now = 1;
    while(now < end) {
        heap[now] = heap[now << 1 | 1] > heap[now << 1] ? heap[now << 1] : heap[now << 1 | 1];
        now = heap[now << 1 | 1] > heap[now << 1] ? now << 1 : now << 1 | 1;
    }
    return t;
}

int main() {

}