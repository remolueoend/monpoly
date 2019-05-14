#include <algorithm>
#include <cstdio>
#include <vector>
using namespace std;

int N;
vector<vector<int> > sets;
int Q;
vector<int> cur;

int main() {
    scanf("%d", &N);
    sets.resize(N);
    for(int i=0; i<N; i++) {
        int l;
        scanf("%d", &l);
        for(int j=0; j<l; j++) {
            int k;
            scanf("%d", &k);
            sets[i].push_back(k);
        }
    }
    scanf("%d", &Q);
    for(int i=0; i<N; i++) {
        int l=sets[i].size();
        for(int j=0; j<l; j++) {
            printf("@0 acq(%d,%d)\n", i, sets[i][j]);
            //printf("acq,%d,%d\n", i, sets[i][j]);
        }
        for(int j=0; j<Q; j++) {
            printf("@0 read(%d,%d)\n", i, j);
            //printf("read,%d,%d\n", i, j);
        }
        for(int j=0; j<l; j++) {
            printf("@0 rel(%d,%d)\n", i, sets[i][j]);
            //printf("rel,%d,%d\n", i, sets[i][j]);
        }
    }
    for(int i=0; i<Q; i++) {
        int l;
        scanf("%d", &l);
        cur.clear();
        for(int j=0; j<l; j++) {
            int k;
            scanf("%d", &k);
            cur.push_back(k);
        }
        for(int j=0; j<l; j++) {
            printf("@0 acq(%d,%d)\n", N+i, cur[j]);
            //printf("acq,%d,%d\n", N+i, cur[j]);
        }
        printf("@0 write(%d,%d)\n", N+i, i);
        //printf("write,%d,%d\n", N+i, i);
        for(int j=0; j<l; j++) {
            printf("@0 rel(%d,%d)\n", N+i, cur[j]);
            //printf("rel,%d,%d\n", N+i, cur[j]);
        }
    }

    return 0;
}
