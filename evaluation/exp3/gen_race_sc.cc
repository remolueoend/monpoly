#include <bits/stdc++.h>
using namespace std;

mt19937 gen;

int main(int argc, char **argv) {
    if(argc!=5) {
        fprintf(stderr, "./gen N Q L SEED\n");
        exit(EXIT_FAILURE);
    }
    int n=atoi(argv[1]);
    int q=atoi(argv[2]);
    int l=atoi(argv[3]);
    gen.seed(atoi(argv[4]));

    printf("%d\n", n);
    vector<vector<int> > sets;
    sets.resize(n);
    for(int i=0; i<n; i++) {
        for(int j=0; j<l; j++) {
            if(gen()%2) sets[i].push_back(j);
        }
        if(sets[i].size()==0) sets[i].push_back(0);
        printf("%lu", sets[i].size());
        for(int j=0; j<sets[i].size(); j++) printf(" %d", sets[i][j]);
        printf("\n");
    }
    printf("%d\n", q);
    for(int i=0; i<q; i++) {
        vector<int> cur;
        for(int j=0; j<l; j++) {
            if(gen()%2) cur.push_back(j);
        }
        if(cur.size()==0) cur.push_back(0);
        printf("%lu", cur.size());
        for(int j=0; j<cur.size(); j++) printf(" %d", cur[j]);
        printf("\n");
    }

    return 0;
}
