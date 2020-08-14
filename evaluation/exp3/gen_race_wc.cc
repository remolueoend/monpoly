#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <random>

std::mt19937 gen;

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "gen_race_wc PREFIX STRATEGY EVENTS SEED\n");
        exit(EXIT_FAILURE);
    }
    int strategy = atoi(argv[2]);
    int events = atoi(argv[3]);
    gen.seed(atoi(argv[4]));

    char *log_name = (char *)malloc((strlen(argv[1]) + 5) * sizeof(char));
    strcpy(log_name, argv[1]);
    strcat(log_name, ".log");
    FILE *log=fopen(log_name, "w");
    strcpy(log_name, argv[1]);
    strcat(log_name, ".csv");
    FILE *log_csv=fopen(log_name, "w");
    free(log_name);

if(strategy==0) {
    int t = 0;
    int ev = 0;
    while (ev < events) {
        int l = gen()%2;
        fprintf(log, "@0 acq(%d,%d)\n", t, l);
        fprintf(log_csv, "acq,%d,%d\n", t, l);
        if (++ev == events) break;
        fprintf(log, "@0 write(%d,%d)\n", t, l);
        fprintf(log_csv, "write,%d,%d\n", t, l);
        if (++ev == events) break;
        fprintf(log, "@0 rel(%d,%d)\n", t, l);
        fprintf(log_csv, "rel,%d,%d\n", t, l);
        ev++;
        t++;
    }
} else if(strategy==1) {
    int ev = 0;
    for(int i=0; i<events/2; i++) {
        int t=gen()%2;
        fprintf(log, "@0 acq(%d,%d)\n", t, i);
        fprintf(log_csv, "acq,%d,%d\n", t, i);
        ev++;
    }
    gen.seed(atoi(argv[4]));
    for(int i=0; i<events/2; i++) {
        int t=gen()%2;
        fprintf(log, "@0 read(%d,%d)\n", t, i);
        fprintf(log_csv, "read,%d,%d\n", t, i);
        ev++;
    }
}

    fclose(log);
    fclose(log_csv);

    return 0;
}
