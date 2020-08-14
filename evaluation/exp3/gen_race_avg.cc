#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <random>

std::mt19937 gen;

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "gen_race_avg PREFIX EVENTS RANGE SEED\n");
        exit(EXIT_FAILURE);
    }
    int events = atoi(argv[2]);
    int range = atoi(argv[3]);
    gen.seed(atoi(argv[4]));

    char *log_name = (char *)malloc((strlen(argv[1]) + 5) * sizeof(char));
    strcpy(log_name, argv[1]);
    strcat(log_name, ".log");
    FILE *log=fopen(log_name, "w");
    strcpy(log_name, argv[1]);
    strcat(log_name, ".csv");
    FILE *log_csv=fopen(log_name, "w");
    free(log_name);

    int *thread = new int[range];
    int *lock = new int[range];
    memset(thread, -1, sizeof(int) * range);
    memset(lock, -1, sizeof(int) * range);
    int *write = new int[range];
    for (int i = 0; i < range; i++) write[i] = gen()%2;

    int ev = 0;
    while (ev < events) {
        int op = (int)(gen()%4);
        switch (op) {
            case 0:
            {
                int t = (int)(gen()%range);
                int x = (int)(gen()%range);
                if (write[x]) {
                    if (lock[t]==-1 && gen()%events) continue;
                    else if (lock[t]!=-1) x = lock[t];
                }
                fprintf(log, "@0 read(%d,%d)\n", t, x);
                fprintf(log_csv, "read,%d,%d\n", t, x);
                break;
            }
            case 1:
            {
                int t = (int)(gen()%range);
                int x = (int)(gen()%range);
                if (write[x] || gen()%events==0) {
                    if (lock[t]==-1 && gen()%events) continue;
                    else if (lock[t]!=-1) x = lock[t];
                } else {
                    continue;
                }
                fprintf(log, "@0 write(%d,%d)\n", t, x);
                fprintf(log_csv, "write,%d,%d\n", t, x);
                break;
            }
            case 2:
            {
                int t = (int)(gen()%range);
                if (lock[t]==-1) {
                    continue;
                } else {
                    fprintf(log, "@0 rel(%d,%d)\n", t, lock[t]);
                    fprintf(log_csv, "rel,%d,%d\n", t, lock[t]);
                    thread[lock[t]]=-1;
                    lock[t]=-1;
                }
                break;
            }
            default:
            {
                int t = (int)(gen()%range);
                int l = (int)(gen()%range);
                if (lock[t]!=-1 || thread[l]!=-1) {
                    continue;
                } else {
                    fprintf(log, "@0 acq(%d,%d)\n", t, l);
                    fprintf(log_csv, "acq,%d,%d\n", t, l);
                    lock[t]=l;
                    thread[l]=t;
                }
                break;
            }
        }
        ev++;
    }

    fclose(log);
    fclose(log_csv);
    delete [] thread;
    delete [] lock;
    delete [] write;

    return 0;
}
