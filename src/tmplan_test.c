#include <amino.h>

#include "tmsmt/tmplan.h"

int main(int argc, char **argv) {

    if( argc < 2 ) {
        fprintf(stderr, "No file specified\n");
        return -1;
    }
    FILE *in = fopen(argv[1],"r");
    struct tmplan *tmp = tmplan_parse(in, NULL);
    fclose(in);
    printf("\n\nPARSED\n\n");
    tmplan_write(tmp,stdout);

    return 0;
}
