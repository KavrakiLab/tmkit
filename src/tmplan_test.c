#include <amino.h>

#include "tmsmt/tmplan.h"

int main(int argc, char **argv) {

    if( argc < 2 ) {
        fprintf(stderr, "No file specified\n");
        return -1;
    }
    struct tmplan *tmp = tmplan_parse_filename(argv[1], NULL);

    if( tmp ) tmplan_write(tmp,stdout);

    return 0;
}
