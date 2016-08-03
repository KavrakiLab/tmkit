#include <amino.h>

#include "tmsmt/tmplan.h"

int main(int argc, char **argv) {

    if( argc < 2 ) {
        fprintf(stderr, "No file specified\n");
        return -1;
    }
    struct aa_mem_region region;
    aa_mem_region_init( &region, 1024*64 );
    struct tmplan *tmp = tmplan_parse_filename(argv[1], &region);

    if( tmp ) tmplan_write(tmp,stdout);

    if( tmp ) aa_mem_region_pop(&region,tmp);


    return 0;
}
