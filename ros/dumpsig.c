#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include "dumpsig.h"


void dumpsig()
{
    sigset_t set;
    if( sigprocmask(0, NULL, &set ) ) {
        fprintf(stderr, "sigprocmask failed\n");
    }
    for( int i = 1; i < 64; i ++ ) {
        if( sigismember( &set, i ) ) {
            fprintf(stderr, "sig %d, `%s' \tis blocked\n",
                    i, strsignal(i) );
        }
    }


}
