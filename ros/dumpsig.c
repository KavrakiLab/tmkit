#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include "dumpsig.h"


void dumpsig()
{
    fprintf(stderr,"printing blocked signals....\n");
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

    fprintf(stderr,"done\n");

}


void unblock_sigpipe()
{

    sigset_t set;
    if( sigemptyset(&set) ) {
        perror("sigemptyset");
        exit(-1);
    }
    if(sigaddset(&set, SIGPIPE)){
        perror("sigaddset");
        exit(-1);
    }
    if(sigprocmask( SIG_UNBLOCK, &set, NULL ) ) {
        perror("sigprocmask");
        exit(-1);
    }
}
