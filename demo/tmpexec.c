/* -*- mode: C; c-basic-offset: 4; -*- */
/* ex: set shiftwidth=4 tabstop=4 expandtab: */
/*
 * Copyright (c) 2017, Rice University
 * All rights reserved.
 *
 * Author(s): Neil T. Dantam <ntd@rice.edu>
 *
 *   Redistribution and use in source and binary forms, with or
 *   without modification, are permitted provided that the following
 *   conditions are met:
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of copyright holder the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 *   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 *   CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 *   INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 *   MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 *   DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 *   CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 *   USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 *   AND ON ANY HEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 *   LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 *   ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 *   POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include "config.h"

#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>

#include <amino.h>
#include <amino/rx/rxtype.h>
#include <amino/rx/scenegraph.h>
#include <amino/rx/scene_plugin.h>

#include "tmsmt/tmplan.h"

static int g_verbosity = 0;

static void parseopt( int argc, char **argv,
                      const char **name, const char **plugin, const char **plan_file );

int main(int argc, char *argv[])
{
    const char *name="scenegraph";
    const char *plugin=NULL;
    const char *plan_file=NULL;

    parseopt( argc, argv,
              &name, &plugin, &plan_file );

    /* Load Scene Plugin */
    struct aa_rx_sg *scenegraph = aa_rx_dl_sg(plugin, name, NULL);
    if( NULL == scenegraph ) {
        fprintf(stderr, "ERROR: could not load scene `%s' from  plugin `%s'\n",
                name, plugin);
        exit(EXIT_FAILURE);
    }

    /* Load Plan File */
    struct aa_mem_region plan_region;
    aa_mem_region_init( &plan_region, 1024*64 );
    struct tmplan *plan = tmplan_parse_filename( plan_file, &plan_region );

    /* TODO: Compute interpolation parameters */

    /* TODO: Execute Plan File */

    /* Cleanup */
    aa_mem_region_pop(&plan_region, plan);
    aa_mem_region_destroy( &plan_region );
    aa_rx_sg_destroy( scenegraph );
}

static void parseopt( int argc, char **argv,
                      const char **name, const char **plugin, const char **plan_file )
{
    int c;
    opterr = 0;

    while( (c = getopt( argc, argv, "n:s:i:?v")) != -1 ) {
        switch(c) {
        case 'n':
            *name = optarg;
            break;
        case 's':
            *plugin = optarg;
            break;
        case 'i':
            *plan_file = optarg;
            break;
        case 'v':
            g_verbosity++;
            break;
        case '?':
            puts("Usage: tmpexec [OPTIONS] -s SCENE -i PLAN_FILE\n"
                 "Viewer for Amino scene graphs"
                 "\n"
                 "Options:\n"
                 "  -n NAME         scene graph name (default: scenegraph)\n"
                 "  -s SCENE        scene graph plugin to load\n"
                 "  -i PLAN         plan file to execute\n"
                 "  -v              verbose output\n"
                 "\n"
                 "\n"
                 "Report bugs to " PACKAGE_BUGREPORT "\n" );
            exit(EXIT_SUCCESS);
            break;
        default:
            fprintf(stderr, "ERROR: Unknown option: `-%c'\n", c);
            exit(EXIT_FAILURE);
        }
    }

    while( optind < argc ) {
        /* No positional arguments */
        fprintf(stderr, "ERROR: Unknown argument: `%s'\n", argv[optind]);
        exit(EXIT_FAILURE);
        optind++;
    }

    /* Check options */
    if( NULL == *plan_file ) {
        fprintf(stderr, "ERROR: no plan file specified\n");
        exit(EXIT_FAILURE);
    }
    if( NULL == *plugin ) {
        fprintf(stderr, "ERROR: no scene graph plugin specified\n");
        exit(EXIT_FAILURE);
    }
    if( g_verbosity ) {
        printf("Scene Plugin: `%s'\n"
               "Scene Name: `%s'\n"
               "Plan File: `%s'\n",
               *plugin, *name, *plan_file);
    }
}
