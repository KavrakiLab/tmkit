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


struct exec_handler {
    struct aa_rx_sg *scenegraph;
    double *q;
};

struct exec_cx {
    struct aa_mem_region *region;
    struct exec_handler *handlers;
    struct aa_rx_sg *scenegraph;
    double *q;
    size_t i;
    size_t n;
};

static void op_function(void *cx, const struct tmplan_op *op);

static void parseopt( int argc, char **argv,
                      struct aa_rx_sg **scenegraph, const char **plan_file );

int main(int argc, char *argv[])
{
    const char *plan_file=NULL;
    struct exec_cx ecx;
    AA_MEM_ZERO(&ecx,1);

    parseopt( argc, argv,
              &ecx.scenegraph, &plan_file );

    /* Load Scene Plugin */

    aa_rx_sg_init(ecx.scenegraph);

    /* Load Plan File */
    struct aa_mem_region plan_region;
    aa_mem_region_init( &plan_region, 1024*64 );
    struct tmplan *plan = tmplan_parse_filename( plan_file, &plan_region );

    /* Compute interpolation parameters */
    ecx.q = AA_MEM_REGION_NEW_N(&plan_region,double, aa_rx_sg_config_count(ecx.scenegraph));
    // TODO: start config
    ecx.region = &plan_region;
    ecx.n = tmplan_op_count(plan);
    ecx.i = 0;
    ecx.handlers = AA_MEM_REGION_NEW_N(&plan_region, struct exec_handler, ecx.n);
    tmplan_map_ops( plan, op_function, &ecx );

    /* TODO: Execute Plan File */

    /* Cleanup */
    aa_mem_region_pop(&plan_region, plan);
    aa_mem_region_destroy( &plan_region );
    aa_rx_sg_destroy( ecx.scenegraph );
}

static void parseopt( int argc, char **argv,
                      struct aa_rx_sg **scenegraph, const char **plan_file )
{
    int c;
    opterr = 0;

    const char *name="scenegraph";

    while( (c = getopt( argc, argv, "n:s:i:?v")) != -1 ) {
        switch(c) {
        case 'n':
            name = optarg;
            break;
        case 's':
        {
            if( g_verbosity ) {
                printf("Scene Plugin: `%s'\n"
                       "Scene Name: `%s'\n",
                       optarg, name);
            }
            *scenegraph = aa_rx_dl_sg(optarg, name, *scenegraph);
            if( NULL == *scenegraph ) {
                fprintf(stderr, "ERROR: could not load scene `%s' from  plugin `%s'\n",
                        name, optarg);
                exit(EXIT_FAILURE);
            }
            break;
        }
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
    if( g_verbosity ) {
        printf( "Plan File: `%s'\n", *plan_file);
    }
}

static void op_function(void *cx_, const struct tmplan_op *op)
{
    struct exec_cx *cx = (struct exec_cx *)cx_;
    assert(cx->i < cx->n);

    if( 0 == cx->i ) {
        cx->handlers[0].scenegraph = cx->scenegraph;
        cx->handlers[0].q = cx->q;
    }
    struct aa_rx_sg *scenegraph_end = cx->handlers[cx->i].scenegraph;
    double *q_end = cx->handlers[cx->i].q;

    enum tmplan_op_type op_type = tmplan_op_type(op);

    switch( op_type ) {
    case TMPLAN_OP_ACTION:
    {
        struct tmplan_op_action *top = (struct tmplan_op_action*)op;
        if( g_verbosity ) {
            printf("OP ACTION: %s\n",
                   tmplan_op_action_get(top));
        }
    }
    break;
    case TMPLAN_OP_MOTION_PLAN:
    {
        struct tmplan_op_motion_plan *top = (struct tmplan_op_motion_plan*)op;
        if( g_verbosity ) {
            printf("OP MOTION\n");
        }
        double *op_path = tmplan_op_motion_plan_path(top);
        size_t op_n_q = tmplan_op_motion_plan_config_count(top);
        size_t op_n_elt = tmplan_op_motion_plan_path_size(top);
        const char *op_names[op_n_q];
        aa_rx_config_id op_ids[op_n_q];
        tmplan_op_motion_plan_vars(top, op_n_q, op_names);
        aa_rx_sg_config_indices( scenegraph_end, op_n_q, op_names, op_ids );
        if( g_verbosity ) {
            for( size_t i = 0; i < op_n_q; i ++ ) {
                printf("\tq[%lu]:\t%s (%d)\n", i, op_names[i], op_ids[i]);
            }
        }
    }
    break;
    case TMPLAN_OP_REPARENT:
    {
        struct tmplan_op_reparent *top = (struct tmplan_op_reparent*)op;
        const char *child = tmplan_op_reparent_get_frame(top);
        const char *new_parent = tmplan_op_reparent_get_new_parent(top);
        if( g_verbosity ) {
            printf("OP REPARENT: `%s' -> `%s'\n",
                   new_parent, child);
        }
        /* compute relative TF */
        size_t n_tf = aa_rx_sg_frame_count(scenegraph_end);
        size_t n_q = aa_rx_sg_config_count(scenegraph_end);
        double TF_rel[7*n_tf];
        double TF_abs[7*n_tf];
        assert( q_end );
        aa_rx_sg_tf( scenegraph_end, n_q, q_end,
                     n_tf,
                     TF_rel, 7,
                     TF_abs, 7 );
        double tf_rel[7];
        aa_rx_sg_rel_tf( scenegraph_end,
                         aa_rx_sg_frame_id(scenegraph_end, new_parent),
                         aa_rx_sg_frame_id(scenegraph_end, child),
                         TF_abs, 7, tf_rel );
        /* Update scenegraph */
        assert( aa_rx_sg_frame_id(scenegraph_end, child) > 0 );
        assert( aa_rx_sg_frame_id(scenegraph_end, new_parent) >= 0 );
        scenegraph_end = aa_rx_sg_copy( scenegraph_end );
        aa_rx_sg_reparent_name( scenegraph_end, new_parent, child, tf_rel );
        aa_rx_sg_init(scenegraph_end);

        // Remap configuration?
    }
    break;
    default:
        fprintf(stderr, "ERROR: Unknown operator type: %d\n", op_type);
        exit(EXIT_FAILURE);
    }

    cx->i++;
    if( cx->i < cx->n ) {
        cx->handlers[cx->i].scenegraph = scenegraph_end;
        cx->handlers[cx->i].q = q_end;
    }
}
