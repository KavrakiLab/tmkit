/*
 * Copyright (c) 2016, Rice University
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
 *   AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 *   LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 *   ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 *   POSSIBILITY OF SUCH DAMAGE.
 *
 */


/*
 * The is a parser for Wavefront OBJ files, written as a Flex Scanner.
 *
 *
 */

%option noyywrap
%option prefix="tmplan_"
%option reentrant
%option yylineno
%option batch
%option never-interactive
%option read

%option extra-type="struct tmplan*"


%{


#include <stdio.h>

#include <amino.h>
#include "tmsmt/tmplan.h"

%}

%x EOL
%x ACTION

%x MOTION_START
%x MOTION_SPACE

%x WAYPOINT_START
%x WAYPOINT_SPACE

%x REPARENT_FRAME
%x REPARENT_SPACE
%x REPARENT_NEW_PARENT

END [[:blank:]]*("#".*)?"\n"

DIGIT    [[:digit:]]
INT      {DIGIT}+
NUMBER   "-"?{INT}("."{DIGIT}*)?("e"("-"?){INT})?
BLANKS   [[:blank:]]+
MAYBE_BLANKS   [[:blank:]]*

NUMBER_BLANKS {NUMBER}{BLANKS}
NUMBER_END {NUMBER}{MAYBE_BLANKS}

FRAME_NAME [[:graph:]]+


START {MAYBE_BLANKS}

%%

{END} {
    /*fprintf(stderr, "comment: %s\n", yytext);*/
}

<EOL>{END} {
    BEGIN(INITIAL);
}

    /* Action */
{START}"a"{BLANKS} {
   tmplan_add_action(yyextra);
   BEGIN(ACTION);
}

<ACTION>[^#\n]*[^[:blank:]#\n] {
    tmplan_op_action_set( (struct tmplan_op_action*)tmplan_last_op(yyextra),
                          yytext);
    BEGIN(EOL);
}


    /* Motion Plan Start */
{START}"m"{BLANKS} {
    tmplan_add_motion_plan(yyextra);
    BEGIN(MOTION_START);
}

<MOTION_START>{FRAME_NAME} {
    tmplan_op_motion_plan_add_var( (struct tmplan_op_motion_plan*)tmplan_last_op(yyextra),
                                   yytext );
    BEGIN(MOTION_SPACE);
}

<MOTION_SPACE>{BLANKS} {
    BEGIN(MOTION_START);
}

<MOTION_START>{END} {
    tmplan_op_motion_plan_path_start( (struct tmplan_op_motion_plan*)tmplan_last_op(yyextra) );
    BEGIN(INITIAL);
}

<MOTION_SPACE>{END} {
    tmplan_op_motion_plan_path_start( (struct tmplan_op_motion_plan*)tmplan_last_op(yyextra) );
    BEGIN(INITIAL);
}

    /* Waypoint */
{START}"p"{BLANKS} {
    BEGIN(WAYPOINT_START);
}

<WAYPOINT_START>{NUMBER} {
    tmplan_op_motion_plan_path_add( (struct tmplan_op_motion_plan*)tmplan_last_op(yyextra),
                                    atof(yytext) );
    BEGIN(WAYPOINT_SPACE);
}

<WAYPOINT_SPACE>{BLANKS} {
    BEGIN(WAYPOINT_START);
}

<WAYPOINT_SPACE>{END} {
    BEGIN(INITIAL);
}

<WAYPOINT_START>{END} {
    BEGIN(INITIAL);
}


    /* Reparent */
{START}"r"{BLANKS} {
    BEGIN(REPARENT_FRAME);
    tmplan_add_reparent(yyextra);
}

<REPARENT_FRAME>{FRAME_NAME} {
    tmplan_op_reparent_set_frame( (struct tmplan_op_reparent*)tmplan_last_op(yyextra),
                                  yytext);
    BEGIN(REPARENT_SPACE);
}
<REPARENT_SPACE>{BLANKS} {
    BEGIN(REPARENT_NEW_PARENT);
}

<REPARENT_NEW_PARENT>{FRAME_NAME} {
    tmplan_op_reparent_set_new_parent( (struct tmplan_op_reparent*)tmplan_last_op(yyextra),
                                       yytext);
    BEGIN(INITIAL);
}
    /* Error */
    /* This rule needs to be last */

<*>. {
    fprintf(stderr, "Unrecognized character: %s (%d)\n", yytext, yylineno);
    return -1;
}

%%

AA_API struct tmplan*
tmplan_parse_file (FILE *in, struct aa_mem_region *reg)
{
    if( NULL == reg ) {
        reg = aa_mem_region_local_get();
    }

    yyscan_t scanner;
    tmplan_lex_init(&scanner);
    tmplan_set_in(in, scanner);

    struct tmplan *e = tmplan_create(reg);
    tmplan_set_extra(e, scanner);

    int r = tmplan_lex(scanner);

    tmplan_lex_destroy(scanner);

    if( r < 0 ) {
        aa_mem_region_pop(reg,e);
        return NULL;
    } else {
        tmplan_finish_op(e);
        return e;
    }
}
