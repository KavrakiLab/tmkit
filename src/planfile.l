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

%option stack

%option extra-type="struct wf_mtl_extra*"

%{

#pragma GCC diagnostic warning "-w"

#include <stdio.h>

#include <amino.h>
#include "tmsmt/tmplan.h"

%}

%x EOL

END [[:blank:]]*("#".*)?"\n"

DIGIT    [[:digit:]]
INT      {DIGIT}+
NUMBER   "-"?{INT}("."{DIGIT}*)?
BLANKS   [[:blank:]]+
MAYBE_BLANKS   [[:blank:]]*

NUMBER_BLANKS {NUMBER}{BLANKS}
NUMBER_END {NUMBER}{MAYBE_BLANKS}

ID [[:graph:]]+


START {MAYBE_BLANKS}

%%

{END} {
    /*fprintf(stderr, "comment: %s\n", yytext);*/
}

<EOL>{END} {
    BEGIN(INITIAL);
}

    /* Action */
{START}"a"{BLANKS}.* {
}
    /* Motion Plan Start */
{START}"m"{BLANKS}.* {
}
    /* Waypoint */
{START}"p"{BLANKS}.* {
}
    /* Reparent */
{START}"r"{BLANKS}.* {
}


    /* Error */
    /* This rule needs to be last */

<*>. {
    fprintf(stderr, "Unrecognized character: %s (%d)\n", yytext, yylineno);
    return -1;
}

%%

AA_API void
tmplan_parse (FILE *in)
{

    yyscan_t scanner;
    tmplan_lex_init(&scanner);
    tmplan_set_in(in, scanner);

    /* struct wf_mtl_extra e; */
    /* e.mtl = aa_rx_wf_mtl_create(); */
    /* e.mtl->filename = strdup(filename); */
    /* aa_rx_wf_set_extra(&e, scanner); */

    int r = tmplan_lex(scanner);

    tmplan_lex_destroy(scanner);

    /* if( r < 0 ) { */
    /*     aa_rx_wf_mtl_destroy(e.mtl); */
    /*     return NULL; */
    /* } else { */
    /*     return e.mtl; */
    /* } */
}
