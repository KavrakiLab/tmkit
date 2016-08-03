Plan Files {#planfile}
==========

Task and motion plans are output in a plan-text, line-based format.

[TOC]

Statements {#planfile_statements}
==========

Each plan file line is a single statement.

Action Lines {#planfile_stmt_action}
------------

Action lines indicate the discrete action to be taken.

Action lines begin with "a".

### Action Example

    a TRANSFER object destination

Reparent Lines {#planfile_stmt_reparent}
--------------

Reparent lines change the topology of the scenegraph. For example
picking an object changes the object frame's parent to the robot
end-effector.

Reparent lines begin with "r", then contain the frame being reparented
followed by its new parent frame.

### Reparent Example

    r object end_effector

Motion Plan Start Lines {#planfile_stmt_motion}
-----------------------

Motion plan start lines indicate the beginning of a new motion plan
and list the names of configuration variables used in the plan.

Motion plan start line begin with "m", then contain a list of the
names of configuration variables described by the plan.

A motion plan start line must be followed by one or more waypoint
lines.

### Motion Plan Start  Example

    m shoulder_0 shoulder_1 shoulder_2 elbow wrist_0 wrist_1 wrist_2

Configuration Waypoint Lines  {#planfile_stmt_waypoint}
----------------------------

Waypoint lines indicate a particular configuration waypoint along a
motion plan.  Each element of the waypoint corresponds to the named
configuration variable from the motion plan start line.

Waypoint lines begin with "p", then contain a list of the
configuration variable values at that waypoint.

### Waypoint Example

    p 0.0 0.0 0.0 3.14 0.0 0.0 0.0

Comment Lines {#planfile_stmt_comment}
-------------

Plan files uses shell-style line comments (`# Comment`).

### Comment Example

    # This is a line comment

Generation and Parsing {#planfile_stmt_gen_parse}
======================

The [tmplan.h] (@ref tmplan.h) header defines functions and data
structures for plan files.


Parsing Example
---------------

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
/* Parse the plan file struct */
struct aa_mem_region region;
aa_mem_region_init(&region, 1024*64);
struct tmplan *tmp = tmplan_parse_filename("plan.tmp", &region);

/* Use the plan file struct */
/* ... */

/* Release the plan file struct */
aa_mem_region_pop(&region, tmp);
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

@sa tmplan_parse_filename()
@sa tmplan_parse_file()

Usage Example
-------------

~~~~~~~~~~~~~~~~{.c}

/* A function to apply to each operator in the plan */
static void
helper_function (void *cx, const struct tmplan_op *op );

/* This is a simplified version of tmplan_write() */
int
simple_tmplan_write (const struct tmplan *tmp)
{
    /* apply helper_function to each operator */
    tmplan_map_ops( tmp, helper_function, stdout );
}

static void
helper_function (void *cx, const struct tmplan_op *op )
{
    FILE *out = (FILE*)cx;
    switch( op->type ) {
    case TMPLAN_OP_ACTION: {
        struct tmplan_op_action *x = (struct tmplan_op_action *)op;
        if( x->action ) {
            fprintf(out,"a %s\n",x->action);
        } else {
            fprintf(out, "a\n");
        }
    } break;
    case TMPLAN_OP_MOTION_PLAN: {
        fprintf(out, "m\n");
    } break;
    case TMPLAN_OP_REPARENT: {
        struct tmplan_op_reparent *x = (struct tmplan_op_reparent *)op;
        fprintf(out, "r %s %s\n",
                x->frame, x->new_parent );
    } break;
    }
}
~~~~~~~~~~~~~~~~

@sa tmplan_map_ops()
@sa tmplan_op_motion_plan_map_var()

Generation Example
------------------

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
struct aa_mem_region region;
aa_mem_region_init(&region, 1024*64);
struct tmplan *tmp = tmplan_create(&region);
/* Initialize the struct */
/* ... */

/* Write the struct */
FILE *out = fopen("plan.tmp", "w");
tmplan_write(tmp,stdout);
fclose(out);

/* Release the plan file struct */
aa_mem_region_pop(&region, tmp);
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

@sa tmplan_write()
