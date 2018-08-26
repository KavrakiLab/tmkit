Constraint-Based Planning Language (CPDL) {#cpdl}
========================================


TMKit's Constraint-Based Planning Language (CPDL) is a language to
define planning problems.  CPDL is an intermediate representation that
decouples the planner implementation from high-level domain languages
such as PDDL and allows the planner to be used for problems defined in
a variety of syntaxes.

[TOC]



Mathematical Model {#cpdl_math}
==================

A CPDL description defines a transition system \f$ D = (X,s_0, \delta,
G) \f$, where:

- \f$ X = f_0 \times f_1 \times \ldots \times f_n \f$ is the
  state space defined as the product of a set of fluents
  (i.e., state variables),
- \f$ s_0 \in X\f$ is the start state,
- \f$ G \subseteq X\f$ is the goal set.
- \f$ \delta: X \mapsto X \f$ is the transition Function,


Syntax {#cpdl_syntax}
======

CPDL includes statements to define each part of the planning problem:
the sstate space, a start state, a goal state, and transition
function. The syntax uses
[S-expression](https://en.wikipedia.org/wiki/S-expression).

State Space {#cpdl_decl}
------------

### Variable Declarations

Declare a variable (fluent) with the `declare-fluent` command:

    (declare-fluent NAME TYPE)


### Type Declarations

Declare an unumerate type with the `declare-enum` command:

    (declare-enum NAME ELEMENTS...)


Start State {#cpdl_start}
-----------

Declare the starting value for a fluent with the `start` command.

### True value at start

    (start FLUENT)

### False value at start

    (start (not FLUENT))

### Other value at start

    (start (= FLUENT VALUE))

Goal Set {#cpdl_goal}
--------

Declare the goal set with the `goal` command:

    (goal EXPRESSION)

If multiple `goal` commands are given, they are and'ed together.

Transition Function {#cpdl_transition}
-------------------

Declare the transition function with the `transition` command:

    (transition EXPRESSION)

If multiple `transition` commands are given, they are and'ed together.

In the transition expression, refer to fluents using `now` and `next`
functions.  The `now` function refers to the fluent at the current
step (at which the transition occurs).  The `next` function refers to
the fluent at the successor step.

    (now FLUENT)
    (next FLUENT)

Output variables
----------------

Declare the output variables with the `output` command.  The planner
will then return the value of these fluents at each step.

    (output FLUENT)


Operators
---------

CPDL expressions may include the following mathematical operators:

| Name                     | Math Symbol                 | CPDL operator |
|--------------------------|-----------------------------|---------------|
| **Relations**            |                             |               |
| Equals                   | \f$ = \f$                   | =             |
| Less than                | \f$ < \f$                   | <             |
| Less than or Equal to    | \f$ \leq \f$                | <=            |
| Greater than             | \f$ > \f$                   | <             |
| Greater than or Equal to | \f$ \geq \f$                | >=            |
| **Arithmetic**           |                             |               |
| Add                      | \f$ + \f$                   | +             |
| Subtract                 | \f$ - \f$                   | -             |
| Multiply                 | \f$ * \f$                   | *             |
| Divide                   | \f$ / \f$                   | /             |
| **Logic**                |                             |               |
| Not                      | \f$ \lnot \f$               | not           |
| And                      | \f$ \land \f$               | and           |
| Or                       | \f$ \lor \f$                | or            |
| Xor                      | \f$ \oplus \f$              | xor           |
| Implies                  | \f$ \Longrightarrow \f$     | =>            |
| Biconditional (Iff)      | \f$ \Longleftrightarrow \f$ | <=>           |
| If-Then-Else             | N/A                         | ite           |
