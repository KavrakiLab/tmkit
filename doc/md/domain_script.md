Domain Scripts {#domain_script}
==============

[TOC]

Domain script files specify the mapping between the task and motion
layers in the particular planning domain.

Functions {#domain_script_functions}
=========


Scene State Function {#domain_script_fun_state}
--------------------

* **Input:** `SCENE-GRAPH, CONFIGURATION`
* **Output:** `EXPRESSION-LIST`

The state function maps the geometric scene to a task state.  The
return value is a list of expressions (implicitly and-ed) that define
the state.

State expressions are represented as lists of operators and arguments
in [S-Expression] (https://en.wikipedia.org/wiki/S-expression) format.


### Expression Examples

The following table provides several examples of state expressions in
customary infix notation, as PDDL and Lisp S-Expressions, and as
Python lists.

| Infix Expression    | PDDL / Lisp S-Expression |  Python List  |
|---------------------|--------------------------|-----------------------|
|  `a AND b`          |  `(and a b)`             |  `["AND", "a", "b"]`  |
|  `a OR b`           |  `(or a b)`              |  `["OR", "a", "b"]`   |
| `(a OR b) AND c`    |  `(and (or a b) c)`      |  `["AND", ["OR", "a", "b"], "c"]` |
| `position(foo) = x` | `(= (position foo) x)`   |  `["=", ["POSITION", "foo"], "x"]` |


#### Python Expression List

Here is an example return value as a Python list:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
[["=", ["POSITION", "block_a"], "front_table__0__0"],
 ["=", ["POSITION", "block_b"], "front_table__0__-2"],
 ["=", ["POSITION", "block_c"], "block_a"]]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


#### S-Expression List

And here is the same return value as a Lisp S-Expression:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
((= (POSITION "block_a") "front_table__0__0")
 (= (POSITION "block_b") "front_table__0__-2")
 (= (POSITION "block_c") "block_a"))
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Scene Objects Function {#domain_script_fun_objects}
----------------------

* **Input:** `SCENE-GRAPH`
* **Output:** `OBJECTS-LIST`

The scene objects function returns the PDDL objects for the scene.
The return value is a list where each element is another list
beginning with the object type and followed by all objects of that
type.

### Examples

The following examples show the object lists objects "block_a",
"block_b" and "block_c" of type "BLOCK", and "location_0",
"location_1", and "location_2" of type "LOCATION".

#### Python Example

Here is an example return value as a Python list:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
[["BLOCK", "block_a", "block_b", "block_c"],
 ["LOCATION", "location_0", "location_1", "location_2"]]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#### S-Expression

And here is the same value as an S-Expression:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
((BLOCK "block_a" "block_b" "block_c")
 (LOCATION "location_0" "location_1" "location_2"))
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#### PDDL Example

These example values correspond to the following PDDL `:objects`
clause:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.c}
(:objects  "block_a" "block_b" "block_c" - block
           "location_0" "location_1" "location_2" - location)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
