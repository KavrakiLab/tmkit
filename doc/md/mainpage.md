Task-Motion Kit {#mainpage}
==============

\htmlonly
<img src="tmkit-front.jpg" style="float:right; margin: 1em;"></img>
\endhtmlonly

The Task-Motion Kit (TMKit) is a framework for Task and Motion
Planning.  Everyday activities, e.g., setting a table or making
coffee, combine discrete decisions about objects and actions with
geometric decisions about collision free motion.  TMKit jointly
reasons about task-level objectives, i.e., choosing actions and
objects, and motion-level objectives, i.e., finding collision free
paths.


Features
========

* TMKit supports:
  - **Task Domains** defined in the de-facto standard [PDDL]
    (https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language)
    format.
  - **Motion Domains** defined in [URDF](http://wiki.ros.org/urdf) or
    compact [Scene Files](http://amino.kavrakilab.org/scenefile.html).
  - **Task-Motion Interaction** defined using
    [custom functions](@ref domain_semantics).

* TMKit provides:
  - A command-line [planner](@ref planner_command) interface.
  - Plain text plan output.
  - Integrated visualization.

* TMKit uses:
  - A new, incremental planning algorithm.
  - The [Z3] (https://github.com/Z3Prover/z3) theorem prover.
  - The Open Motion Planning Library
    ([OMPL](http://ompl.kavrakilab.org/)).

Getting Started
===============

- [Download] (@ref download)
- [Installation] (@ref installation)
- [Tutorial] (@ref tutorial)
- [License](@ref license): 3-clause BSD (permissive)
- [Citations] (@ref citations)
