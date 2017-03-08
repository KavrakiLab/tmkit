TMKit Internals and Hacking {#tmkit_hacking}
===========================

This page describes some of the internals of TMKit, including design
decisions and implementation choices.  It is aimed at a developer who
is not necessarily familiar with all the tools used to develop TMKit.

[TOC]

--------------------------------------------------------------------------------


Library and Process Model {#tmkit_hacking_proc}
=========================

<pre>
          |------------------------------------|
          |            TMKit Process           |
          |------------------------------------|
          |------------------------------------|              |--------------------|
          |             TMKIT (SBCL)           |<------------>| SMT Solver Process |
          |                                    |   (SMT-LIB)  |--------------------|
          |                                    |
          |                                    |              |--------------------|
          |                                    |------------->|   Real-Time Land   |
          |------------------------------------|  T./M. Plan  |--------------------|
 |------->|             AMINO (SBCL)           |
 |        |------------------------------------|
 |        |             libamino.so            |
 |        |------------------------------------|
 |        | OMPL | FCL | GL/SDL2 | BLAS/LAPACK |
 |        |------------------------------------|
 |
 |
 |
 |
 |
 |  |--------------------|
 |->|  Blender Process   |
 |  |--------------------|
 |
 |  |--------------------|
 |->| C Compiler Process |
 |  |--------------------|
 |
 |  |--------------------|
 |->|   POV-Ray Process  |
    |--------------------|

</pre>

TMKit runs as a single process communicating with several external
tools.  The primary TMKit process runs in [SBCL](http://www.sbcl.org).
The primary process dynamically loads `libamino.so` (and related
libraries) from the [Amino](http://amino.golems.org) package to handle
geometric information.  The `libamino.so`, etc. libraries link against
several external libraries including [OMPL]
((http://ompl.kavrakilab.org/) for motion planning, the [FCL]
(https://github.com/flexible-collision-library/fcl) for collision
checking, and [OpenGL](https://www.opengl.org/) /
[SDL2](https://www.libsdl.org/index.php) for GUI rendering, and
[BLAS](http://www.netlib.org/blas/) / [LAPACK]
(http://www.netlib.org/lapack/) for linear algebra.

TMKit also forks several child processes.  The SMT solver runs in a
separate process, communicating with TMKit via the [SMT-LIB]
(http://smtlib.cs.uiowa.edu/) format.  Via code from Amino, TMKit uses
[Blender](https://www.blender.org/) to convert meshes, a C compiler to compile
meshes, and [POV-Ray](http://www.povray.org/) to produce high-quality
rendered images.

The plan produced by TMKit will mostly likely need to be executed via
a separate, real-time process because the TMKit process may impose
unacceptable latices due to memory management and threading.  Many of
the routines from Amino, including the scene graph structure used by
TMKit, are capable of low-latency, real-time performance.

--------------------------------------------------------------------------------

Implementation Choices {#tmkit_hacking_implementation_choices}
======================

TMKit is implemented primarily in Common Lisp, interfaces with an
external [SMT Solver]
(https://en.wikipedia.org/wiki/Satisfiability_modulo_theories), makes
heavy use of many C/C++ libraries.  Each of these tools offers key
advantages to satisfy the requirements of TMKit.

Why C/C++?
----------

Real-time constraints are an important consideration in robotics.  To
acheive acceptable latency, certain software modules, e.g., kinematic
computations, must be implemented in a low-level language.  C and C++
are the most widely-used and well-supported low-level languages.  It
is desirable to re-use as much of this existing, necessarily real-time
code as possible.

Many other authors provide C or C++ libraries.  TMKit makes heavy use
of the [Open Motion Planning Library] (http://ompl.kavrakilab.org/),
which provides a C++ interface.

Why SMT?
--------

Satisfiability Checking (SAT) underlies some of the most efficient
task planning approaches.  Many Satisfiability Modulo Theories (SMT)
solvers offer the capability to perform *incremental* checking, which
is useful for the repeated/alternation planning that Task-Motion
planning sometimes requires.  In addition, the "Theories" capability
of SMT offers the potential to efficiently handle rich, non-boolean
constraints in the robotics domain.

A number of of SMT solvers share the standard [SMT-LIB]
(http://smtlib.cs.uiowa.edu/) input/output format.  Using this
standard format, we gain the flexibility to use different solvers and
the ability to benefit from ongoing improvements to these tools.

Why Common Lisp?
---------------

**TL;DR:** *expressive for symbolic processing, plays well with C/C++
libraries, efficient performance.*

Common Lisp is well-suited for the symbolic processing necessary in
TMP.  [Symbolic Expressions]
(https://en.wikipedia.org/wiki/S-expression) are a builtin language
type.  You can see this expressivness in the TMKit source tree where
the initial [implementation]
(https://github.com/KavrakiLab/tmkit/blob/3ff7db6de239f6183fe2da5cb06655be3ead8030/smtplan.lisp)
of SATPlan required only ~300 lines of code.

The [SBCL] (http://www.sbcl.org/) implementation can efficiently share
data between Lisp and C functions, which improves interoperation with
C/C++ libraries.  Many other high-level language implementations
cannot easily share such data because their (copying) garbage
collector may move memory out from under a C function attempting to
access it.

SBCL includes a high-quality compiler that produces efficient native
code on all major [CPU architectures]
(http://www.sbcl.org/platform-table.html).

--------------------------------------------------------------------------------
APIs {#tmkit_hacking_apis}
====

Amino
-----

TMKit makes heavy use of the [Amino] (http://amino.kavrakilab.org)
library, which defines the scene graph data structure and provides an
interface to [OMPL] (http://ompl.kavrakilab.org/).

TMKit C API
-----------

Parts of TMKit are implemented as a [C library](@ref FILES).  In
particular, plan file parsing is implemented in C so that this
function can also be used by a separate real-time process that will
execute the plan.

TMKit Lisp API
--------------

The majority of TMKit is implemented in common lisp for the
aforementioned reasons.  Several functions are exported from the
[package](@ref TMKIT_LISP), notably the primary entry point of the
planner: `TMP-DRIVER'.

TMKit (CL)Python API
--------------------

Despite the productivy and performance advantages of common lisp, many
potential users of TMKit may be unfamiliar with this language.
Consequently, we also provide a
[CLPython](https://github.com/metawilm/cl-python)-based [interface]
(@ref tmsmtpy) for writing domain semantics definitions.

--------------------------------------------------------------------------------

Development Environment {#tmkit_hacking_dev_env}
=======================

A suitable environment will greatly speed up development.

Common Lisp blurs the distinctions between the typically separate
edit-compile-test phases of software development by including the Lisp
compiler in the Lisp runtime environment. (There is some myth that
Lisp is interpreted.  SBCL compiles *all* functions to native code.)
In typical Lisp development, the program never necessarily
terminates. Instead, individual functions are written/edited,
compiled/loaded into the running program, and tested as needed.  This
interactive development style speeds up the edit-compile-test cycle
from (often) minutes to (typically) seconds.

Taking advantage of the interactive Lisp development style requires
support from the text editor to integrate with the Lisp system.

SLIME: The Superior Lisp Interaction Mode for Emacs
---------------------------------------------------

[SLIME] (https://common-lisp.net/project/slime/) provides integrated
support for Lisp editing and interaction in Emacs.

The best way to setup SLIME is probably to install the [Quicklisp]
(https://www.quicklisp.org/beta/) package manager and follow their
instructions to [install SLIME]
(https://www.quicklisp.org/beta/#slime) via Quicklisp.

Alternatives to SLIME
---------------------

Some alternatives to SLIME exist, but these are much less widely used.

* [SLIMV] (https://bitbucket.org/kovisoft/slimv): Superior Lisp Interaction Mode for Vim


--------------------------------------------------------------------------------

References {#tmkit_hacking_references}
==========

TMKit
-----

### Algorithm

- N. T. Dantam, Z. K. Kingston, S. Chaudhuri, and L. E. Kavraki.
  [Incremental Task and Motion Planning: A Constraint-Based Approach](http://www.roboticsproceedings.org/rss12/p02.html),
  in Robotics: Science and Systems, 2016.


### Implementation

- Neil T. Dantam, Swarat Chaudhuri, Lydia
  E. Kavraki. [The Task Motion Kit]
  (http://www.cs.rice.edu/research/technical-reports/TR16-02/). Department
  of Computer Science. Rice University. TR16-02. 2016.

Common Lisp
-----------
* Cliki. [Getting Started] (http://cliki.net/Getting+Started)
* Peter Seibel. [Practical Common Lisp] (http://www.gigamonkeys.com/book/)
* Paul Graham. [On Lisp] (http://www.paulgraham.com/onlisptext.html)
