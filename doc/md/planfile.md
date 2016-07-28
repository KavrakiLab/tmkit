Plan Files
==========

Task and motion plans are output in a plan-text, line-based format.

Statements
==========

Each plan file line is a single statement.

Action Lines
------------

Action lines indicate the discrete action to be taken.

Action lines begin with "a".

### Action Example

    a TRANSFER object destination

Reparent Lines
--------------

Reparent lines change the topology of the scenegraph. For example
picking an object changes the object frame's parent to the robot
end-effector.

Reparent lines begin with "r", then contain the frame being reparented
followed by its new parent frame.

### Reparent Example

    r object end_effector

Motion Plan Start Lines
-----------------------

Motion plan start lines indicate the beginning of a new motion plan
and list the names of configuration variables used in the plan.

Motion plan start line begin with "m", then contain a list of the
names of configuration variables described by the plan.

A motion plan start line must be followed by one or more waypoint
lines.

### Motion Plan Start  Example

    m shoulder_0 shoulder_1 shoulder_2 elbow wrist_0 wrist_1 wrist_2

Configuration Waypoint Lines
----------------------------

Waypoint lines indicate a particular configuration waypoint along a
motion plan.  Each element of the waypoint corresponds to the named
configuration variable from the motion plan start line.

Waypoint lines begin with "p", then contain a list of the
configuration variable values at that waypoint.

### Waypoint Example

    p 0.0 0.0 0.0 3.14 0.0 0.0 0.0

Comment Lines
-------------

Plan files uses shell-style line comments (`# Comment`).

### Comment Example

    # This is a line comment
