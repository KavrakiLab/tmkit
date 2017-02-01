#########################
### Domain Parameters ###
#########################

# Table grid resolution
RESOLUTION=0.1

# End-Effector Frame
FRAME = "end_effector_grasp"

# Object placement tolerance
EPSILON = 1e-4



########################
### Imported Modules ###
########################

# Import our planning packages
import aminopy as aa
import tmsmtpy as tm

import TMSMT

# Import python math package
from math import pi

# The Common Lisp runtime is also available
import CL as cl


#############
## Helpers ##
#############

def map_locations(function, scene):
    for frame in tm.collect_frame_type(scene,"surface"):
        name = frame['name']
        for geom in frame['geometry']:
            shape = geom['shape']
            if aa.shape_is_box(shape):
                d = shape['dimension']
                x_max = d[0] / 2
                y_max = d[1] / 2
                x = 0
                i = 0
                while x <= x_max:
                    y = 0
                    j = 0
                    while y <= y_max:
                        function(name,i,j)
                        if i > 0: function(name,-i,j)
                        if j > 0: function(name,i,-j)
                        if i > 0 and j > 0: function(name,-i,-j)
                        y += RESOLUTION
                        j+=1
                    x +=  RESOLUTION
                    i+=1


def location_table(parent,frame):
    parent_name = parent.name
    name = frame.name
    trans = aa.translation( aa.frame_fixed_tf(frame) )
    i = int(round( trans[0] / RESOLUTION))
    j = int(round( trans[1] / RESOLUTION))
    position = tm.mangle(parent_name,i,j)
    return (["ONTABLE", name, position], i, j)

############################
### Collision Constraint ###
############################

def collision_constraint(scene,op,objs):
    # TODO: stacking

    moveable = []
    def collect_moveable(frame_name):
        frame = scene[frame_name]
        if aa.frame_isa(frame,"moveable"):
            moveable.append(frame)
    map(collect_moveable, objs)

    conjunction = []

    def handle_moveable(frame):
        parent_name = frame.parent
        parent = scene[parent_name]
        if aa.frame_isa(parent, "surface"):
            (x, i, j) = location_table(parent,frame)
            conjunction.append(x)

    map(handle_moveable, moveable)

    return conjunction

##########################
## Scene State Function ##
##########################
## TODO: Does not work after an UNSTACK operatorion
## Problem is with the "Clear" predicate
def make_state(scene, configuration, is_goal):
    '''Map the scene graph `scene' to a task state expression'''

    ## terms in the expression
    conjunction = []
    occupied = {}
    moveable_frames = tm.collect_frame_type(scene,"moveable")

    ## Add object locations
    handempty = [True]

    def add_on(child,parent):
        if parent == FRAME:
            conjunction.append(["HOLDING", child])
            conjunction.append(["NOT", ["HANDEMPTY"]])
            handempty[0] = False
            occupied[child] = True
        else:
            conjunction.append(["ON", child, parent])
            occupied[parent] = True

    def handle_moveable(frame):
        name = frame.name
        parent_name = frame.parent

        try:
            # If parent frame is a placement surface, position is the
            # appropriate grid cell on the surface.
            parent_frame = scene[parent_name]
            if aa.frame_isa(parent_frame, "surface"):
                (x, i, j) = location_table(parent_frame,frame)
                conjunction.append(x)

                occupied[(parent_name,i,j)] = True
            else:
                add_on(name,parent_name)
        except NameError:
                add_on(name,parent_name)

    map(handle_moveable, moveable_frames)

    if handempty[0]:
        conjunction.append(["HANDEMPTY"])

    ## Clear things
    def clear_block(frame):
        name = frame.name
        if not name in occupied:
            conjunction.append(["CLEAR", name])

    def clear_location(name,i,j):
        if not (name,i,j) in occupied:
            conjunction.append(["CLEAR", tm.mangle(name,i,j)])

    if not is_goal:
        map(clear_block, moveable_frames)
        map_locations(clear_location,scene)

    return conjunction

def scene_state(scene,configuration):
    return make_state(scene, configuration, False)

def goal_state(scene,configuration):
    return make_state(scene, configuration, True)

############################
## Scene Objects Function ##
############################

def scene_objects(scene):
    '''Return the PDDL objects for `scene'.'''
    obj = []

    def type_names(thing):
        return [ f.name
                 for f in
                 tm.collect_frame_type(scene,thing) ]

    # Moveable objects are blocks
    moveable = type_names("moveable")
    moveable.insert(0, "BLOCK")

    # Draw grid on surfaces
    locations = ['LOCATION']
    def add_loc(name,i,j):
        locations.append(tm.mangle(name,i,j))

    map_locations(add_loc,scene)

    return [moveable, locations]

############################
### Operator Definitions ###
############################


def motion_plan(op, frame, goal):
    scene = op.final_scene
    sub_scenegraph = aa.scene_chain(scene, "", frame)
    return tm.op_motion( op, sub_scenegraph, goal )

# def pick(op, obj):
#     mp = motion_plan(op, FRAME, tm.op_tf_abs(op,obj))
#     return tm.op_reparent(mp, FRAME, obj)

def place_tf(op, obj, dst_frame, g_tf_o ):
    mp =  motion_plan(op, obj, g_tf_o)
    return tm.op_reparent(mp, dst_frame, obj)

def place_height(scene,name):
    g = scene[name].collision
    s = g[0].shape
    if aa.shape_is_box(s):
        return s.dimension[2] / 2

# def place(op, obj, dst, i, j):
#     scene = op['final_scene']
#     x = i*RESOLUTION
#     y = j*RESOLUTION
#     z = place_height(scene,obj) + place_height(scene,dst) + EPSILON
#     d_tf_o = aa.tf2( 1, [x,y,z] )
#     g_tf_d = tm.op_tf_abs(op,dst)
#     g_tf_o = aa.mul(g_tf_d, d_tf_o );
#     return place_tf(op, obj, dst, g_tf_o)

# def stack(op, obj, dst ):
#     scene = op['final_scene']
#     config = op['final_config']
#     g_tf_d = tm.op_tf_abs(op,dst)
#     d_tf_o = aa.tf2(1, [0,0, place_height(scene,obj) + place_height(scene,dst) + EPSILON])
#     g_tf_o = aa.mul(g_tf_d, d_tf_o)
#     return place_tf(op, obj, dst, g_tf_o)



def op_pick_up(scene, config, op):
    #(a, obj, src, i, j) = op
    obj = op[1]
    nop = tm.op_nop(scene,config)
    mp = motion_plan(nop, FRAME, tm.op_tf_abs(nop,obj))
    return tm.op_reparent(mp, FRAME, obj)

def op_put_down(scene, config, op):
    (a, obj, dst, i, j) = op
    nop = tm.op_nop(scene,config)
    x = i*RESOLUTION
    y = j*RESOLUTION
    z = place_height(scene,obj) + place_height(scene,dst) + EPSILON
    d_tf_o = aa.tf2( 1, [x,y,z] )
    g_tf_d = tm.op_tf_abs(nop,dst)
    g_tf_o = aa.mul(g_tf_d, d_tf_o );
    return place_tf(nop, obj, dst, g_tf_o)

def op_stack(scene, config, op):
    (act,obj,dst) = op
    nop = tm.op_nop(scene,config)
    g_tf_d = tm.op_tf_abs(nop,dst)
    d_tf_o = aa.tf2(1, [0,0, place_height(scene,obj) + place_height(scene,dst) + EPSILON])
    g_tf_o = aa.mul(g_tf_d, d_tf_o)
    return place_tf(nop, obj, dst, g_tf_o)

def op_unstack(scene, config, op):
    return op_pick_up(scene,config,op)



##########################
### Register functions ###
##########################

tm.bind_scene_state(scene_state)
tm.bind_goal_state(goal_state)
tm.bind_scene_objects(scene_objects)
tm.bind_refine_operator(op_pick_up, "PICK-UP")
tm.bind_refine_operator(op_put_down, "PUT-DOWN")
tm.bind_refine_operator(op_stack, "STACK")
tm.bind_refine_operator(op_unstack, "UNSTACK")

tm.bind_collision_constraint(collision_constraint)
