# python

# Import our planning packages
import aminopy as aa
import tmsmtpy as tm

import TMSMT

# Import python math package
from math import pi

# The Common Lisp runtime is also available
import CL as cl


## Some domain parameters

# Table grid resolution
RESOLUTION=0.1

# End-Effector Frame
FRAME = "end_effector_grasp"

# Object placement tolerance
EPSILON = 1e-4

def scene_state_linear(scene, configuration):
    '''Map the scene graph `scene' to a task state expression'''

    ## terms in the expression
    conjunction = []

    def handle_moveable(frame):
        name = frame['name']
        parent_name = frame['parent']
        position = parent_name

        try:
            # If parent frame is a placement surface, position is the
            # appropriate grid cell on the surface.
            parent_frame = scene[parent_name]
            if aa.frame_isa(parent_frame, "surface"):
                trans = aa.translation( aa.frame_fixed_tf(frame) )
                i = int(round( trans[0] / RESOLUTION))
                j = int(round( trans[1] / RESOLUTION))
                position = tm.mangle(parent_name,i,j)
        except NameError:
            pass

        conjunction.append(["=",
                            ["POSITION", name],
                            position])

    moveable_frames = tm.collect_frame_type(scene,"moveable")
    map(handle_moveable, moveable_frames)

    return conjunction

## END def scene_state_linear


def scene_objects_linear(scene):
    '''Return the PDDL objects for `scene'.'''
    obj = []

    def type_names(thing):
        return [ f['name']
                 for f in
                 tm.collect_frame_type(scene,thing) ]

    # Moveable objects are blocks
    moveable = type_names("moveable")
    moveable.insert(0, "BLOCK")

    # Draw grid on surfaces
    locations = ['LOCATION']
    def add_loc(name,i,j):
        locations.append(tm.mangle(name,i,j))

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
                        add_loc(name,i,j)
                        if i > 0: add_loc(name,-i,j)
                        if j > 0: add_loc(name,i,-j)
                        if i > 0 and j > 0: add_loc(name,-i,-j)
                        y += RESOLUTION
                        j+=1
                    x +=  RESOLUTION
                    i+=1

    #print surface
    return [moveable, locations]

## END def scene_objects_linear(scene):


############################
### Operator Definitions ###
############################

def motion_plan(op,frame, goal):
    scene = op['final_scene']
    ssg = aa.scene_chain(scene, "", frame)
    mp = tm.op_motion( op, ssg, goal )
    if False == mp: raise tm.PlanningFailure()
    return mp

def pick(op, obj):
    mp = motion_plan(op, FRAME, tm.op_tf_abs(op,obj))
    return tm.op_reparent(mp, FRAME, obj)

def place_tf(op, obj, dst_frame, g_tf_o ):
    mp =  motion_plan(op, obj, g_tf_o)
    return tm.op_reparent(mp, dst_frame, obj)

def place_height(scene,name):
    g = scene[name]['collision']
    s = g[0]['shape']
    if aa.shape_is_box(s):
        return s['dimension'][2] / 2

def place(op, obj, dst, i, j):
    scene = op['final_scene']
    x = i*RESOLUTION
    y = j*RESOLUTION
    z = place_height(scene,obj) + place_height(scene,dst) + EPSILON
    d_tf_o = aa.tf2( 1, [x,y,z] )
    g_tf_d = tm.op_tf_abs(op,dst)
    g_tf_o = aa.mul(g_tf_d, d_tf_o );
    return place_tf(op, obj, dst, g_tf_o)

def stack(op, obj, dst ):
    scene = op['final_scene']
    config = op['final_config']
    g_tf_d = tm.op_tf_abs(op,dst)
    d_tf_o = aa.tf2(1, [0,0, place_height(scene,obj) + place_height(scene,dst) + EPSILON])
    g_tf_o = aa.mul(g_tf_d, d_tf_o)
    return place_tf(op, obj, dst, g_tf_o)

def op_transfer(scene, config, op):
    (act, obj, dst_frame, dst_i, dst_j) = op
    nop = tm.op_nop(scene,config)
    op_pick = pick(nop,obj)
    return place( op_pick, obj, dst_frame, dst_i, dst_j )

def op_stack(scene, config, op):
    (act,obj,dst) = op
    nop = tm.op_nop(scene,config)
    op_pick = pick(nop, obj)
    return stack( op_pick, obj, dst )

## Register functions
tm.bind_scene_state(scene_state_linear)
tm.bind_scene_objects(scene_objects_linear)
tm.bind_refine_operator(op_transfer, "TRANSFER")
tm.bind_refine_operator(op_stack, "STACK")
