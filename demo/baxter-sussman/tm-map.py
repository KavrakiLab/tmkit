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
FRAME = "right_endpoint"

# Object placement tolerance
EPSILON = 1e-4

# Nominal relative grasp pose
GRASP = aa.tf2( aa.yangle(pi),
                aa.vec3([0.00, 0.00, 0.075]))


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


def motion_plan(op,goal):
    scene = op['final_scene']
    ssg = aa.scene_chain(scene, "", FRAME)
    return tm.op_motion( op, ssg, goal )

def pick(op, obj):
    scene = op['final_scene']
    config = op['final_config']
    g_tf_o = aa.scene_tf_abs(scene,config,obj)
    g_tf_e = aa.mul(g_tf_o, GRASP)

    return motion_plan(op, g_tf_e)


def place_height(scene,name):
    g = scene[name]['collision']
    s = g[0]['shape']
    if aa.shape_is_box(s):
        return s['dimension'][2] / 2

def place(op, obj, dst, i, j):
    scene = op['final_scene']
    config = op['final_config']
    x = i*RESOLUTION
    y = j*RESOLUTION
    z = place_height(scene,obj) + place_height(scene,dst) + EPSILON
    d_tf_o = aa.tf2( 1, [x,y,z] )
    g_tf_d = aa.scene_tf_abs(scene,config,dst)
    o_tf_e = aa.scene_tf_rel(scene,config,obj,FRAME)

    g_tf_e = aa.mul( g_tf_d, d_tf_o, o_tf_e )

    return motion_plan(op, g_tf_e)



def op_transfer(scene, config, op):
    obj = op[1]
    dst_frame = op[2]
    dst_i = op[3]
    dst_j = op[4]

    nop = tm.op_nop(scene,config)

    op_pick = pick(nop,obj)
    if False == op_pick:
        print "Pick failed"
        return False

    op_reparent0 = tm.op_reparent( op_pick, FRAME, obj )

    op_place = place( op_reparent0, obj, dst_frame, dst_i, dst_j )

    if False == op_place:
        print "Place failed"
        return False

    op_reparent1 = tm.op_reparent( op_place, dst_frame, obj )

    return [op_pick, op_reparent0, op_place, op_reparent1]

def stack( op, obj, dst ):
    scene = op['final_scene']
    config = op['final_config']
    g_tf_d = aa.scene_tf_abs(scene,config,dst)
    d_tf_o = aa.tf2(1, [0,0, place_height(scene,obj) + place_height(scene,dst) + EPSILON])
    o_tf_e = aa.scene_tf_rel(scene,config,obj,FRAME)
    g_tf_e = aa.mul( g_tf_d, d_tf_o, o_tf_e )
    return motion_plan(op, g_tf_e)


def op_stack( scene, config, op):
    print op
    obj = op[1]
    dst = op[2]

    nop = tm.op_nop(scene,config)
    op_pick = pick(nop, obj)
    if False == op_pick:
        print "Pick failed"
        return False

    op_reparent0 = tm.op_reparent( op_pick, FRAME, obj )

    op_place = stack( op_reparent0, obj, dst )

    if False == op_place:
        print "Place failed"
        return False

    op_reparent1 = tm.op_reparent( op_place, dst, obj )

    return [op_pick, op_reparent0, op_place, op_reparent1]


def refine_operator_linear(scene,config,op):
    print "\n\n** START REFINE **"
    cl.PRINT(op)

    op_name = op[0]

    result = 0
    if op_name == "TRANSFER":
        print "transfer"
        result = op_transfer(scene,config,op)
    elif op_name == "STACK":
        print "stack"
        result = op_stack(scene,config,op)
    else:
        print "Unknown operator"

    print "** END REFINE **\n\n"
    return result

## Register functions
tm.bind_scene_state(scene_state_linear)
tm.bind_scene_objects(scene_objects_linear)
tm.bind_refine_operator(refine_operator_linear)

0
False
