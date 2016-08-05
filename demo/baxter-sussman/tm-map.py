# python

import aminopy as aa
import tmsmtpy as tm
import CL
import math

tm.hello()

RESOLUTION=0.1


def scene_state_linear(scene, configuration):
    '''Map the scene graph `scene' to a task state expression'''

    ## terms in the expression
    conjunction = ["AND"]

    def handle_moveable(frame):
        name = frame['name']
        parent_name = frame['parent']
        parent_frame = scene[parent_name]

        if aa.frame_isa(parent_frame, "surface"):
            trans = aa.translation( aa.frame_fixed_tf(frame) )
            i = int(round( trans[0] / RESOLUTION))
            j = int(round( trans[1] / RESOLUTION))
            conjunction.append(["=",
                                ["POSITION", name],
                                tm.mangle(parent_name,i,j)])

        if aa.frame_isa(parent_frame, "stackable"):
            print "  stacked"
            conjunction.append(["=",
                                ["POSITION", name],
                                parent_name])

    moveable_frames = tm.collect_frame_type(scene,"moveable")
    map(handle_moveable, moveable_frames)

    return conjunction

## END def scene_state_linear

def scene_objects_linear(scene):
    obj = []

    def type_names(thing):
        return [ f['name']
                 for f in
                 tm.collect_frame_type(scene,thing) ]

    # Moveable objects are blocks
    moveable = type_names("moveable")
    moveable.insert(0, "BLOCK")

    # Draw grid on surfaces
    locations = ['LOCATIONS']
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


## Register functions
tm.bind_scene_state(scene_state_linear)
tm.bind_scene_objects(scene_objects_linear)

0
