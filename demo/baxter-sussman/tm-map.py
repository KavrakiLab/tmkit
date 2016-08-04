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
        name = aa.frame_name(frame)
        parent_name = aa.frame_parent(frame)
        parent_frame = aa.find_frame(scene,parent_name)

        if aa.frame_isa(parent_frame, "surface"):
            trans = aa.translation( aa.frame_fixed_tf(frame) )
            i = int(round( aa.vec_x(trans) / RESOLUTION))
            j = int(round( aa.vec_y(trans) / RESOLUTION))
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



## Register functions
tm.bind_scene_state(scene_state_linear)

0







    # def print_frame(frame):
    #     print aa.frame_name(frame)


    #aa.map_frames(handle_frame,scene)
    # print "Moveable Frames"
    # print "==============="
    # map(print_frame, moveable_frames)
    # print ""

    # print "Stackable Frames"
    # print "================"
    # map(print_frame, moveable_frames)
    # print ""
