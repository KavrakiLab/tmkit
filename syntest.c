#include <stdlib.h>
#include <ompl/geometric/planners/ltl/syn.h>


int main(int argc, char **argv )
{
    size_t n_obj = 1;
    size_t n_location = 8;
    //size_t n_goal = 1;

    size_t obj_loc[n_obj];
    size_t n_label[n_location];
    size_t *labels[n_location];

    size_t goal_obj_index[1] = {0};
    size_t goal_obj_label[1] = {4};

    //for( size_t i = 0; i < n_obj; i ++ ) {
    obj_loc[0] = 4;
    //}


    for( size_t i = 0; i < n_location; i ++ ) {
        n_label[i] = 1;
    }

    for( size_t i = 0; i < n_location; i ++ ) {
        labels[i] = (size_t*)malloc(sizeof(size_t));
        labels[i][0] = i;
    }

    struct syn_handle *h =
        syn_handle_create( n_obj,
                           obj_loc,
                           n_location, n_label, labels );

    syn_handle_goal(h,1,goal_obj_index, goal_obj_label );

    struct syn_plan p;


    syn_handle_plan( h, &p );


    return 0;
}
