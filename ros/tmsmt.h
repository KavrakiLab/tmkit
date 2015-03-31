#ifndef TMSMT_H
#define TMSMT_H

#ifdef __cplusplus
#define TMSMT_API extern "C"
extern "C" {
#endif


void
tmsmt_ros_init( );

struct tmsmt_model;

struct tmsmt_model *
tmsmt_model_load( const char *name );


void
tmsmt_model_destroy( struct tmsmt_model *);

int
tmsmt_model_set_start( struct tmsmt_model *p,
                       const char *group,
                       size_t n,
                       const double *goal );

int
tmsmt_model_plan_simple( struct tmsmt_model *p,
                         const char *group,
                         size_t n,
                         const double *goal );


int
tmsmt_model_plan_ik( struct tmsmt_model *p,
                     const char *group,
                     const char *global_frame,
                     const char *end_frame,
                     const double *q,
                     const double *v,
                     double epsilon_angle,
                     double epsilon_x );

#ifdef __cplusplus
}
#endif

#endif /*TMSMT_H*/
