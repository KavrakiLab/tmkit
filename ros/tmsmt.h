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
tmsmt_model_load( const char *urdf_filename,
                  const char *srdf_filename );


void
tmsmt_model_destroy( struct tmsmt_model *);

int
tmsmt_model_set_start( struct tmsmt_model *p,
                       const char *group,
                       size_t n,
                       double *goal );

int
tmsmt_model_plan_simple( struct tmsmt_model *p,
                         const char *group,
                         size_t n,
                         double *goal );


#ifdef __cplusplus
}
#endif

#endif /*TMSMT_H*/
