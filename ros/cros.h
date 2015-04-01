#ifndef CROS_H
#define CROS_H

#ifdef __cplusplus
extern "C" {
#endif

struct cros_node_handle;

void cros_init(int argc, char **argv, const char *name );

struct cros_node_handle *
cros_node_handle_create( const char *name );

void
cros_node_handle_destroy( struct cros_node_handle * );

char *
cros_node_handle_get_namespace_dup( struct cros_node_handle * nh);

#ifdef __cplusplus
}
#endif

#endif
