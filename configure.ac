#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.65])
AC_INIT([tmsmt], [0.0.1], [ntd@rice.edu])

AM_INIT_AUTOMAKE([subdir-objects])
m4_ifdef([AM_SILENT_RULES], [AM_SILENT_RULES([yes])])

AC_CONFIG_SRCDIR([lisp/tmsmt.asd])


AC_CHECK_PROGS([AARX_CORE], [aarx.core])

AS_IF([test "x$AARX_CORE" = x],
      [AC_MSG_ERROR([Could not found aarx.core.  Is amino installed?])])


AC_CONFIG_FILES([Makefile])
AC_OUTPUT

AS_BOX([TMSMT CONFIGURATION SUMMARY])
AC_MSG_NOTICE([AARX_CORE:         $AARX_CORE])
AS_BOX([END SUMMARY])
