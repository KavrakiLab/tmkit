#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.65])
AC_INIT([tmkit], [0.0.1-alpha1], [ntd@rice.edu])

AM_INIT_AUTOMAKE([subdir-objects])
m4_ifdef([AM_SILENT_RULES], [AM_SILENT_RULES([yes])])

AC_CONFIG_SRCDIR([lisp/tmsmt.asd])
AC_CONFIG_HEADERS([config.h])
AC_CONFIG_MACRO_DIR([m4])

AC_PROG_CC_C99
LT_INIT

AC_CHECK_PROGS([AARX_CORE], [aarx.core])

AS_IF([test "x$AARX_CORE" = x],
      [AC_MSG_ERROR([Could not found aarx.core.  Is amino installed?])])


# Check for Lex/Flex
AC_ARG_WITH([lex],
            AS_HELP_STRING([--without-lex], [Do not run lex/flex]),
            [],
            [with_lex=yes])
AS_IF([test "x$with_lex" != xyes],
      [AM_PROG_LEX])
AM_CONDITIONAL([HAVE_LEX], [test "x$LEX" != x -a "x$with_lex" = xyes])


# Amino
PKG_CHECK_MODULES([AMINO], [amino],
[
  CFLAGS="$CFLAGS $AMINO_CFLAGS"
  CXXFLAGS="$CXXFLAGS $AMINO_CXXFLAGS"
  LDFLAGS="$LDFLAGS $AMINO_LIBS"
],
[
  AC_MSG_ERROR([Amino is required])
])


# Doxygen
AC_ARG_WITH([doxygen],
            AS_HELP_STRING([--without-doxygen], [Disable doxygen support]),
            [],
            [with_doxygen=auto])
AS_IF([test "x$with_doxygen" != xno],
      [AC_CHECK_PROGS([DOXYGEN],[doxygen])])
AS_IF([test "x$with_doxygen" = xyes -x "x$DOXYGEN" = x],
      [AC_MSG_ERROR([Doxygen not found])])
AM_CONDITIONAL([HAVE_DOXYGEN], [test "x$DOXYGEN" != x])

# Man Pages
AC_ARG_ENABLE([man],
              [AS_HELP_STRING([--disable-man], [Do not build man pages])],
              [],
              [enable_man="yes"])

AS_IF([test "x$enable_man" = xyes -a "x$build" = "x$host"],
      [AC_CHECK_PROGS([HELP2MAN], [help2man])
       AC_CHECK_PROGS([GROFF], [groff])])

AM_CONDITIONAL([HAVE_HELP2MAN], [test x$HELP2MAN != x])
AM_CONDITIONAL([HAVE_GROFF], [test x$GROFF != x])

# Demos

AC_DEFUN([DEF_DEMO],
[
AC_ARG_ENABLE([demo-$1],
              [AS_HELP_STRING([--enable-demo-$1], [Build the $1 demo])],
              [],
              [])

AS_IF([test "x$enable_demo_$1" = "xyes"],
      [ENABLED_DEMOS="$1 $ENABLED_DEMOS"])

AM_CONDITIONAL([BUILD_DEMO_$2], [test "x$enable_demo_$1" = "xyes"])

])

DEF_DEMO([baxter],[BAXTER])


# Output
AC_CONFIG_FILES([Makefile Doxyfile lisp/config.lisp])

AC_DEFUN([CONFIG_SCRIPT],
         [AC_CONFIG_FILES([$1],
                          [chmod +x $1])])

CONFIG_SCRIPT([tmsmt])

AC_CONFIG_FILES([demo-path.sh])
CONFIG_SCRIPT([demo/run/run-sussman.sh])
CONFIG_SCRIPT([demo/run/run-baxter-sussman.sh])
CONFIG_SCRIPT([demo/run/run-baxter-sussman-safety.sh])
CONFIG_SCRIPT([demo/run/run-baxter-sussman-linear.sh])

AC_OUTPUT

AS_BOX([TMSMT CONFIGURATION SUMMARY])
AC_MSG_NOTICE([AARX_CORE:         $AARX_CORE])
AC_MSG_NOTICE([LEX:               $LEX])
AS_BOX([END SUMMARY])
