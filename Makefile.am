AM_CPPFLAGS = -I$(top_srcdir)/include -I$(top_builddir)/include
ACLOCAL_AMFLAGS = -I m4

bin_PROGRAMS =
bin_SCRIPTS =
noinst_PROGRAMS =
lib_LTLIBRARIES =

## Shared Library ##

lib_LTLIBRARIES += libtmsmt.la

libtmsmt_la_SOURCES = \
	src/planfile.c \
	src/tmplan.c

src/planfile.c: src/planfile.l
	$(LEX) -t $(top_srcdir)/src/planfile.l > src/planfile.c

## Lisp Core ##

bin_PROGRAMS += tmsmt.core
tmsmt_core_SOURCES = \
	build.lisp \
	lisp/package.lisp \
	lisp/util.lisp \
	lisp/smtlib.lisp \
	lisp/smtrun.lisp \
	lisp/expression.lisp \
	lisp/pddl.lisp \
	lisp/pddl-cgen.lisp \
	lisp/planner.lisp \
	lisp/tm-plan.lisp \
	lisp/genscene.lisp \
	lisp/placement-graph.lisp \
	lisp/motion-plan.lisp \
	lisp/m-actions.lisp \
	lisp/itmp-rec.lisp \
	lisp/driver.lisp \
	lisp/python/tmsmtpy.lisp \
	lisp/tmsmt.asd


tmsmt.core$(EXEEXT): $(tmsmt_core_SOURCES)
	$(AARX_CORE) --script build.lisp

bin_SCRIPTS += tmsmt




noinst_PROGRAMS += planfile_test
planfile_test_SOURCES = src/tmplan_test.c
planfile_test_LDADD = libtmsmt.la


if HAVE_DOXYGEN
scriptapi.md: $(tmsmt_core_SOURCES)
	sbcl --eval '(require :tmsmt)' --eval '(require :ntdoc)' \
	     --eval '(ntdoc::markdown "tmsmtpy" :system :tmsmt :target "scriptapi.md" :title "Domain Script API (Python)")' \
	     --eval '(sb-ext:quit)'

doxygen: scriptapi.md
	$(DOXYGEN)
endif


if HAVE_HELP2MAN
doc/tmsmt.1: $(top_srcdir)/tmsmt $(top_srcdir)/configure.ac
	$(HELP2MAN) -h -h --version-string="0.0" --no-info -n "Task-Motion Planner" $(top_srcdir)/tmsmt -o $@
endif

clean-local:
	-rm -rf doc/manual/
