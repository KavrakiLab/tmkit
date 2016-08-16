AM_CPPFLAGS = -I$(top_srcdir)/include -I$(top_builddir)/include
ACLOCAL_AMFLAGS = -I m4

bin_PROGRAMS =
bin_SCRIPTS =
dist_bin_SCRIPTS =
noinst_PROGRAMS =
lib_LTLIBRARIES =
EXTRA_DIST =


####################
## Shared Library ##
####################

lib_LTLIBRARIES += libtmsmt.la

libtmsmt_la_SOURCES = \
	src/planfile.c \
	src/tmplan.c

EXTRA_DIST += src/planfile.l
src/planfile.c: src/planfile.l
	$(LEX) -t $(top_srcdir)/src/planfile.l > src/planfile.c


EXTRA_DIST += include/tmsmt/tmplan.h \
              include/tmsmt/tmplan_internal.h

###############
## Lisp Core ##
###############

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

EXTRA_DIST += load.lisp build.lisp
tmsmt.core$(EXEEXT): $(tmsmt_core_SOURCES) libtmsmt.la
	top_srcdir=$(top_srcdir) \
	top_builddir=$(top_builddir) \
	LD_LIBRARY_PATH=.libs:$(LD_LIBRARY_PATH) \
		$(AARX_CORE) --script $(top_srcdir)/build.lisp

dist_bin_SCRIPTS += tmsmt


noinst_PROGRAMS += planfile_test
planfile_test_SOURCES = src/tmplan_test.c
planfile_test_LDADD = libtmsmt.la

###################
## Documentation ##
###################

EXTRA_DIST += doc.lisp

if HAVE_DOXYGEN
EXTRA_DIST += scriptapi.md
scriptapi.md: $(tmsmt_core_SOURCES)
	LD_LIBRARY_PATH=.libs:$(LD_LIBRARY_PATH) \
	top_srcdir=$(top_srcdir) \
	top_builddir=$(top_builddir) \
	sbcl --non-interactive \
	     --eval '(load "doc.lisp")' \
	     --eval '(sb-ext:quit)'

doxygen: scriptapi.md
	$(DOXYGEN)

doc/manual: doxygen

else

doc/manual:
	mkdir doc/manual

endif


if HAVE_HELP2MAN
EXTRA_DIST += doc/tmsmt.1
doc/tmsmt.1: $(top_srcdir)/tmsmt $(top_srcdir)/configure.ac
	$(HELP2MAN) -h -h --version-string="0.0" --no-info -n "Task-Motion Planner" $(top_srcdir)/tmsmt -o $@


if HAVE_GROFF
EXTRA_DIST += doc/manual/man_tmsmt.html
doc/manual/man_tmsmt.html: doc/tmsmt.1
	$(MKDIR_P) doc/manual
	$(GROFF) -mandoc -Thtml < doc/tmsmt.1 > doc/manual/man_tmsmt.html
endif

endif

EXTRA_DIST += doc/md/command.md \
              doc/md/copying.md \
              doc/md/domain_script.md \
              doc/md/foot.html \
              doc/md/head.html \
              doc/md/install.md \
              doc/md/mainpage.md \
              doc/md/planfile.md \
              doc/md/ReadMe.md \
              doc/md/tutorial.md \
              doc/manual

clean-local:
	-rm -rf doc/manual/ doc/doxygen_sqlite3.db

###########
## Demos ##
###########

EXTRA_DIST += demo/baxter-sussman/allowed-collision.robray \
              demo/baxter-sussman/run.lisp \
              demo/baxter-sussman/sussman-1.robray \
              demo/baxter-sussman/table.robray \
              demo/baxter-sussman/class.robray \
              demo/baxter-sussman/sussman-0.robray \
              demo/domains/blocksworld/blocks-domain.pddl \
              demo/domains/blocksworld/tm-blocks.pddl \
              demo/domains/blocksworld/tm-sussman.pddl \
              demo/domains/blocksworld/sussman-anomaly.pddl \
              demo/domains/blocksworld/tm-blocks.py \
              demo/domains/blocksworld/tm-blocks-safety.pddl \
              demo/domains/linear-blocksworld/linear-blocksworld.pddl \
              demo/domains/linear-blocksworld/linear-blocksworld.py \
              demo/baxter-sussman.pddl \
              demo/run-sussman.sh \
              demo/run-baxter-sussman.sh \
              demo/run-baxter-sussman-safety.sh \
              demo/run-baxter-sussman-linear.sh \
              demo/demo-path.sh
