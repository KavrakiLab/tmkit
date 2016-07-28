
bin_PROGRAMS =
noinst_PROGRAMS =

AM_CPPFLAGS = -I$(top_srcdir)/include -I$(top_builddir)/include

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
	lisp/tmsmt.asd


tmsmt.core$(EXEEXT): $(tmsmt_core_SOURCES)
	$(AARX_CORE) --script build.lisp


doc/manual/planfile.html: doc/md/planfile.md doc/md/head.html doc/md/foot.html
	$(MKDIR_P) `dirname "$@"`
	cp doc/md/head.html $@ && \
	markdown $< >> $@ && \
	cat doc/md/foot.html >> $@


src/planfile.c: src/planfile.l
	$(LEX) -t $(top_srcdir)/src/planfile.l > src/planfile.c

noinst_PROGRAMS += planfile_test
planfile_test_SOURCES = src/planfile.c src/tmplan_test.c
planfile_LDFLAGS = -lfl


clean-local:
	-rm -rf doc/manual/
