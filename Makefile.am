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
	load.lisp \
	lisp/package.lisp \
	lisp/grovel.lisp \
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
	lisp/foreign-tmplan.lisp \
	lisp/python/tmsmtpy.lisp \
	lisp/tmsmt.asd

nodist_tmsmt_core_SOURCES = \
	$(top_builddir)/lisp/dir.lisp \
	$(top_builddir)/lisp/config.lisp

$(top_builddir)/lisp/dir.lisp: configure Makefile
	echo "(in-package :tmsmt) " > lisp/dir.lisp
	echo "(defparameter *libdir* (pathname \"${libdir}/\"))" >>  lisp/dir.lisp
	echo "(defparameter *builddir* (pathname \"${top_builddir}/\"))" >>  lisp/dir.lisp
	echo "(defparameter *srcdir* (pathname \"${top_srcdir}/\"))" >>  lisp/dir.lisp
	echo "(defparameter *abs-builddir* (pathname \"${abs_top_builddir}/\"))" >>  lisp/dir.lisp
	echo "(defparameter *abs-srcdir* (pathname \"${abs_top_srcdir}/\"))" >>  lisp/dir.lisp

tmsmt.core$(EXEEXT): $(tmsmt_core_SOURCES) $(nodist_tmsmt_core_SOURCES) libtmsmt.la
	$(MKDIR_P) lisp/python/
	if test "x$(top_srcdir)" != "x$(top_builddir)"; then \
		for i in $(tmsmt_core_SOURCES); \
		do \
			cp -v "$(top_srcdir)/$$i" "$(top_builddir)/$$i"; \
		done; \
	fi
	top_srcdir=$(top_srcdir) \
	top_builddir=$(top_builddir) \
	LD_LIBRARY_PATH=.libs:$(LD_LIBRARY_PATH) \
		$(AARX_CORE) --script $(top_srcdir)/build.lisp

dist_bin_SCRIPTS += src/tmsmt


noinst_PROGRAMS += planfile_test
planfile_test_SOURCES = src/tmplan_test.c
planfile_test_LDADD = libtmsmt.la

###################
## Documentation ##
###################

EXTRA_DIST += doc.lisp
EXTRA_DIST += py-api.md lisp-api.md

if HAVE_DOXYGEN


py-api.md: tmsmt.core $(top_srcdir)/doc.lisp
	LD_LIBRARY_PATH=.libs:$(LD_LIBRARY_PATH) \
	top_srcdir=$(top_srcdir) \
	top_builddir=$(top_builddir) \
	./tmsmt.core \
	     --eval "(load \"$(top_srcdir)/doc.lisp\")" \
	     --eval '(sb-ext:quit)'

lisp-api.md: py-api.md

doxygen: py-api.md lisp-api.md doc/md/copying.md doc/md/mainpage.md doc/md/authors.md Doxyfile
	$(DOXYGEN)

doc/md/copying.md: $(top_srcdir)/COPYING $(top_srcdir)/doc/md/copying.md.header
	$(MKDIR_P) doc/md/
	cat $(top_srcdir)/doc/md/copying.md.header  \
	    $(top_srcdir)/COPYING \
	    > doc/md/copying.md

doc/md/authors.md: $(top_srcdir)/AUTHORS $(top_srcdir)/doc/md/authors-head.md
	$(MKDIR_P) doc/md/
	cat $(top_srcdir)/doc/md/authors-head.md \
	    $(top_srcdir)/AUTHORS \
	    > doc/md/authors.md

doc/manual: doxygen

doc: doxygen

else

doc/manual:
	mkdir doc/manual

endif


if HAVE_HELP2MAN
EXTRA_DIST += doc/tmsmt.1
doc/tmsmt.1: tmsmt src/tmsmt configure.ac tmsmt.core$(EXEEXT)
	$(MKDIR_P) doc
	$(HELP2MAN) --version-option=--version-man --no-info -n "Task-Motion Planner" $(top_builddir)/tmsmt -o $@


if HAVE_GROFF
EXTRA_DIST += doc/manual/man_tmsmt.html
doc/manual/man_tmsmt.html: doc/tmsmt.1
	$(MKDIR_P) doc/manual
	$(GROFF) -mandoc -Thtml < doc/tmsmt.1 > doc/manual/man_tmsmt.html

doxygen: doc/manual/man_tmsmt.html

endif

endif

sync-doc:
	rsync -r doc/manual/ tmkit.kavrakilab.org:/srv/www/amino

EXTRA_DIST += doc/md/mainpage.md \
              doc/md/command.md \
              doc/md/copying.md.header \
              doc/md/authors-head.md \
              doc/md/semantics.md \
              doc/md/foot.html \
              doc/md/head.html \
              doc/md/install.md \
              doc/md/planfile.md \
              doc/md/tutorial.md \
              doc/md/citations.md \
              doc/md/ReadMe.md \
              doc/header.html \
              doc/footer.html \
              doc/manual

clean-local:
	-rm -rf doc/manual/ doc/doxygen_sqlite3.db

distclean-local:
	-rm -rf py-api.md lisp-api.md doc/tmsmt.1 doc/md/authors.md doc/md/copying.md
	if test "x$(top_srcdir)" != "x$(top_builddir)"; then \
		rm -rf $(top_builddir)/lisp build.lisp load.lisp; \
	fi

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
              demo/domains/blocksworld/blocks-safety-goal.pddl \
              demo/domains/linear-blocksworld/linear-blocksworld.pddl \
              demo/domains/linear-blocksworld/linear-blocksworld.py
