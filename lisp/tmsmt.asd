(cl:eval-when (:load-toplevel :execute)
    (asdf:operate 'asdf:load-op 'cffi-grovel))

(asdf:defsystem tmsmt
  :description "SMT-based planner"
  :depends-on ("alexandria" "cl-ppcre" "sycamore" "cffi" "amino" "amino-rx" "amino-py")
  :components (
               ;; SMT Symbols
               (:file "smt/smt-symbols")

               ;; Z3
               (:file "z3/package")
               (cffi-grovel:grovel-file "z3/z3-grovel" :depends-on ("z3/package"))
               (:file "z3/type" :depends-on ("z3/z3-grovel"))
               (:file "z3/lib" :depends-on ("z3/type"))
               (:file "z3/api" :depends-on ("z3/lib"))

               (:file "package")

               (:file "dir" :depends-on ("package"))
               (cffi-grovel:grovel-file "grovel" :depends-on ("dir"))

               (:file "util" :depends-on ("package"))
               (:file "config" :depends-on ("package"))
               (:file "smtlib" :depends-on ("util"))
               (:file "smtrun" :depends-on ("smtlib"))
               (:file "expression" :depends-on ("util"))
               (:file "pddl" :depends-on ("util"))
               (:file "pddl-cgen" :depends-on ("pddl" "planner"))
               (:file "planner" :depends-on ("util" "expression" "pddl" "smtrun"))
               (:file "tm-plan" :depends-on ("util"))
               (:file "genscene" :depends-on ("util"))

               ;; OMPL
               ;(:file "ompl" :depends-on ("util" "moveit"))
               ;(:file "synergistic-defs" :depends-on ("ompl" "ros/ros-container"))
               ;(:file "synergistic" :depends-on ("synergistic-defs"))

               (:file "placement-graph" :depends-on ("pddl"))
               (:file "motion-plan" :depends-on ("util"))
               ;(:file "moveit" :depends-on ("ros/ros-scene" "ros/ros-container" "motion-plan"))
               ;(:file "m-actions" :depends-on ("util" "motion-plan"))
               (:file "itmp-rec" :depends-on ("util"))
               (:file "driver" :depends-on ("itmp-rec" "util" "config"))

               (:file "foreign-tmplan" :depends-on ("tm-plan"))
               ;(:file "planvis" :depends-on ("util"))

               ;;; Python Interface
               (:file "python/tmsmtpy" :depends-on ("package" "util" "tm-plan"))
               ))
