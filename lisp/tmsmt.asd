(asdf:defsystem tmsmt
  :description "SMT-based planner"
  :depends-on ("alexandria" "cl-ppcre" "sycamore" "motion-grammar-kit" "cffi" "amino" "amino-rx")
  :components ((:file "package")
               (:file "util" :depends-on ("package"))
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
               (:file "m-actions" :depends-on ("util" "motion-plan"))
               (:file "itmp-rec" :depends-on ("util" "m-actions"))
               ;(:file "planvis" :depends-on ("util"))
               ))
