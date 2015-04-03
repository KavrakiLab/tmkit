(asdf:defsystem tmsmt
  :description "SMT-based planner"
  :depends-on ("alexandria" "cl-ppcre" "sycamore" "motion-grammar-kit" "cffi")
  :components ((:file "package")
               (:file "util" :depends-on ("package"))
               (:file "smtlib" :depends-on ("util"))
               (:file "expression" :depends-on ("util"))
               (:file "pddl" :depends-on ("util"))
               (:file "placement-graph" :depends-on ("pddl"))
               (:file "planner" :depends-on ("util" "expression" "pddl" "smtlib"))))
