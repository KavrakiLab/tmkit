(in-package :tmsmt)


(defparameter *base*
  (robray::format-pathname "~A/../pddl/itmp/"
                           (asdf:system-source-directory :tmsmt)))

(defparameter *operators*
  (load-operators (robray::format-pathname "~A/itmp-blocks-linear.pddl" *base*)))

(defparameter *facts*
  (load-facts (robray::format-pathname "~A/blocks-linear-0.pddl" *base*)))

(defparameter *ground* (ground-domain *operators* *facts*))

*ground*
