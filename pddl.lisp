(in-package :tmsmt)


(defstruct action
  "A PDDL action"
  name
  parameters
  precondition
  uncontrollable
  effect
  )

(defstruct predicate
  "A PDDL predicate"
  name
  arity)

(defstruct operators
  "A PDDL set of operators"
  name
  predicates
  actions)

(defstruct facts
  "A PDDL set of facts"
  name
  domain
  objects
  init
  goal)

(defun load-operators (filename)
  "Load operators from `FILENAME'."
  (typecase filename
    (operators filename)
    ((or string pathname) (parse-operators (load-sexp filename)))))

(defun load-facts (filename)
  "Load facts from `FILENAME'."
  (etypecase filename
    (facts filename)
    ((or string pathname) (parse-facts (load-sexp filename)))))

(defun parse-operators (sexp)
  (destructuring-bind (-define (-domain name) &rest clauses)
      sexp
    (check-symbol -define :define)
    (check-symbol -domain :domain)
    (let ((ops (make-operators :name name)))
      (dolist (clause clauses)
        (destructuring-ecase clause
          ((:predicates &rest predicates)
           (setf (operators-predicates ops)
                 (loop for p in predicates
                    collect (destructuring-bind (name &rest arguments) p
                              (make-predicate :name name :arity (length arguments))))))
          ((:action name &key parameters uncontrollable precondition effect)
           (push (make-action :name name
                              :parameters parameters
                              :uncontrollable uncontrollable
                              :precondition precondition
                              :effect effect)
                 (operators-actions ops)))))
      ops)))

(defun parse-facts (sexp)
  (destructuring-bind (-define (-problem name) &rest clauses)
      sexp
    (check-symbol -define :define)
    (check-symbol -problem :problem)
    (let ((facts (make-facts :name name)))
      (dolist (clause clauses)
        (destructuring-ecase clause
          ((:domain name)
           (setf (facts-domain facts)
                 name))
          ((:objects &rest objs)
           (setf (facts-objects facts)
                 objs))
          ((:init &rest things)
           (setf (facts-init facts)
                 things))
          ((:goal goal)
           (setf (facts-goal facts)
                 goal))))
      facts)))



(defun pddl-print (exp &optional (stream *standard-output*))
  ;; Use the lisp printer to pretty print the expressions, then fixup
  ;; the output with some regular expressions
  (let* ((cl-string (with-output-to-string (s)
                      (print exp s)))
         ;; eat CL case quotes
         (string-0 (ppcre:regex-replace-all "\\|([\\w\\-]+)\\|"
                                                cl-string
                                                "\\1"))
         ;; eat string quotes
         (string-1 (ppcre:regex-replace-all "\"([\\w\\-]+)\""
                                                string-0
                                                "\\1")))
    (princ string-1 stream))
  nil)
