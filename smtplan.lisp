(in-package :tmsmt)

(defstruct action
  name
  parameters
  precondition
  effect)

(defstruct predicate
  name
  arity)

(defstruct operators
  name
  predicates
  actions)

(defstruct facts
  name
  domain
  objects
  init
  goal)

(defun load-sexp (filename)
  (with-open-file (s filename :direction :input)
    (read s)))

(defun load-operators (filename)
  (parse-operators (load-sexp filename)))

(defun load-facts (filename)
  (parse-facts (load-sexp filename)))

(defun check-symbol (value required)
  (unless (string= (string value) (string required))
    (error "Symbol mismatch on ~A, required ~A" value required)))

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
          ((:action name &key parameters precondition effect)
           (push (make-action :name name
                              :parameters parameters
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


(defun smt-plan (operator-file fact-file steps)
  ;; initial state
  ;; goal state
  ;; operator encodings
  ;; frame axioms
  ;; exclusion axioms
)
