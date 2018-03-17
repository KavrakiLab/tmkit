(in-package :tmsmt)

;(defun smtp-declare-type (type))

(defun smtp-mangle-do (name)
  (concatenate 'string "do-" (string name)))

(defun smtp-rewrite-fluent (step exp)
  `(,(car exp) ,step ,@(cdr exp)))

(defun smtp-rewrite-exp (step exp)
  (apply-rewrite-exp (lambda (exp)
                       (smtp-rewrite-fluent step exp))
                     exp))

(defun smtp-fluent (step name args)
  (smtp-rewrite-fluent step `(,name ,@args)))

(defun smtp-declare-objects (operators facts)
  (declare (ignore operators))
  (list
   (smt-declare-enum 'object
                         (map 'list #'pddl-typed-name
                              (pddl-facts-objects facts)))))

(defun smtp-declare-function (f)
  (smt-declare-fun
   (pddl-function-name f)
   (cons 'Int
         (loop for a in (pddl-function-arguments f)
            collect 'object))
   (pddl-function-type f)))

(defun smtp-declare-actions (operators facts)
  (declare (ignore facts))
  (loop for a in (pddl-operators-actions operators)
       collect
       (smt-declare-fun
        (pddl-action-name a)
        (cons 'Int
              (loop for a in (pddl-action-parameters a)
                 collect 'object))
        'bool)))

(defun smtp-define-action (a)
  (let ((name (pddl-action-name a))
        (args (map 'list #'pddl-typed-name (pddl-action-parameters a))))
    (smt-define-fun
     (smtp-mangle-do (pddl-action-name a))
     (cons (list 'i 'Int)
           (loop for p in args
              collect (list p 'object)))
     'bool
     (smt-implies (smtp-fluent 'i name args)
                  (smt-and (smtp-rewrite-exp 'i (pddl-action-precondition a))
                           (smtp-rewrite-exp '(+ i 1) (pddl-action-effect a)))))))


(defun smtp-define-actions (operators facts)
  (declare (ignore facts))
  (loop for a in (pddl-operators-actions operators)
       collect (smtp-define-action a)))

(defun smtp-frame-axioms-exp (grounded i-var)
  ;(print ground-operators)
  (let ((state-vars (ground-domain-variables grounded))
        (ground-actions (ground-domain-operators grounded))
        (hash (make-hash-table :test #'equal))  ;; hash: variable => (list modifiying-operators)
        (empty-set (make-tree-set #'gsymbol-compare)))
    ;; note modified variables
    (dolist (op ground-actions)
      (let ((fmt-op (smtp-fluent i-var (ground-action-name op)
                                 (ground-action-actual-arguments op))))
        (dolist (v (ground-action-modified-variables op))
          (setf (gethash v hash)
                (tree-set-insert (gethash v hash empty-set)
                                 fmt-op)))))
    ;; collect axioms
    (apply #'smt-and
           (loop for var in state-vars
              for var-i = (smtp-rewrite-exp i-var var)
              for var-j = (smtp-rewrite-exp `(+ ,i-var 1) var)
              for eq = (smt-= var-i var-j)
              for actions = (tree-set-list (gethash var hash empty-set))
              collect
                (if actions
                    (smt-or eq (apply #'smt-or actions))
                    eq)))))


(defun smtp-define-delta (grounded)
  (labels ((delta-fun (name exp)
             (smt-define-fun name '((i int)) 'bool exp)))
    (list
     (smt-comment "Operator Precondition/Effect")
     (delta-fun "delta-trans"
                (cons 'and
                      (loop for op in (ground-domain-operators grounded)
                         collect
                           (smtp-fluent 'i
                                        (smtp-mangle-do (ground-action-name op))
                                        (ground-action-actual-arguments op)))))
     (smt-comment "Frame Axioms")
     (delta-fun "delta-frame"
                (smtp-frame-axioms-exp grounded 'i))
     (delta-fun "delta"
                `(and ("delta-trans" i)
                      ("delta-frame" i))))))

(defun smtp-start (grounded)
  (list (smt-assert (smtp-rewrite-exp 0 (ground-domain-start grounded)))))

(defun smtp-goal (grounded i)
  (list (smt-assert (smtp-rewrite-exp i (ground-domain-goal grounded)))))

(defun smtp-plan (operators facts)
  (let* ((operators (load-operators operators))
         (facts (load-facts facts))
         (grounded (ground-domain operators facts)))

    (append
     (list (smt-comment "Objects"))
     (smtp-declare-objects operators facts)
     (list (smt-comment "Fluents"))
     (map 'list #'smtp-declare-function (pddl-operators-functions operators))
     (list (smt-comment "Action Variables"))
     (smtp-declare-actions operators facts)
     (list (smt-comment "Action Functions"))
     (smtp-define-actions operators facts)
     (list (smt-comment "Transition Function"))
     (smtp-define-delta grounded)
     (list (smt-comment "Transitions"))
     (list
      (smt-declare-const 'h 'Int)
      (smt-assert `(>= H 0))
      `(|minimize| H)
      (smt-assert (smt-forall '((i Int))
                              (smt-ite
                               `(and (< i h)
                                     (>= i 0))
                               ;'(< i h)
                               `("delta" i)
                               'true))))
     (list (smt-comment "Start"))
     (smtp-start grounded)
     (list (smt-comment "Goal"))
     (smtp-goal grounded 'h)
     )))
