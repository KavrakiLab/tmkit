(in-package :tmsmt)

(defun pddl-sat-op (action)
  (cons (ground-action-name action)
        (ground-action-actual-arguments action)))

(defun pddl-sat-start (ground add-function)
  (destructuring-bind (-and &rest args) (ground-domain-start ground)
    (assert (eq 'and -and))
    (dolist (a args)
      (funcall add-function
               (if (atom a)
                   `(start ,a)
                   (destructuring-bind (op &rest args)
                       a
                     (case op
                       (not `(start ,a))
                       ;; TODO: check that we have a fluent
                       (= (assert (and (cdr args) (null (cddr args))))
                          `(start= ,(first args) ,(second args)))
                       (otherwise
                        `(start ,a)))))))))

(defun pddl-sat-frame (ground)
  ;(print ground-operators)
  (let* ((actions (ground-domain-operators ground))
         (fluents (ground-domain-variables ground))
         (hash (make-hash-table :test #'equal))  ;; hash: variable => (list modifiying-operators)
         (empty-set (make-tree-set #'gsymbol-compare)))

    ;; Index modified variables
    (loop for action in actions
       for op-exp = (fluent-now (pddl-sat-op action))
       do
         (loop for v in (ground-action-modified-variables action)
            for set = (gethash v hash empty-set)
            for setp = (tree-set-insert set op-exp)
            do (setf (gethash v hash) setp)))

    ;; collect axioms
    (loop for f in fluents
       for now = (fluent-now f)
       for next = (fluent-next f)
       for eq = `(= ,now ,next)
       for actions = (tree-set-list (gethash f hash empty-set))
       collect
         (if actions
             `(or ,eq
                  ,(exp-or* actions))
             eq))))


(defun pddl-sat-transition (ground add-function)
  (let* ((actions (ground-domain-operators ground))
         (action-fluents (map 'list #'pddl-sat-op actions)))
    ;(with-collected (add)
    (flet ((add (arg) (funcall add-function arg)))
      ;; operator-encoding
      (loop for a in actions
         for op-exp in action-fluents
         do
           (let ((pre (exp-now (ground-action-precondition a)))
                 (eff (exp-next (ground-action-effect a))))
             (add
              `(or (not (now ,op-exp))          ; action not active
                   (and ,(or pre '|true|)       ; precondition holds
                        ,(if (equal '(and) eff) ; effect holds
                             '|true|
                             eff))))))
      ;; exclusion
      (dolist (op-a action-fluents)
        (add `(=> ,(fluent-now op-a)
                  (and ,@(loop for op-b in action-fluents
                            unless (equal op-a op-b)
                            collect `(not ,(fluent-now op-b)))))))
      ;; frame
      (map nil #'add (pddl-sat-frame ground)))))

(defun pddl-sat-domain (operators facts)
  (let* ((operators (load-operators operators))
         (facts (load-facts facts))
         (ground (ground-domain operators facts)))
  (parse-cpdl
   (with-collected (add)
     ;; State variables
     (do-map (k v (ground-domain-variable-type ground))
       (add `(declare-fluent ,k ,v)))

     ;; Action variables
     (dolist (a (ground-domain-operators ground))
       (let ((a (pddl-sat-op a)))
         (add `(declare-fluent ,a bool))
         (add `(output ,a))))

     ;; Start
     (pddl-sat-start ground #'add)

     ;; Goal
     (destructuring-ecase (ground-domain-goal ground)
       ((and &rest args)
        (dolist (a args)
          (add `(goal ,a)))))

     ;; Transition
     (pddl-sat-transition ground
                          (lambda (x) (add `(transition ,x))))))))


(defun pddl-sat (operators facts &optional options)
  (let ((cpd (pddl-sat-domain operators facts)))
    (multiple-value-bind (results sat)
        (cpd-plan cpd options)
      (values (when sat
                (cpd-actions results))
              sat))))
