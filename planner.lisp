(in-package :tmsmt)


;;; ENCODING,
;;;  - PDDL Objects are state variables

(defun collect-args (objects arity)
  (if (zerop arity)
      (list nil)
      (loop for o in objects
         nconc
           (loop for args in (collect-args objects (1- arity))
              collect (cons o args)))))


(defun format-state-variable (predicate step)
  (format nil "~{~A~^_~}_~D" predicate step))

(defun format-op (op args step)
  (format nil "~A_~{~A~^_~}_~D" op args step))

(defun unmangle-op (mangled)
  (let ((list (ppcre:split "_" mangled)))
    (cons (parse-integer (lastcar list))
          (loop for x on list
             for a = (car x)
             when (cdr x)
             collect
             a))))


(defun create-state-variables (predicates objects)
  (loop for p in predicates
     append
       (loop for args in (collect-args objects (predicate-arity p))
          collect (cons (predicate-name p) args))))

(defstruct concrete-action
  name
  actual-arguments
  precondition
  effect)

(defun format-concrete-action (op step)
  (format-op (concrete-action-name op)
             (concrete-action-actual-arguments op)
             step))

(defun exp-args-alist (dummy-args actual-args)
  "Find alist for argument replacement"
  (assert (= (length dummy-args) (length actual-args)))
  (loop
     for d in dummy-args
     for a in actual-args
     collect (cons d a)))

;; (defun action-add-del (concrete-precondition concrete-effect)
;;   (declare (ignore concrete-precondition))
;;   (destructuring-bind (-and &rest things) concrete-effect
;;     (check-symbol -and 'and)
;;     (let ((add) (del))
;;       (dolist (exp things)
;;         (if (and (listp exp)
;;                  (eq (car exp) 'not))
;;             (progn (assert (null (cddr exp)))
;;                    (push (second exp) del))
;;             (push exp add))))
;;     (values add del)))

(defun smt-concrete-actions (actions objects)
  (let ((result))
    (dolist (action (operators-actions actions))
      (dolist (args (collect-args objects
                                  (length (action-parameters action))))
        (let ((arg-alist (exp-args-alist (action-parameters action)
                                         args)))
          (push (make-concrete-action
                 :name (action-name action)
                 :actual-arguments args
                 :precondition (sublis arg-alist (action-precondition action))
                 :effect (sublis arg-alist (action-effect action)))
                result))))
    result))

;;(defun smt-encode-all-operators (operators step objects)
  ;;(let ((arg-set (collect-args objects (length (action-parameters operator)))))
  ;; collect operator instanciations
  ;; operator application axioms
  ;; exclusion axioms
  ;; frame axioms

(defun concrete-action-modifies-varable-p (action variable)
  (let ((not-variable (list 'not variable)))
    (destructuring-bind (-and &rest things) (concrete-action-effect action)
      (check-symbol -and 'and)
      (labels ((rec (rest)
                 (when rest
                   (let ((x (first rest)))
                     (if (or (equal x variable)
                             (equal x not-variable))
                         t
                         (rec (cdr rest)))))))
        (rec things)))))

(defun concrete-action-modified-variables (action)
  (destructuring-bind (-and &rest things) (concrete-action-effect action)
    (check-symbol -and 'and)
    (loop for exp in things
       collect
         (destructuring-case exp
           ((not x) x)
           ((t &rest rest) (declare (ignore rest))
            exp)))))

(defun smt-frame-axioms (state-vars concrete-actions step)
  ;(print concrete-operators)
  (let ((hash (make-hash-table :test #'equal))) ;; hash: variable => (list modifiying-operators)
    ;; note modified variables
    (dolist (op concrete-actions)
      (dolist (v (concrete-action-modified-variables op))
        (push op (gethash v hash))))
    ;; collect axioms

    ;(loop for var in state-vars
       ;do (print (gethash var hash)))
    (loop for var in state-vars
       collect
         (smt-assert (smt-or (list '=
                                   (format-state-variable var step)
                                   (format-state-variable var (1+ step)))
                             (apply #'smt-or
                                    (loop for op in (gethash var hash)
                                       collect (format-concrete-action op step))))))))



(defun smt-plan-encode (operators facts steps)
  (let* ((smt-statements nil)
         (state-vars (create-state-variables (operators-predicates operators)
                                             (facts-objects facts)))
         (concrete-actions (smt-concrete-actions operators  (facts-objects facts)))
         (step-ops))
    (labels ((stmt (x)
               (push x smt-statements))
             (declare-step (x)
               (stmt (smt-declare-fun  x () 'bool))))
      ;; per-step state variables
      ;; create the per-step state
      (dotimes (i (1+ steps))
        (dolist (v state-vars)
          (declare-step (format-state-variable v i))))

      ;; per-step action variables
      (dotimes (i  steps)
        (dolist (op concrete-actions)
          (let ((v (format-concrete-action op i)))
            (push v step-ops)
            (declare-step v ))))

      ;; initial state
      (let* ((initial-true (facts-init facts))
             (initial-false (set-difference  state-vars initial-true :test #'equal)))
        (dolist (p initial-true)
          (stmt (smt-assert (format-state-variable p 0))))
        (dolist (p initial-false)
          (stmt (smt-assert (smt-not (format-state-variable p 0))))))
      ;; goal state
      (let* ((goal (facts-goal facts)))
        (stmt (smt-assert (rewrite-exp goal steps))))
      ;; operator encodings
      (dotimes (i steps)
        (dolist (op concrete-actions)
          (stmt (smt-assert `(or (not ,(format-op (concrete-action-name op)
                                                  (concrete-action-actual-arguments op)
                                                  i))
                                 (and ,(rewrite-exp (concrete-action-precondition op) i)
                                      ,(rewrite-exp (concrete-action-effect op) (1+ i))))))))


      ;; exclusion axioms
      (dotimes (i steps)
        (dolist (op concrete-actions)
          (stmt (smt-assert `(=> ,(format-op (concrete-action-name op)
                                             (concrete-action-actual-arguments op)
                                             i)
                                 (and ,@(loop for other-op in concrete-actions
                                           unless (eq op other-op)
                                           collect `(not ,(format-op (concrete-action-name other-op)
                                                                     (concrete-action-actual-arguments other-op)
                                                                     i)))))))))
      ;; frame axioms
      (dotimes (i steps)
        (map nil #'stmt (smt-frame-axioms state-vars concrete-actions i))))
    (values (reverse smt-statements)
            step-ops)))

(defun smt-parse-assignments (assignments)
  (let ((plan))
    (dolist (x assignments)
      (destructuring-bind (var value) x
        (when (eq 'true value)
          (push (unmangle-op (string var)) plan))))
    (sort plan (lambda (a b) (< (car a) (car b))))))

(defun smt-plan (operator-file facts-file
                 &key
                   (steps 1)
                   (max-steps 10))
  (let ((operators (load-operators operator-file))
        (facts (load-facts facts-file)))
    (labels ((rec (steps)
               (multiple-value-bind (assignments is-sat)
                   (multiple-value-bind (stmts vars)
                       (smt-plan-encode operators facts steps)
                     (smt-run stmts vars))
                 (cond
                   (is-sat
                    (smt-parse-assignments assignments))
                   ((< steps max-steps)
                    (rec (1+ steps)))
                   (t nil)))))
    (rec steps))))


(defun smt-plan-automaton (operator-file facts-file)
  ;; 1. Generate Plan
  ;; 2. Identify states with uncontrollable actions
  ;; 3. If uncontrollable effect is outside automata states,
  ;;    recursively solve from effect state back to automaton
  ;;    3.a If no recursive solution, restart with constraint to avoid
  ;;    the uncontrollable precondition state.
  ;; 4. When no deviating uncontrollable effects, return the automaton
)

;; (defun smt-print-exp (sexp &optional (stream *standard-output*))
;;   (etypecase sexp
;;     (null (format stream " () "))
;;     (list
;;      (destructuring-case sexp
;;        ((|not| exp)
;;         (format stream "~&(not")
;;         (smt-print-exp exp)
;;         (princ ")" stream))
;;        ((t &rest ignore)
;;         (declare (ignore ignore))
;;         (format stream "~&(")
;;         (dolist (sexp sexp) (smt-print-exp sexp))
;;         (princ ")" stream))))
;;     (symbol (format stream " ~A " sexp))
;;     (string (format stream " ~A " sexp))))
