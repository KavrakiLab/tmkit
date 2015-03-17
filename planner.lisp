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
  (smt-mangle-list `(,@predicate ,step)))

(defun format-op (op args step)
  (smt-mangle-list `(,op ,@args ,step)))

(defun unmangle-op (mangled)
  (let ((list (smt-unmangle mangled)))
    (cons (lastcar list)
          (loop for x on list
             for a = (car x)
             when (cdr x)
             collect
             a))))

(defun create-state-variables (predicates objects)
  "Create all state variables from `PREDICATES' applied to `OBJECTS'"
  (let ((vars))
    (dolist (p predicates)
      ;; apply p to all valid arguments
      (dolist (args (collect-args objects (predicate-arity p)))
        (push (cons (predicate-name p) args)
              vars)))
    vars))

(defstruct concrete-action
  name
  actual-arguments
  precondition
  effect)

(defstruct concrete-state
  (bits (make-array 0 :element-type 'bit))
  exp)

(defun concrete-state-compare (a b)
  (let* ((a-bits (concrete-state-bits a))
         (b-bits (concrete-state-bits b))
         (n-a (length a-bits))
         (n-b (length b-bits)))
    (assert (= n-a n-b))
    (bit-vector-compare a-bits b-bits)))

(defun concrete-state-decode (state state-vars)
  (let ((bits (concrete-state-bits state)))
    (loop
       for b across bits
       for v in state-vars
       unless (zerop b)
       collect (list v
                     (if (zerop b) 'false 'true)))))

(defun state-vars-index (state-vars var)
  "Return the index of `VAR' in `STATE-VARS'."
  (let ((i (position var state-vars :test #'equal)))
    (assert i)
    i))

(defun state-vars-ref (state-vars i)
  (nth i state-vars))

(defun state-vars-size (state-vars)
  (length state-vars))

(defun concrete-state-create (true-bits false-bits state-vars)
  (let ((bits (make-array (state-vars-size state-vars) :element-type 'bit)))
    (dolist (var true-bits)
      (setf (aref bits (state-vars-index state-vars var))
            1))
    (dolist (var false-bits)
      (setf (aref bits (state-vars-index state-vars var))
            0))
    (make-concrete-state :bits bits
                         :exp `(and ,@true-bits
                                    ,@(loop for var in false-bits
                                         collect `(not ,var))))))

(defun concrete-state-translate-exp (exp state-vars)
  "Return a lambda expression that evaluates `EXP'."
  (with-gensyms (state bits)
    `(lambda (,state)
       (let ((,bits (concrete-state-bits ,state)))
         ,(apply-rewrite-exp (lambda (v)
                               `(not (zerop (aref ,bits ,(state-vars-index state-vars v )))))
                             exp)))))

(defun concrete-state-compile-exp (exp state-vars)
  "Return a compiled lambda expression that evaluates `EXP'."
  (compile nil
           (concrete-state-translate-exp exp state-vars)))

(defun destructure-concrete-effect (thing)
  "Returns the effect as (values state-variable (or t nil))"
  (etypecase thing
      (atom (values thing t))
      (cons
       (destructuring-case thing
         (((and or) &rest args)
          (declare (ignore args))
          (error "Can't destructure ~A" thing))
         ((not x)
          (multiple-value-bind (state-variable sign) (destructure-concrete-effect x)
            (values state-variable (not sign))))
         ((t &rest x)
          (declare (ignore x))
          (values thing t))))))

(defun concrete-state-translate-effect (effect state-vars)
  "Return a lambda expression that creates a new state with `EFFECT' set."
  (with-gensyms (state bits new-bits)
    `(lambda (,state)
       (let* ((,bits (concrete-state-bits ,state))
              (,new-bits (make-array ,(state-vars-size state-vars) :element-type 'bit
                                     :initial-contents ,bits)))
         ,@(destructuring-bind (-and &rest things) effect
             (check-symbol -and 'and)
             (loop for exp in things
                collect
                  (multiple-value-bind (var sign)
                      (destructure-concrete-effect exp)
                    `(setf (aref ,new-bits ,(state-vars-index state-vars var))
                           ,(if sign 1 0)))))
         (make-concrete-state :bits ,new-bits
                              ;; TODO: this could be better
                              :exp (list 'and
                                         ,@(loop
                                              for i below (state-vars-size state-vars)
                                              for v = (state-vars-ref state-vars i)
                                              collect `(if (zerop (aref ,new-bits ,i))
                                                           (list 'not ',v)
                                                           ',v))))))))

(defun concrete-state-compile-effect (effect state-vars)
  "Return a compiled lambda expression that creates a new state with `EFFECT' set."
  (compile nil
           (concrete-state-translate-effect effect state-vars)))


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

(defun smt-concrete-actions (actions objects)
  (let ((result))
    (dolist (action actions)
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

(defun smt-frame-axioms-exp (state-vars concrete-actions i j)
  ;(print concrete-operators)
  (let ((hash (make-hash-table :test #'equal))) ;; hash: variable => (list modifiying-operators)
    ;; note modified variables
    (dolist (op concrete-actions)
      (dolist (v (concrete-action-modified-variables op))
        (push op (gethash v hash))))
    ;; collect axioms

    ;(loop for var in state-vars
       ;do (print (gethash var hash)))
    (apply #'smt-and
           (loop for var in state-vars
              collect
                (smt-or (list '=
                              (format-state-variable var i)
                              (format-state-variable var j))
                        (apply #'smt-or
                               (loop for op in (gethash var hash)
                                  collect (format-concrete-action op i))))))))

(defun smt-frame-axioms (state-vars concrete-actions step)
  (smt-assert (smt-frame-axioms-exp state-vars concrete-actions step (1+ step))))


(defun smt-plan-encode (state-vars concrete-actions
                        initial-state
                        goal
                        steps)
  (let* ((smt-statements nil)
         (step-ops))
    (labels ((stmt (x)
               (push x smt-statements))
             (declare-step (x)
               (stmt (smt-declare-fun  x () 'bool)))
             (bool-args (list)
               (loop for x in list
                    collect (list x 'bool)))
             (bool-fun (name args exp)
               (smt-define-fun name
                              (bool-args args)
                              'bool
                              exp))
             (state-var-step (i)
               (loop for s in state-vars
                  collect (rewrite-exp s i)))
             (op-step (i)
               (loop for op in concrete-actions
                  collect (format-concrete-action op i))))

      ;; per-step state variables
      ;; create the per-step state
      (stmt (smt-comment "State Variables"))
      (dotimes (i (1+ steps))
        (dolist (v state-vars)
          (declare-step (format-state-variable v i))))

      ;; per-step action variables
      (stmt (smt-comment "Action Variables"))
      (dotimes (i steps)
        (dolist (op concrete-actions)
          (let ((v (format-concrete-action op i)))
            (push v step-ops)
            (declare-step v ))))

      ;; initial state
      (stmt (smt-comment "Initial State"))
      (stmt (smt-assert (rewrite-exp initial-state 0)))

      ;; operator encodings
      (stmt (smt-comment "Operator Function"))
      (stmt (bool-fun "op-step"
                      ;; args
                      (append (op-step 'i)
                              (state-var-step 'i)
                              (state-var-step 'j))

                      ;; exp
                      (apply #'smt-and
                             (loop for op-var in (op-step 'i)
                                for op in concrete-actions
                                collect
                                  (let ((pre (rewrite-exp (concrete-action-precondition op) 'i))
                                        (eff (rewrite-exp (concrete-action-effect op) 'j)))
                                    `(or (not ,op-var)      ; action not active
                                         (and ,pre          ; precondition holds
                                              ,eff)))))))    ; effect holds

      ;; exclusion axioms
      (stmt (smt-comment "Exclusion Function"))
      (let ((ops (loop for i from 0 below (length concrete-actions)
                    collect (format nil "o~D" i ))))
        (stmt (bool-fun "exclude-1" ops
                        `(=> ,(car ops)
                             (and ,@(loop for b in (cdr ops)
                                       collect (list 'not b))))))
        (stmt (bool-fun "exclude-step" ops
                        `(and ,@(loop for op-a in ops
                                   collect `("exclude-1" ,op-a ,@(remove op-a ops)))))))

      ;; frame axioms
      (stmt (smt-comment "Frame Axioms"))
      (stmt (bool-fun "frame-axioms" (append (op-step 'i)
                                             (state-var-step 'i)
                                             (state-var-step 'j))
                      (smt-frame-axioms-exp state-vars concrete-actions 'i 'j)))

      ;; Steps
      (dotimes (i steps)
        (stmt (smt-comment (format nil "Step ~D" i)))
        (let* ((ops (op-step i))
               (state-i (state-var-step i))
               (state-j (state-var-step (1+ i)))
               (args (append ops state-i state-j)))
          (stmt (smt-assert `("exclude-step" ,@ops)))
          (stmt (smt-assert (cons "op-step" args)))
          (stmt (smt-assert (cons "frame-axioms" args)))))

      ;; goal state
      (stmt (smt-comment "Goal State"))
      (stmt (smt-assert (rewrite-exp goal steps))))

    (values (reverse smt-statements)
            step-ops)))

(defun smt-plan-parse (assignments)
  (let ((plan))
    (dolist (x assignments)
      (destructuring-bind (var value) x
        (when (eq 'true value)
          (push (unmangle-op (string var)) plan))))
    (map 'list #'cdr (sort plan (lambda (a b) (< (car a) (car b)))))))

(defun smt-plan ( &key
                    operators facts
                    state-vars
                    concrete-actions
                    initial-true
                    initial-false
                    initial-state
                    goal
                    (steps 1)
                    (max-steps 10))
  (let* ((operators (when operators
                      (load-operators operators)))
         (facts (when facts (load-facts facts)))
         (state-vars (or state-vars
                         (create-state-variables (operators-predicates operators)
                                                 (facts-objects facts))))
         (concrete-actions (or concrete-actions
                               (smt-concrete-actions (operators-actions operators)
                                                      (facts-objects facts))))
         (initial-true (unless initial-state (or initial-true (facts-init facts))))
         (initial-false (unless initial-state (or initial-false
                                                  (set-difference  state-vars initial-true :test #'equal))))
         (initial-state (or initial-state
                            `(and ,@initial-true
                                  ,@(loop for v in initial-false collect `(not ,v)))))

         (goal (or goal (facts-goal facts))))
    (format t "~&ground actions: ~D" (length concrete-actions))
    (format t "~&ground states: ~D" (length state-vars))
    ;; ))

    (labels ((rec (steps)
               (format t "~&Trying for ~D steps" steps)
               (multiple-value-bind (assignments is-sat)
                   (multiple-value-bind (stmts vars)
                       (smt-plan-encode state-vars concrete-actions
                                        initial-state
                                        goal
                                        steps)
                     (smt-run stmts vars))
                     (cond
                       (is-sat
                        (smt-plan-parse assignments))
                       ((< steps max-steps)
                        (rec (1+ steps)))
                       (t nil)))))
      (rec steps))))


(defun plan-automaton (&key operators facts)
  ;; 1. Generate Plan
  ;; 2. Identify states with uncontrollable actions
  ;; 3. If uncontrollable effect is outside automata states,
  ;;    recursively solve from effect state back to automaton
  ;;    3.a If no recursive solution, restart with constraint to avoid
  ;;    the uncontrollable precondition state.
  ;; 4. When no deviating uncontrollable effects, return the automaton
  (let* ((operators (load-operators operators))
         (facts (load-facts facts))
         (state-vars (create-state-variables (operators-predicates operators)
                                              (facts-objects facts)))
         (controllable-actions (loop for a in (operators-actions operators)
                                   unless (action-uncontrollable a) collect a))
         (uncontrollable-actions (loop for a in (operators-actions operators)
                                     when (action-uncontrollable a) collect a))
         (concrete-controllable (smt-concrete-actions controllable-actions (facts-objects facts)))
         (concrete-uncontrollable (smt-concrete-actions uncontrollable-actions (facts-objects facts)))
         (uncontrollable-preconditions
          (loop for a in concrete-uncontrollable
             collect (concrete-state-compile-exp (concrete-action-precondition a)
                                                 state-vars)))
         (uncontrollable-effects
          (loop for a in concrete-uncontrollable
             collect (concrete-state-compile-effect (concrete-action-effect a)
                                                    state-vars)))
         (controllable-effects-hash (fold (lambda (hash action)
                                            (let ((key (cons (string (concrete-action-name action))
                                                             (map 'list #'string
                                                                  (concrete-action-actual-arguments action)))))
                                              (setf (gethash key hash)
                                                    (concrete-state-compile-effect (concrete-action-effect action)
                                                                                   state-vars))
                                              hash))
                                          (make-hash-table :test #'equal)
                                          concrete-controllable)))
    (labels ((controllable-effect (state action)
               ;; find the successor concrete state
               (funcall (gethash action controllable-effects-hash)
                        state))
             (plan-states (start plan)
               ;; collect list of concrete states in the plan
               (cons start
                     (loop for a in plan
                        for s = (controllable-effect start a) then (controllable-effect s a)
                        collect s)))
             (add-edge (edges s0 a s1)
               (cons (list s0 a s1) edges))
             (merge-plan (states edges plan-actions plan-states)
               ;; add concrete states and edges to the plan automaton
               (assert (not (tree-set-member-p states (car plan-states))))
               (setq states (tree-set-insert states (car plan-states)))
               (loop
                  for a in plan-actions
                  for rest-states on plan-states
                  for s0 = (first rest-states)
                  for s1 = (second rest-states)
                  do (setq states (tree-set-insert states s1)
                           edges (add-edge edges s0 a s1)))
               (values states edges))
             (fix-plan (states edges plan-states)
               ;; TODO: recursively fix the plan
               (dolist (s0 plan-states)
                 (loop
                    for u-pre in uncontrollable-preconditions
                    for u-eff in uncontrollable-effects
                    for u-a in concrete-uncontrollable
                    when (funcall u-pre s0)
                    do
                      (let ((s1 (funcall u-eff s0)))
                        (setq edges (add-edge edges
                                              s0
                                              (cons (concrete-action-name u-a)
                                                    (concrete-action-actual-arguments u-a))
                                              s1))
                        (unless (tree-set-member-p states s1)
                          (multiple-value-setq (states edges)
                            (rec-plan states edges s1))))))
               (values states edges))
             (rec-plan (states edges start &optional goal)
               (let* ((goal-exp (or goal
                                    (cons 'or
                                          (map-tree-set 'list #'concrete-state-exp states))))
                      (start-exp (concrete-state-exp start))
                      (plan-actions (smt-plan :state-vars state-vars :concrete-actions concrete-controllable
                                              :initial-state start-exp :goal goal-exp))
                      (plan-states (plan-states start plan-actions)))
                 (multiple-value-bind (states edges)
                     (merge-plan states edges plan-actions plan-states)
                   (fix-plan states edges plan-states)))))
      (let ((start (concrete-state-create (facts-init facts)
                                          (set-difference state-vars (facts-init facts) :test #'equal)
                                          state-vars)))
        (multiple-value-bind (states edges)
            (rec-plan (make-tree-set #'concrete-state-compare)
                      nil
                      start
                      (facts-goal facts))
          ;; TODO: collect accept states
          (values states edges start nil)))
    )))

(defun plan-automata-dot (edges start goal)
  (let ((edge-list (map 'list (lambda (e) (list (concrete-state-exp (first e))
                                                (second e)
                                                (concrete-state-exp (third e))))
                                 edges))
        (start-exp  (concrete-state-exp start)))
    (mg::fa-dot (mg:make-fa edge-list start-exp goal) :output "/tmp/dot.pdf" :rankdir "TB" )))

;; (defun smt-print-exp (sexp &optional (stream *standard-output*))
;;   (etypecase sexp
;;     (null (format stream " () "))
;;     (list
;;      (destructuring-case sexp
;;        ((|not| exp) ;;         (format stream "~&(not")
;;         (smt-print-exp exp)
;;         (princ ")" stream))
;;        ((t &rest ignore)
;;         (declare (ignore ignore))
;;         (format stream "~&(")
;;         (dolist (sexp sexp) (smt-print-exp sexp))
;;         (princ ")" stream))))
;;     (symbol (format stream " ~A " sexp))
;;     (string (format stream " ~A " sexp))))
