(in-package :tmsmt)


;;; ENCODING,
;;;  - PDDL Objects are state variables

(defun collect-args (typed-list type-map)
  (if (null typed-list)
      (list nil)
      (loop
         with type =  (pddl-typed-type (car typed-list))
         for o in (tree-set-list (tree-map-find type-map type))
         nconc
           (loop for args in (collect-args (cdr typed-list) type-map)
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

(defun create-state-variables (predicates type-map)
  "Create all state variables from `PREDICATES' applied to `OBJECTS'"
  (let ((vars))
    (dolist (p predicates)
      ;; apply p to all valid arguments
      (dolist (args (collect-args (pddl-predicate-arguments p)
                                  type-map))
        (push (cons (pddl-predicate-name p) args)
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
     collect (cons (pddl-typed-name d) a)))

(defun smt-concrete-actions (actions type-map)
  (let ((result))
    (dolist (action actions)
      (dolist (args (collect-args (pddl-action-parameters action)
                                  type-map))
        (let ((arg-alist (exp-args-alist (pddl-action-parameters action)
                                         args)))
          (push (make-concrete-action
                 :name (pddl-action-name action)
                 :actual-arguments args
                 :precondition (sublis arg-alist (pddl-action-precondition action))
                 :effect (sublis arg-alist (pddl-action-effect action)))
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
  (let ((hash (make-hash-table :test #'equal))  ;; hash: variable => (list modifiying-operators)
        (empty-set (make-tree-set #'gsymbol-compare)))
    ;; note modified variables
    (dolist (op concrete-actions)
      (let ((fmt-op (format-concrete-action op i)))
        (dolist (v (concrete-action-modified-variables op))
          (setf (gethash v hash)
                (tree-set-insert (gethash v hash empty-set)
                                 fmt-op)))))
    ;; collect axioms
    (apply #'smt-and
           (loop for var in state-vars
              for var-i = (format-state-variable var i)
              for var-j = (format-state-variable var j)
              for eq = (smt-= var-i var-j)
              for actions = (tree-set-list (gethash var hash empty-set))
              collect
                (if actions
                    (smt-or eq (apply #'smt-or actions))
                    eq)))))

(defun smt-frame-axioms (state-vars concrete-actions step)
  (smt-assert (smt-frame-axioms-exp state-vars concrete-actions step (1+ step))))


(defun smt-plan-var-step (state-vars i)
  (loop for s in state-vars
     collect (rewrite-exp s i)))

(defun smt-plan-op-step (concrete-actions i)
  (loop for op in concrete-actions
     collect (format-concrete-action op i)))

(defun smt-plan-step-fun-args (state-vars concrete-actions i j)
  (let ((vars-i (smt-plan-var-step state-vars i))
        (vars-j (smt-plan-var-step state-vars j))
        (op-i (smt-plan-op-step concrete-actions i)))
    (append op-i vars-i vars-j)))

(defun smt-plan-step-fun (state-vars concrete-actions)
  "Generate the per-step assertion for a planning problem"
  (labels ((bool-args (list)
             (loop for x in list
                collect (list x 'bool)))
           (bool-fun (name args exp)
             (smt-define-fun name
                             (bool-args args)
                             'bool
                             exp)))
    (let* ((op-i (smt-plan-op-step concrete-actions 'i))
           (op-vars (smt-plan-step-fun-args state-vars concrete-actions 'i 'j)))
      (append
       (list (smt-comment "Operator Function")
             (smt-define-fun "op-step"
                             ;; args
                             (bool-args op-vars)
                             'bool
                             ;; exp
                             (apply #'smt-and
                                    (loop
                                       for op in concrete-actions
                                       for op-var in op-i
                                       collect
                                         (let ((pre (rewrite-exp (concrete-action-precondition op) 'i))
                                               (eff (rewrite-exp (concrete-action-effect op) 'j)))
                                           `(or (not ,op-var)      ; action not active
                                                (and ,pre          ; precondition holds
                                                     ,eff)))))))
       (let ((ops (loop for i from 0 below (length concrete-actions)
                     collect (format nil "o~D" i ))))
         (list (smt-comment "Exclusion Function")
               (bool-fun "exclude-1" ops
                               `(=> ,(car ops)
                                    (and ,@(loop for b in (cdr ops)
                                              collect (list 'not b)))))
               (bool-fun "exclude-step" ops
                         `(and ,@(loop for op-a in ops
                                    collect `("exclude-1" ,op-a ,@(remove op-a ops)))))))
       (list (smt-comment "Frame Axioms")
             (bool-fun "frame-axioms" op-vars
                       (smt-frame-axioms-exp state-vars concrete-actions 'i 'j)))
       (list (smt-comment "plan-step")
             (bool-fun "plan-step" op-vars
                       (smt-and (cons "exclude-step" op-i)
                                (cons "op-step" op-vars)
                                (cons "frame-axioms" op-vars))))))))

(defun smt-plan-step-vars (state-vars i)
  (loop for s in state-vars
     for v = (format-state-variable s i)
     collect (smt-declare-fun v () 'bool)))

(defun smt-plan-step-stmts (state-vars concrete-actions i)
  (append
   ;; create the per-step state
   (list (smt-comment "State Variables" ))
   (smt-plan-step-vars state-vars (1+ i))

   ;; per-step action variables
   (list (smt-comment "Action Variables"))
   (loop for op in concrete-actions
      for v = (format-concrete-action op i)
      collect (smt-declare-fun v () 'bool))
   (list (smt-comment (format nil "Step ~D" i))
         (smt-assert `("plan-step"
                       ,@(smt-plan-step-fun-args state-vars concrete-actions i (1+ i)))))))

(defun smt-plan-step-ops (concrete-actions steps)
  (let ((step-ops))
    (dotimes (i steps)
      (dolist (op concrete-actions)
        (let ((v (format-concrete-action op i)))
          (push v step-ops))))
    step-ops))

(defun smt-plan-encode (state-vars concrete-actions
                        initial-state
                        goal
                        steps)
  (let ((smt-statements nil))
    (labels ((stmt (x) (push x smt-statements)))
      ;; Per-step function
      (map nil #'stmt (smt-plan-step-fun state-vars concrete-actions))

      ;; initial state
      (stmt (smt-comment "Initial State"))
      (map nil #'stmt (smt-plan-step-vars state-vars 0))
      (stmt (smt-assert (rewrite-exp initial-state 0)))

      ;; Steps
      (dotimes (i steps)
        (map nil #'stmt (smt-plan-step-stmts state-vars concrete-actions i)))

      ;; goal state
      (stmt (smt-comment "Goal State"))
      (stmt (smt-assert (rewrite-exp goal steps))))

    (values (reverse smt-statements)
            (smt-plan-step-ops concrete-actions steps))))

(defun smt-plan-parse (assignments)
  (let ((plan))
    (dolist (x assignments)
      (destructuring-bind (var value) x
        ;; TODO: non-boolean variables
        (ecase value
          ((true |true|)
           (push (unmangle-op (string var)) plan))
          ((false |false|)))))
    (map 'list #'cdr (sort plan (lambda (a b) (< (car a) (car b)))))))

(defun smt-plan-batch ( &key
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
         (type-map (compute-type-map (pddl-operators-types operators)
                                     (pddl-facts-objects facts)))
         (state-vars (or state-vars
                         (create-state-variables (pddl-operators-predicates operators)
                                                 type-map)))
         (concrete-actions (or concrete-actions
                               (smt-concrete-actions (pddl-operators-actions operators)
                                                      type-map)))
         (initial-true (unless initial-state (or initial-true (pddl-facts-init facts))))
         (initial-false (unless initial-state (or initial-false
                                                  (set-difference  state-vars initial-true :test #'equal))))
         (initial-state (or initial-state
                            `(and ,@initial-true
                                  ,@(loop for v in initial-false collect `(not ,v)))))

         (goal (or goal (pddl-facts-goal facts)))
         (n-op (length concrete-actions))
         (n-var (length state-vars)))
    (format t "~&ground actions: ~D" n-op)
    (format t "~&ground states: ~D" n-var)
    (labels ((rec (steps)
               (format t "~&Trying for ~D steps (~D vars)"
                       steps
                       (+ (* steps n-op)
                          (* (1+ steps) n-var)))
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

(defstruct smt-plan-context
  smt
  ground-variables
  ground-actions
  goal
  step
  values
  )

(defun smt-plan-check (cx &key max-steps)
  "Check if a plan exists for the current step, recurse if not."
  (let* ((i (smt-plan-context-step cx))
         (smt (smt-plan-context-smt cx))
         (is-sat (smt-eval smt '(|check-sat|))))
    (print is-sat)
    (case is-sat
      ((sat |sat|)
       (setf (smt-plan-context-values cx)
             (smt-plan-result cx))
       (smt-plan-parse (smt-plan-context-values cx)))
      ((unsat |unsat|)
       (setf (smt-plan-context-values cx) nil)
       ;; pop
       (smt-eval smt '(|pop| 1))
       (when (< (1+ i) max-steps)
         (incf (smt-plan-context-step cx))
         (smt-plan-step cx :max-steps max-steps)))
      (otherwise
       (error "Unrecognized (check-sat) result: ~A" is-sat)))))

(defun smt-plan-step (cx &key
                           (max-steps 10))
  "Try to find a plan at the next step, recursively."
  (let ((i (smt-plan-context-step cx))
        (smt (smt-plan-context-smt cx)))
    (labels ((stmt (exp)
               (smt-eval smt exp))
             (stmt-list (list)
               (map nil #'stmt list)))
      (format t "~&trying step ~D" i)
      ;; step declarations
      (stmt-list (smt-plan-step-stmts (smt-plan-context-ground-variables cx)
                                      (smt-plan-context-ground-actions cx)
                                      i))
      ;; namespace
      (stmt '(|push| 1))
      ;; goal assertion
      (stmt (smt-assert (rewrite-exp (smt-plan-context-goal cx)
                                     (1+ i))))
      ;; check-sat
      (smt-plan-check cx :max-steps max-steps))))

(defun smt-plan-other (cx &key (max-steps 10))
  "Try to find an alternate plan, recursively."
  (let ((values (smt-plan-result cx)))
    ;; Invalidate the current plan
    ;; TODO: maybe we just need the true actions?
    (let ((exp (smt-not (apply #'smt-and
                               (loop for (variable truth) in values
                                  collect (ecase truth
                                            ((true |true|)
                                             variable)
                                            ((false |false|)
                                             (smt-not variable))))))))
      (smt-eval (smt-plan-context-smt cx)
                (smt-assert exp)))
    ;; Get another plan
    (smt-plan-check cx :max-steps max-steps)))

(defun smt-plan-next (cx &key (max-steps 10))
  "Find the next valid plan."
  (if (smt-plan-context-values cx)
      (smt-plan-other cx :max-steps max-steps)
      (smt-plan-step cx :max-steps max-steps)))

(defun smt-plan-result (cx)
  "Retrive action variable assignments from SMT solver."
  (let* ((i (smt-plan-context-step cx))
         (step-ops (smt-plan-step-ops (smt-plan-context-ground-actions cx)
                                      (1+ i))))
    (smt-eval (smt-plan-context-smt cx)
              `(|get-value| ,step-ops))))


(defun smt-plan-context ( &key
                            operators facts
                            state-vars
                            concrete-actions
                            initial-true
                            initial-false
                            initial-state
                            goal
                            smt)
  "Fork an SMT solver and initialize with base plan definitions."
  (let* ((operators (when operators
                      (load-operators operators)))
         (facts (when facts (load-facts facts)))
         (type-map (compute-type-map (pddl-operators-types operators)
                                     (pddl-facts-objects facts)))
         (state-vars (or state-vars
                         (create-state-variables (pddl-operators-predicates operators)
                                                 type-map)))
         (concrete-actions (or concrete-actions
                               (smt-concrete-actions (pddl-operators-actions operators)
                                                      type-map)))
         (initial-true (unless initial-state (or initial-true (pddl-facts-init facts))))
         (initial-false (unless initial-state (or initial-false
                                                  (set-difference  state-vars initial-true :test #'equal))))
         (initial-state (or initial-state
                            `(and ,@initial-true
                                  ,@(loop for v in initial-false collect `(not ,v)))))

         (goal (or goal (pddl-facts-goal facts)))
         (n-op (length concrete-actions))
         (n-var (length state-vars)))
    (format t "~&ground actions: ~D" n-op)
    (format t "~&ground states: ~D" n-var)
    (let ((smt (or smt (smt-start))))
      (labels ((stmt (exp)
                 ;(print (list 'eval exp))
                 (smt-eval smt exp))
               (stmt-list (list)
                 (map nil #'stmt list)))
        ;; Per-step function
        (stmt-list (smt-plan-step-fun state-vars concrete-actions))
        ;; initial state
        (stmt-list (smt-plan-step-vars state-vars 0))
        (stmt (smt-assert (rewrite-exp initial-state 0))))

      (make-smt-plan-context :smt smt
                             :ground-variables state-vars
                             :ground-actions concrete-actions
                             :goal goal
                             :step 0))))




(defun smt-plan ( &key
                    operators facts
                    state-vars
                    concrete-actions
                    initial-true
                    initial-false
                    initial-state
                    goal
                    (max-steps 10))
  (let* ((operators (when operators
                      (load-operators operators)))
         (facts (when facts (load-facts facts)))
         (type-map (compute-type-map (pddl-operators-types operators)
                                     (pddl-facts-objects facts)))
         (state-vars (or state-vars
                         (create-state-variables (pddl-operators-predicates operators)
                                                 type-map)))
         (concrete-actions (or concrete-actions
                               (smt-concrete-actions (pddl-operators-actions operators)
                                                      type-map)))
         (initial-true (unless initial-state (or initial-true (pddl-facts-init facts))))
         (initial-false (unless initial-state (or initial-false
                                                  (set-difference  state-vars initial-true :test #'equal))))
         (initial-state (or initial-state
                            `(and ,@initial-true
                                  ,@(loop for v in initial-false collect `(not ,v)))))

         (goal (or goal (pddl-facts-goal facts)))
         (n-op (length concrete-actions))
         (n-var (length state-vars)))
    (format t "~&ground actions: ~D" n-op)
    (format t "~&ground states: ~D" n-var)
    (let ((smt (smt-start)))
      (labels ((stmt (exp)
                 ;(print (list 'eval exp))
                 (smt-eval smt exp))
               (stmt-list (list)
                 (map nil #'stmt list))
               (plan-step (i)
                 (format t "~&trying step ~D" i)
                 ;; step declarations
                 (stmt-list (smt-plan-step-stmts state-vars concrete-actions i))
                 ;; namespace
                 (stmt '(|push| 1))
                 ;; goal assertion
                 (stmt (smt-assert (rewrite-exp goal (1+ i))))
                 ;; check-sat
                 (let ((is-sat (smt-eval smt '(|check-sat|))))
                   (print is-sat)
                   (case is-sat
                     (sat
                      (result i))
                     (unsat
                      ;; pop
                      (stmt '(|pop| 1))
                      (when (< (1+ i) max-steps)
                        (plan-step (1+ i))))
                     (otherwise
                      (error "Unrecognized (check-sat) result: ~A" is-sat)))))
               (result (i)
                 (let* ((step-ops (smt-plan-step-ops concrete-actions (1+ i)))
                        (values (stmt `(|get-value| ,step-ops)))
                        (plan (smt-plan-parse values)))
                   plan)))
        ;; Per-step function
        (stmt-list (smt-plan-step-fun state-vars concrete-actions))
        ;; initial state
        (stmt-list (smt-plan-step-vars state-vars 0))
        (stmt (smt-assert (rewrite-exp initial-state 0)))
        (prog1 (plan-step 0)
          (smt-stop smt))))))



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
         (state-vars (create-state-variables (pddl-operators-predicates operators)
                                              (pddl-facts-objects facts)))
         (controllable-actions (loop for a in (pddl-operators-actions operators)
                                   unless (pddl-action-uncontrollable a) collect a))
         (uncontrollable-actions (loop for a in (pddl-operators-actions operators)
                                     when (pddl-action-uncontrollable a) collect a))
         (concrete-controllable (smt-concrete-actions controllable-actions (pddl-facts-objects facts)))
         (concrete-uncontrollable (smt-concrete-actions uncontrollable-actions (pddl-facts-objects facts)))
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
      (let ((start (concrete-state-create (pddl-facts-init facts)
                                          (set-difference state-vars (pddl-facts-init facts) :test #'equal)
                                          state-vars)))
        (multiple-value-bind (states edges)
            (rec-plan (make-tree-set #'concrete-state-compare)
                      nil
                      start
                      (pddl-facts-goal facts))
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
