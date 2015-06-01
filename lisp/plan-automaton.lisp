(in-package :tmsmt)


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
