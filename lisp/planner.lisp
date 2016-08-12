(in-package :tmsmt)

;; TODO: encode datatype name into datatype values
;;       needed to allow complex type inheritance
;;
;; Ground domain expressions should carry around the type of each term
;; so that the appropriate constant symbol can be selected in SMT
;; expressions.  (smells like overloading)

(defvar *operators*)

(defvar *facts*)

(defun plan-enum-symbol (type name)
  (declare (ignore type))
  name)

;;; ENCODING,
;;;  - PDDL Objects are state variables

(defun collect-args (typed-list type-map)
  (if (null typed-list)
      (list nil)
      (loop
         with type =  (pddl-typed-type (car typed-list))
         with objects = (tree-map-find type-map type)
         with list = (when objects (tree-set-list objects))
         for o in list
         nconc
           (loop for args in (collect-args (cdr typed-list) type-map)
              unless (position o args) ;; no duplicate args
              collect (cons o args)))))


;; TODO: should we assume that atomic predicates are constants?
;; TODO: refactor smtlib mangling

(defun format-state-variable (predicate step)
  (if (consp predicate)
      (smt-mangle-list `(,@predicate ,step))
      predicate))

(defun mangle-var (thing &key args step)
  (let ((base (append (ensure-list thing)
                      args)))
    (if step
        (smt-mangle-list (append base (list step)))
        (smt-mangle-list base))))

(defun unmangle-op (mangled)
  (let ((list (smt-unmangle mangled)))
    (cons (lastcar list)
          (loop for x on list
             for a = (car x)
             when (cdr x)
             collect
             a))))


(defun create-state-variables (functions type-objects)
  "Create all state variables from `PREDICATES' applied to `OBJECTS'"
  (fold (lambda (map f)
          (fold (lambda (map args)
                  (tree-map-insert map
                                   (cons (pddl-function-name f) args)
                                   (pddl-function-type f)))
                map
                (collect-args (pddl-function-arguments f)
                              type-objects)))
        (make-tree-map #'gsymbol-compare)
        functions))



  ;; (let ((variable-type (make-hash-table :test #'equal)))
  ;;   (dolist (f functions)
  ;;     ;; apply p to all valid arguments
  ;;     (dolist (args (collect-args (pddl-function-arguments f)
  ;;                                 type-objects))
  ;;       (let ((var (cons (pddl-function-name f) args)))
  ;;         (setf (gethash var variable-type) (pddl-function-type f)))))
  ;;   variable-type))

(defun ground-derived-body (derived actual-args type-map)
  (labels ((arg-alist (dummies actuals)
             (loop for act in actuals
                for dummy in dummies
                collect (cons (pddl-typed-name dummy)
                              act)))
             (rec (e alist)
               (etypecase e
                 (pddl-quantifier
                  (let ((fun (ecase (pddl-quantifier-head e)
                               (tmsmt/pddl::exists 'or)
                               (tmsmt/pddl::forall 'and))))
                    `(,fun
                      ,@(loop for a in (collect-args (pddl-quantifier-parameters e)
                                                     type-map)
                           for sub-alist = (append (arg-alist (pddl-quantifier-parameters e)
                                                              a)
                                                   alist)
                           collect (rec (pddl-quantifier-body e) sub-alist)))))
                 (symbol
                  (assoc-value-default e alist :test #'eq :default e))
                 (cons
                  (map 'list (lambda (e) (rec e alist)) e)))))
      (rec (pddl-derived-body derived)
           (arg-alist (pddl-derived-arguments derived)
                      actual-args))))

(defun ground-derived (type-objects derived)
  (let ((variable-type (make-hash-table :test #'equal))
        (variable-body (make-hash-table :test #'equal)))
    (dolist (d derived)
      ;; apply p to all valid arguments
      (dolist (args (collect-args (pddl-function-arguments d)
                                  type-objects))
        (let ((var (cons (pddl-function-name d) args)))
          ;(print (list var args (pddl-derived-body d)))
          (setf (gethash var variable-type) (pddl-function-type d)
                (gethash var variable-body) (ground-derived-body d args type-objects)))))
    (values (hash-table-tree-map variable-type #'gsymbol-compare)
            (loop for k being the hash-keys in variable-body
                 collect `(= ,k ,(gethash k variable-body))))))

(defstruct ground-action
  name
  actual-arguments
  precondition
  effect)


(defun format-ground-action (op step)
  (mangle-var (ground-action-name op)
              :args (ground-action-actual-arguments op)
              :step step))


(defun smt-plan-action-exp (action i action-encoding)
  (ecase action-encoding
    (:boolean (format-ground-action action i))
    (:enum (smt-= (mangle-var 'action :step i)
                  (mangle-var (ground-action-name action)
                              :args (ground-action-actual-arguments action))))))

(defun exp-args-alist (dummy-args actual-args)
  "Find alist for argument replacement"
  (assert (= (length dummy-args) (length actual-args)))
  (loop
     for d in dummy-args
     for a in actual-args
     collect (cons (pddl-typed-name d) a)))

(defun smt-ground-actions (actions type-map)
  (let ((result))
    (dolist (action actions)
      (dolist (args (collect-args (pddl-action-parameters action)
                                  type-map))
        (let ((arg-alist (exp-args-alist (pddl-action-parameters action)
                                         args)))
          (push (make-ground-action
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

(defun ground-action-modifies-varable-p (action variable)
  (let ((not-variable (list 'not variable)))
    (destructuring-bind (-and &rest things) (ground-action-effect action)
      (check-symbol -and 'and)
      (labels ((rec (rest)
                 (when rest
                   (let ((x (first rest)))
                     (if (or (equal x variable)
                             (equal x not-variable))
                         t
                         (rec (cdr rest)))))))
        (rec things)))))

(defun ground-action-modified-variables (action)
  (destructuring-bind (-and &rest things) (ground-action-effect action)
    (check-symbol -and 'and)
    (loop for exp in things
       collect
         (destructuring-case exp
           ((not x) x)
           ((= x y) (if (atom x) y x)) ;; TODO: maybe not general
           ((t &rest rest) (declare (ignore rest))
            exp)))))



(defstruct ground-domain
  (variables nil :type list)
  (types nil :type list)
  (variable-type nil :type tree-map)
  (derived-variables nil :type list)
  (derived-type nil :type tree-map)
  (type-objects nil :type tree-map)
  (operators nil :type list)
  (axioms nil :type list)
  (start nil :type list)
  (goal nil :type list)
  action-encoding)

(defun type-map-keys (map)
  (map-tree-map :inorder 'list (lambda (key value)
                                 (declare (ignore value))
                                 key)
                map))

(defun type-map-types (map)
  (tree-set-list (fold-tree-map (lambda (set key value)
                                  (declare (ignore key))
                                  (tree-set-insert set value))
                                (make-tree-set #'gsymbol-compare)
                                map)))


;; TODO: ground derived types
;;       - add to variables (separate slot for derived variables)
;;       - add axioms indicating state
;;       - need to omit derived variables from frame axioms
(defun ground-domain (operators facts
                      &key
                        (action-encoding :boolean)
                        goal)
  (let* ((operators (load-operators operators))
         (canon (pddl-operators-canon operators))
         (facts (load-facts facts operators))
         (objects (append (pddl-operators-constants operators)
                          (pddl-facts-objects facts)))
         (type-objects (compute-type-map (pddl-operators-types operators)
                                         objects))
         (variable-type (create-state-variables (pddl-operators-functions operators)
                                                type-objects))
         (ground-variables (type-map-keys variable-type))
         (ground-operators (smt-ground-actions (pddl-operators-actions operators)
                                               type-objects))
         (initial-true (pddl-facts-init facts))
         (bool-vars (loop for g in ground-variables
                       when (eq 'bool (tree-map-find variable-type g))
                       collect g))
         (initial-false (set-difference  bool-vars initial-true :test #'equal)))
    (ecase action-encoding
      (:boolean)
      (:enum (push (make-ground-action :name 'no-op
                                       :effect '(and))
                   ground-operators)))
    (multiple-value-bind (derived-type derived-axioms)
        (ground-derived type-objects (pddl-operators-derived operators))
      (make-ground-domain :variables ground-variables
                          :variable-type variable-type
                          :derived-variables (type-map-keys derived-type)
                          :derived-type derived-type
                          :type-objects type-objects
                          :types (type-map-types variable-type)
                          :operators ground-operators
                          :axioms derived-axioms
                          :action-encoding action-encoding
                          :start  `(and ,@initial-true
                                        ,@(loop for v in initial-false collect `(not ,v)))
                          :goal (or goal (pddl-facts-goal facts))))))


(defun smt-frame-axioms-exp (state-vars ground-actions i j action-encoding)
  ;(print ground-operators)
  (let ((hash (make-hash-table :test #'equal))  ;; hash: variable => (list modifiying-operators)
        (empty-set (make-tree-set #'gsymbol-compare)))
    ;; note modified variables
    (dolist (op ground-actions)
      (let ((fmt-op (smt-plan-action-exp op i action-encoding)))
        (dolist (v (ground-action-modified-variables op))
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

(defun smt-frame-axioms (state-vars ground-actions step action-encoding)
  (smt-assert (smt-frame-axioms-exp state-vars ground-actions step (1+ step) action-encoding)))


(defun smt-plan-var-step (state-vars i)
  (loop for s in state-vars
     collect (rewrite-exp s i)))

(defun smt-plan-op-step (ground-actions i)
  (loop for op in ground-actions
     collect (format-ground-action op i)))

(defun smt-plan-step-fun-args (domain i j)
  (let* ((state-vars (ground-domain-variables domain))
         (ground-actions (ground-domain-operators domain))
         (derived (ground-domain-derived-variables domain))
         (vars-i (smt-plan-var-step state-vars i))
         (vars-j (smt-plan-var-step state-vars j))
         (derived-i (smt-plan-var-step derived j))
         (op-i (smt-plan-op-step ground-actions i)))
    (ecase (ground-domain-action-encoding domain)
      (:boolean
       (append op-i vars-i vars-j derived-i))
      (:enum
       (cons (mangle-var 'action :step i)
             (append vars-i vars-j derived-i))))))


(defun smt-plan-var-type (vars map)
  (loop for v in vars collect (tree-map-find map v)))

(defun smt-plan-bool-type (vars)
  (loop for v in vars collect 'bool))

(defun smt-plan-exclude-exp (vars)
  (labels ((fmt (v)
             (smt-mangle "let" v))
           (ite (vars)
             (if (cdr vars)
                 (smt-ite (first vars)
                          (fmt (second vars))
                          (ite (cdr vars)))
                 '|true|)))
    (let ((bindings (loop for x on (cdr vars)
                       collect (list (fmt (first x))
                                     (if (cdr x)
                                         (smt-and (smt-not (first x))
                                                  (fmt (second x)))
                                         (smt-not (first x)))))))
      (smt-let* (reverse bindings)
                (ite vars)))))


(defun smt-plan-datatypes (domain)
  (labels ((tree-set-add-type (set name type)
             (declare (ignore name))
             (tree-set-insert set type)))
    (let* ((object-types (fold-tree-map #'tree-set-add-type (tree-set #'gsymbol-compare)
                                        (ground-domain-variable-type domain)))
           (type-objects (ground-domain-type-objects domain)))
      (fold-tree-set (lambda (list type)
                       (case type
                         ((bool object t) list)
                         (otherwise
                          (cons (smt-declare-enum type
                                                  (map-tree-set 'list (lambda (name)
                                                                        (plan-enum-symbol type name))
                                                                (tree-map-find type-objects type)))
                                 list))))
                     nil
                     object-types))))

(defun smt-plan-step-fun (domain)
  "Generate the per-step assertion for a planning problem"
  (labels ((arg-list (args types)
             (map 'list #'list args types))
           (bool-fun (name args types exp)
             (smt-define-fun name
                             (arg-list args types)
                             'bool
                             exp)))
    (let* ((state-vars (ground-domain-variables domain))
           (ground-actions (ground-domain-operators domain))
           (action-encoding (ground-domain-action-encoding domain))
           (op-i (ecase action-encoding
                   (:boolean (smt-plan-op-step ground-actions 'i))
                   (:enum (list (mangle-var 'action :step 'i)))))
           (op-exps (loop for op in ground-actions
                       collect (smt-plan-action-exp op 'i action-encoding)))
           (op-type (ecase action-encoding
                      (:boolean (smt-plan-bool-type ground-actions))
                      (:enum (list 'actions))))
           (vars-i (smt-plan-var-step state-vars 'i))
           (vars-j (smt-plan-var-step state-vars 'j))
           (var-type (smt-plan-var-type state-vars (ground-domain-variable-type domain)))
           (derived-i (smt-plan-var-step (ground-domain-derived-variables domain) 'i))
           (derived-type (smt-plan-var-type (ground-domain-derived-variables domain)
                                            (ground-domain-derived-type domain)))
           (frame-vars (append op-i vars-i vars-j))
           (frame-vars-type (append op-type var-type var-type))
           (op-vars (append op-i vars-i vars-j derived-i))
           (op-vars-type (append op-type var-type var-type derived-type)))
      ;(print (smt-plan-step-fun-types domain state-vars ground-actions))
      (append
       ;; exclusion
       (ecase (ground-domain-action-encoding domain)
         (:boolean
          (list (smt-comment "Exclusion Function")
                (bool-fun "exclude-step" op-i op-type
                          (smt-plan-exclude-exp op-i))))
         (:enum
          (list (smt-declare-enum 'actions
                                  (loop for a in ground-actions
                                     collect (mangle-var (ground-action-name a)
                                                         :args (ground-action-actual-arguments a)))))))
         ;; Operator
       (list (smt-comment "Operator Function")
             (bool-fun "op-step" op-vars op-vars-type
                       (apply #'smt-and
                              (loop
                                 for op in ground-actions
                                 for op-exp in op-exps
                                 collect
                                   (let ((pre (rewrite-exp (ground-action-precondition op) 'i))
                                         (eff (rewrite-exp (ground-action-effect op) 'j)))
                                     `(or (not ,op-exp)      ; action not active
                                          (and ,(or pre '|true|)         ; precondition holds
                                               ,(if (equal '(and) eff)
                                                    '|true|
                                                    eff))))))))

       ;; early termination
       (list (smt-comment "Early Termination")
             (bool-fun "early-term" (append op-i vars-i) (append op-type var-type)
                       (ecase action-encoding
                         (:boolean (smt-ite
                                    ;; if goal
                                    (rewrite-exp (ground-domain-goal domain) 'i)
                                    ;; then no op
                                    (smt-not (apply #'smt-or op-i))
                                    ;; else op
                                    (apply #'smt-or op-i)))
                         (:enum
                          (smt-ite
                           ;; if goal
                           (rewrite-exp (ground-domain-goal domain) 'i)
                           ;; then no op
                           (smt-= (car op-i) 'no-op)
                           ;; else op
                           (smt-not (smt-= (car op-i) 'no-op)))))))
       ;; frame
       (list (smt-comment "Frame Axioms")
             (bool-fun "frame-axioms" frame-vars frame-vars-type
                       (smt-frame-axioms-exp state-vars ground-actions 'i 'j
                                             (ground-domain-action-encoding domain))))


       ;; Step
       (list (smt-comment "plan-step")
             (bool-fun "plan-step" op-vars op-vars-type
                       (apply #'smt-and
                              (append
                               (ecase (ground-domain-action-encoding domain)
                                 (:boolean
                                  (list (cons "exclude-step" op-i)))
                                 (:enum nil))
                               (list (cons "early-term" (append op-i vars-i)))
                               (list (cons "op-step" op-vars))
                               (list (cons "frame-axioms" frame-vars))
                               ;; direct axioms
                               (loop for axiom in (ground-domain-axioms domain)
                                  collect (rewrite-exp axiom 'i))))))))))

(defun smt-plan-step-vars (domain i)
  (labels ((helper (vars types)
             (loop
                for s in vars
                for v = (format-state-variable s i)
                collect (multiple-value-bind (type contains)
                            (tree-map-find types s)
                          (assert contains)
                          (smt-declare-fun v () type)))))
    (append (helper (ground-domain-variables domain)
                    (ground-domain-variable-type domain))
            (helper (ground-domain-derived-variables domain)
                    (ground-domain-derived-type domain)))))

(defun smt-plan-step-stmts (domain i)
  (let ((ground-actions (ground-domain-operators domain))
        (action-encoding (ground-domain-action-encoding domain)))
    (append
     ;; create the per-step state
     (list (smt-comment "State Variables" ))
     (smt-plan-step-vars domain (1+ i))

     ;; per-step action variables
     (list (smt-comment "Action Variables"))

     (ecase action-encoding
       (:boolean (loop for op in ground-actions
                    for v = (format-ground-action op i)
                    collect (smt-declare-fun v () 'bool)))
       (:enum
        (list (smt-declare-fun (mangle-var 'action :step i) ()
                               'actions))))
     (list (smt-comment (format nil "Step ~D" i))
           (smt-assert `("plan-step"
                         ,@(smt-plan-step-fun-args domain
                                                   i (1+ i))))))))

(defun smt-plan-step-ops (domain steps)
  (let* ((ground-actions (ground-domain-operators domain))
         (action-encoding (ground-domain-action-encoding domain))
         (step-ops))
    (ecase action-encoding
      (:boolean
       (dotimes (i steps)
         (dolist (op ground-actions)
           (let ((v (format-ground-action op i)))
             (push v step-ops)))))
      (:enum
       (dotimes (i steps)
         (push (mangle-var 'action :step i)
               step-ops))))
    step-ops))

(defun smt-plan-items (action-encoding assignments)
  (let ((plan))
    (dolist (x assignments)
      (destructuring-bind (var value) x
        ;; TODO: non-boolean variables
        (ecase action-encoding
          (:boolean (ecase value
                      ((true |true|)
                       (push (unmangle-op (string var)) plan))
                      ((false |false|))))
          (:enum (let ((x (smt-unmangle (string var)))
                       (y (smt-unmangle (string value))))
                   (push (cons (lastcar x)
                               y)
                         plan))))))
    plan))

(defun smt-plan-parse (action-encoding assignments)
  (map 'list #'cdr (sort (smt-plan-items action-encoding assignments)
                         (lambda (a b) (< (car a) (car b))))))



(defstruct smt-plan-context
  smt
  domain
  step
  values)

(defun smt-plan-context-ground-variables (instance)
  (ground-domain-variables (smt-plan-context-domain instance)))
(defun smt-plan-context-ground-actions (instance)
  (ground-domain-operators (smt-plan-context-domain instance)))
(defun smt-plan-context-goal (instance)
  (ground-domain-goal (smt-plan-context-domain instance)))
(defun smt-plan-context-action-encoding (instance)
  (ground-domain-action-encoding (smt-plan-context-domain instance)))

(defun smt-plan-check (cx &key max-steps)
  "Check if a plan exists for the current step, recurse if not."
  (let* ((i (smt-plan-context-step cx))
         (smt (smt-plan-context-smt cx))
         (old-time (smt-runtime smt))
         (is-sat (smt-eval smt '(|check-sat|)))
         (new-time (smt-runtime smt)))
    (format t "~&~S (~Fs)~%" is-sat (let ((r 1d-4)) (* (round (- new-time old-time) r)
                                                   r)))
    (case is-sat
      ((sat |sat|)
       (setf (smt-plan-context-values cx)
             (smt-plan-result cx))
       ;(print (smt-plan-context-values cx))
       (smt-plan-parse (ground-domain-action-encoding (smt-plan-context-domain cx))
                       (smt-plan-context-values cx)))
      ((unsat |unsat|)
       ;(print (smt-eval smt '(|get-unsat-core|)))
       (setf (smt-plan-context-values cx) nil)
       ;; pop
       (smt-eval smt '(|pop| 1))
       (when (< (1+ i) max-steps)
         (incf (smt-plan-context-step cx))
         (smt-plan-step cx :max-steps max-steps)))
      (otherwise
       (error "Unrecognized (check-sat) result: ~S" is-sat)))))

(defun smt-plan-step (cx &key
                           (max-steps 10))
  "Try to find a plan at the next step, recursively."
  (let ((domain (smt-plan-context-domain cx))
        (i (smt-plan-context-step cx))
        (smt (smt-plan-context-smt cx)))
    (labels ((stmt (exp)
               (smt-eval smt exp))
             (stmt-list (list)
               (map nil #'stmt list)))
      (format t "~&trying step ~D~%" i)
      ;; step declarations
      (stmt-list (smt-plan-step-stmts domain i))
      ;; namespace
      (stmt '(|push| 1))
      ;; goal assertion
      (stmt (smt-assert (rewrite-exp (smt-plan-context-goal cx)
                                     (1+ i))))
      ;; check-sat
      (smt-plan-check cx :max-steps max-steps))))

(defun smt-plan-other (cx &key (max-steps 10))
  "Try to find an alternate plan, recursively."
  ;; (let ((values (smt-plan-context-values cx)))
  ;;   ;; Invalidate the current plan
  ;;   ;; TODO: maybe we just need the true actions?
  ;;   (let ((exp (smt-not (apply #'smt-and
  ;;                              (loop for (variable truth) in values
  ;;                                 collect (ecase truth
  ;;                                           ((true |true|)
  ;;                                            variable)
  ;;                                           ((false |false|)
  ;;                                            (smt-not variable))))))))
  ;;     ;; TODO: don't need this assertion when invalidating operators
  ;;     (smt-eval (smt-plan-context-smt cx)
  ;;               (smt-assert exp))))

  ;; Get another plan
  (smt-plan-check cx :max-steps max-steps))

(defun smt-plan-next (cx &key (max-steps 10))
  "Find the next valid plan."
  (if (smt-plan-context-values cx)
      (smt-plan-other cx :max-steps max-steps)
      (smt-plan-step cx :max-steps max-steps)))

(defun smt-plan-result (cx)
  "Retrive action variable assignments from SMT solver."
  (let* ((i (smt-plan-context-step cx))
         (step-ops (smt-plan-step-ops (smt-plan-context-domain cx)
                                      (1+ i))))
    (smt-eval (smt-plan-context-smt cx)
              `(|get-value| ,step-ops))))


(defun smt-plan-invalidate-op (cx state op)
  (let* ((action-encoding (smt-plan-context-action-encoding cx))
         (stmts (loop for i to (smt-plan-context-step cx)
                   collect
                     (smt-implies (apply #'smt-and
                                         (loop for s in state
                                            collect (rewrite-exp s i)))
                                  (smt-not (ecase action-encoding
                                             (:boolean (mangle-var op :step i))
                                             (:enum (smt-= (mangle-var 'action :step i)
                                                               (mangle-var op))))))))
         (e (apply #'smt-and stmts)))
    (smt-eval (smt-plan-context-smt cx)
              (smt-assert e))))

    ;; (dotimes (i (smt-plan-context-step cx))
    ;; (format t "~&state: ~A" state)
    ;; (format t "~&op: ~A" op)
    ;; (format t "~&step: ~A" step)))

(defun smt-plan-invalidate-plan (cx action-encoding)
  (let* ((operators (smt-plan-items action-encoding
                                    (smt-plan-context-values cx)))
         (exp
          (ecase action-encoding
            (:boolean
             (loop for op in operators
                collect (mangle-var (cdr op) :step (car op))))
            (:enum
             (loop for op in operators
                collect (smt-= (mangle-var 'action :step (car op))
                               (mangle-var (cdr op))))))))
      (smt-eval (smt-plan-context-smt cx)
                   (smt-assert (smt-not (apply #'smt-and exp))))))



(defun smt-plan-context (&key
                           operators
                           facts
                           domain
                           goal
                           smt
                           (action-encoding :boolean))
  "Fork an SMT solver and initialize with base plan definitions."
  (let* ((domain (or domain (ground-domain operators
                                           facts
                                           :action-encoding action-encoding
                                           :goal goal)))
         (state-vars (ground-domain-variables domain))
         (ground-actions (ground-domain-operators domain))
         (initial-state (ground-domain-start domain))
         (n-op (length ground-actions))
         (n-var (length state-vars)))
    (format t "~&ground actions: ~D" n-op)
    (format t "~&ground states: ~D" n-var)
    (let ((smt (or smt (smt-start))))
      (labels ((stmt (exp)
                 ;(print (list 'eval exp))
                 (smt-eval smt exp))
               (stmt-list (list)
                 (map nil #'stmt list)))
        ;; Datatypes
        (stmt-list (smt-plan-datatypes domain))
        ;; Per-step function
        (stmt-list (smt-plan-step-fun domain))
        ;; initial state
        (stmt-list (smt-plan-step-vars domain 0))
        (stmt (smt-assert (rewrite-exp initial-state 0))))

      (make-smt-plan-context :smt smt
                             :domain domain
                             :step 0))))

(defun smt-plan (operators facts &key
                                   (max-steps 5)
                                   (action-encoding :boolean))
  (with-smt (smt)
    (let ((cx (smt-plan-context :operators operators
                                :facts facts
                                :smt smt
                                :action-encoding action-encoding)))
      (smt-plan-next cx :max-steps max-steps))))


;; (defun smt-plan-single ( &key
;;                     operators facts
;;                     state-vars
;;                     ground-actions
;;                     initial-true
;;                     initial-false
;;                     initial-state
;;                     goal
;;                     (max-steps 10))
;;   (let* ((operators (when operators
;;                       (load-operators operators)))
;;          (facts (when facts (load-facts facts)))
;;          (type-map (compute-type-map (pddl-operators-types operators)
;;                                      (pddl-facts-objects facts)))
;;          (state-vars (or state-vars
;;                          (create-state-variables (pddl-operators-predicates operators)
;;                                                  type-map)))
;;          (ground-actions (or ground-actions
;;                                (smt-ground-actions (pddl-operators-actions operators)
;;                                                       type-map)))
;;          (initial-true (unless initial-state (or initial-true (pddl-facts-init facts))))
;;          (initial-false (unless initial-state (or initial-false
;;                                                   (set-difference  state-vars initial-true :test #'equal))))
;;          (initial-state (or initial-state
;;                             `(and ,@initial-true
;;                                   ,@(loop for v in initial-false collect `(not ,v)))))

;;          (goal (or goal (pddl-facts-goal facts)))
;;          (n-op (length ground-actions))
;;          (n-var (length state-vars)))
;;     (format t "~&ground actions: ~D" n-op)
;;     (format t "~&ground states: ~D" n-var)
;;     (let ((smt (smt-start)))
;;       (labels ((stmt (exp)
;;                  ;(print (list 'eval exp))
;;                  (smt-eval smt exp))
;;                (stmt-list (list)
;;                  (map nil #'stmt list))
;;                (plan-step (i)
;;                  (format t "~&trying step ~D" i)
;;                  ;; step declarations
;;                  (stmt-list (smt-plan-step-stmts state-vars ground-actions i))
;;                  ;; namespace
;;                  (stmt '(|push| 1))
;;                  ;; goal assertion
;;                  (stmt (smt-assert (rewrite-exp goal (1+ i))))
;;                  ;; check-sat
;;                  (let ((is-sat (smt-eval smt '(|check-sat|))))
;;                    (print is-sat)
;;                    (case is-sat
;;                      (sat
;;                       (result i))
;;                      (unsat
;;                       ;; pop
;;                       (stmt '(|pop| 1))
;;                       (when (< (1+ i) max-steps)
;;                         (plan-step (1+ i))))
;;                      (otherwise
;;                       (error "Unrecognized (check-sat) result: ~A" is-sat)))))
;;                (result (i)
;;                  (let* ((step-ops (smt-plan-step-ops ground-actions (1+ i)))
;;                         (values (stmt `(|get-value| ,step-ops)))
;;                         (plan (smt-plan-parse values)))
;;                    plan)))
;;         ;; Per-step function
;;         (stmt-list (smt-plan-step-fun state-vars ground-actions))
;;         ;; initial state
;;         (stmt-list (smt-plan-step-vars state-vars 0))
;;         (stmt (smt-assert (rewrite-exp initial-state 0)))
;;         (prog1 (plan-step 0)
;;           (smt-stop smt))))))

;; (defun smt-plan-encode (state-vars ground-actions
;;                         initial-state
;;                         goal
;;                         steps)
;;   (let ((smt-statements nil))
;;     (labels ((stmt (x) (push x smt-statements)))
;;       ;; Per-step function
;;       (map nil #'stmt (smt-plan-step-fun state-vars ground-actions))

;;       ;; initial state
;;       (stmt (smt-comment "Initial State"))
;;       (map nil #'stmt (smt-plan-step-vars state-vars 0))
;;       (stmt (smt-assert (rewrite-exp initial-state 0)))

;;       ;; Steps
;;       (dotimes (i steps)
;;         (map nil #'stmt (smt-plan-step-stmts state-vars ground-actions i)))

;;       ;; goal state
;;       (stmt (smt-comment "Goal State"))
;;       (stmt (smt-assert (rewrite-exp goal steps))))

;;     (values (reverse smt-statements)
;;             (smt-plan-step-ops ground-actions steps))))

;; (defun smt-plan-batch ( &key
;;                           operators facts
;;                           state-vars
;;                           ground-actions
;;                           initial-true
;;                           initial-false
;;                           initial-state
;;                           goal
;;                           (steps 1)
;;                           (max-steps 10))
;;   (let* ((operators (when operators
;;                       (load-operators operators)))
;;          (facts (when facts (load-facts facts)))
;;          (type-map (compute-type-map (pddl-operators-types operators)
;;                                      (pddl-facts-objects facts)))
;;          (state-vars (or state-vars
;;                          (create-state-variables (pddl-operators-predicates operators)
;;                                                  type-map)))
;;          (ground-actions (or ground-actions
;;                                (smt-ground-actions (pddl-operators-actions operators)
;;                                                       type-map)))
;;          (initial-true (unless initial-state (or initial-true (pddl-facts-init facts))))
;;          (initial-false (unless initial-state (or initial-false
;;                                                   (set-difference  state-vars initial-true :test #'equal))))
;;          (initial-state (or initial-state
;;                             `(and ,@initial-true
;;                                   ,@(loop for v in initial-false collect `(not ,v)))))

;;          (goal (or goal (pddl-facts-goal facts)))
;;          (n-op (length ground-actions))
;;          (n-var (length state-vars)))
;;     (format t "~&ground actions: ~D" n-op)
;;     (format t "~&ground states: ~D" n-var)
;;     (labels ((rec (steps)
;;                (format t "~&Trying for ~D steps (~D vars)"
;;                        steps
;;                        (+ (* steps n-op)
;;                           (* (1+ steps) n-var)))
;;                (multiple-value-bind (assignments is-sat)
;;                    (multiple-value-bind (stmts vars)
;;                        (smt-plan-encode state-vars ground-actions
;;                                         initial-state
;;                                         goal
;;                                         steps)
;;                      (smt-run stmts vars))
;;                      (cond
;;                        (is-sat
;;                         (smt-plan-parse assignments))
;;                        ((< steps max-steps)
;;                         (rec (1+ steps)))
;;                        (t nil)))))
;;       (rec steps))))





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
