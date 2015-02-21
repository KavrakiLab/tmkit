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


;;; ENCODING,
;;;  - PDDL Objects are state variables

(defun collect-args (objects arity)
  (if (zerop arity)
      (list nil)
      (loop for o in objects
         nconc
           (loop for args in (collect-args objects (1- arity))
              collect (cons o args)))))


(defun format-exp (predicate step)
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


  ;; (format nil "~A_~{~A~^_~}_~D" op args step))

(defun rewrite-exp (exp step)
  (destructuring-case exp
    ((and &rest rest)
     `(and ,@(map 'list (lambda (e) (rewrite-exp e step)) rest)))
    ((or &rest rest)
     `(or ,@(map 'list (lambda (e) (rewrite-exp e step)) rest)))
    ((not &rest rest)
     `(not ,@(map 'list (lambda (e) (rewrite-exp e step)) rest)))
    ((t &rest rest) (declare (ignore rest))
     (format-state-variable exp step))))

(defun create-state-variables (predicates objects)
  (loop for p in predicates
     append
       (loop for args in (collect-args objects (predicate-arity p))
          collect (cons (predicate-name p) args))))

(defun smt-subst (stmts)
  "Replace upcased CL symbols with properly-cased SMT-Lib symbols"
  (sublis '((or     .  |or|)
            (not    .  |not|)
            (assert .  |assert|)
            (bool   .  |Bool|)
            (and    .  |and|))
          stmts))

(defun smt-print (stmts &optional (stream *standard-output*))
  ;; Use the lisp printer to pretty print the expressions, then fixup
  ;; the output with some regular expressions
  (let* ((cl-string (with-output-to-string (s)
                      (dolist (e (smt-subst stmts))
                        (print e s))))
         ;; eat CL case quotes
         (smt-string-0 (ppcre:regex-replace-all "\\|([\\w\\-]+)\\|"
                                                cl-string
                                                "\\1"))
         ;; eat string quotes
         (smt-string-1 (ppcre:regex-replace-all "\"([\\w\\-]+)\""
                                                smt-string-0
                                                "\\1"))
         ;; replace NILs with ()
         (smt-string-2 (ppcre:regex-replace-all "([\\s\\(\\)])NIL([\\s\\(\\)])"
                                                smt-string-1
                                                "\\1()\\2")))
    (princ smt-string-2 stream))
  nil)



(defun smt-assert (x)
  (list '|assert| x))

(defun smt-declare-fun (name args type)
  (list '|declare-fun| name args type))

(defun smt-not (x)
  (list 'not x))

(defun smt-or (&rest args)
  (cons 'or args))

(defun smt-and (&rest args)
  (cons 'and args))

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



(defun smt-concrete-operators (operators objects)
  (let ((result))
    (dolist (operator (operators-actions operators))
      (dolist (args (collect-args objects
                                  (length (action-parameters operator))))
        (let ((arg-alist (exp-args-alist (action-parameters operator)
                                         args)))
          (push (make-concrete-action
                 :name (action-name operator)
                 :actual-arguments args
                 :precondition (sublis arg-alist (action-precondition operator))
                 :effect (sublis arg-alist (action-effect operator)))
                result))))
    result))

;;(defun smt-encode-all-operators (operators step objects)
  ;;(let ((arg-set (collect-args objects (length (action-parameters operator)))))
  ;; collect operator instanciations
  ;; operator application axioms
  ;; exclusion axioms
  ;; frame axioms

(defun concrete-action-modifies-varable-p (operator variable)
  (let ((not-variable (list 'not variable)))
    (destructuring-bind (-and &rest things) (concrete-action-effect operator)
      (check-symbol -and 'and)
      (labels ((rec (rest)
                 (when rest
                   (let ((x (first rest)))
                     (if (or (equal x variable)
                             (equal x not-variable))
                         t
                         (rec (cdr rest)))))))
        (rec things)))))

(defun concrete-action-modified-variables (operator)
  (destructuring-bind (-and &rest things) (concrete-action-effect operator)
    (check-symbol -and 'and)
    (loop for exp in things
       collect
         (destructuring-case exp
           ((not x) x)
           ((t &rest rest) (declare (ignore rest))
            exp)))))

(defun smt-frame-axioms (state-vars concrete-operators step)
  ;(print concrete-operators)
  (let ((hash (make-hash-table :test #'equal))) ;; hash: variable => (list modifiying-operators)
    ;; note modified variables
    (dolist (op concrete-operators)
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



(defun smt-plan (operator-file fact-file steps)
  (let* ((operators (load-operators operator-file))
         (facts (load-facts fact-file))
         (smt-statements nil)
         (state-vars (create-state-variables (operators-predicates operators)
                                             (facts-objects facts)))
         (concrete-operators (smt-concrete-operators operators  (facts-objects facts)))
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
        (dolist (op concrete-operators)
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
        (dolist (op concrete-operators)
          (stmt (smt-assert `(or (not ,(format-op (concrete-action-name op)
                                                  (concrete-action-actual-arguments op)
                                                  i))
                                 (and ,(rewrite-exp (concrete-action-precondition op) i)
                                      ,(rewrite-exp (concrete-action-effect op) (1+ i))))))))


      ;; exclusion axioms
      (dotimes (i steps)
        (dolist (op concrete-operators)
          (stmt (smt-assert `(=> ,(format-op (concrete-action-name op)
                                             (concrete-action-actual-arguments op)
                                             i)
                                 (and ,@(loop for other-op in concrete-operators
                                           unless (eq op other-op)
                                           collect `(not ,(format-op (concrete-action-name other-op)
                                                                     (concrete-action-actual-arguments other-op)
                                                                     i)))))))))
      ;; frame axioms
      (dotimes (i steps)
        (map nil #'stmt (smt-frame-axioms state-vars concrete-operators i)))

      ;; control statements
      (stmt '(|check-sat|))
      (stmt (list '|get-value| step-ops)))
    (reverse smt-statements)))

(defun smt-output (file operator-file fact-file steps)
  (with-open-file (s file :direction :output :if-exists :supersede)
    (smt-print (smt-plan operator-file fact-file steps) s)))


(defun smt-parse-assignments (assignments)
  (let ((plan))
    (dolist (x assignments)
      (destructuring-bind (var value) x
        (when (eq 'true value)
          (push (unmangle-op (string var)) plan))))
    (sort plan (lambda (a b) (< (car a) (car b))))))

(defun smt-input (file)
  (multiple-value-bind (is-sat assignments)
      (with-open-file (s file :direction :input)
        (values (read s)
                (read s)))
    ;(print is-sat)
    (when (eq 'sat is-sat)
      (smt-parse-assignments assignments))))

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
