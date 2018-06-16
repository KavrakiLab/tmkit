(in-package :tmsmt)


;;; Constraint-based Planning Definition Language (CPDL)
;;;
;;; (declare-enum NAME ELEMENTS...)
;;; (declare-fluent NAME TYPE)
;;; (start (= FLUENT VALUE))
;;; (start FLUENT)
;;; (start (not FLUENT))
;;; (goal EXPRESSION)
;;; (transition EXPRESSION)
;;; (now FLUENT)
;;; (next FLUENT)
;;; (output FLUENT)

(defun fluent-now (fluent)
  (list 'now fluent))

(defun fluent-next (fluent)
  (list 'next fluent))

(defun exp-now (exp)
  (apply-rewrite-exp #'fluent-now exp))

(defun exp-next (exp)
  (apply-rewrite-exp #'fluent-next exp))


(defun cpdl-error (fmt &rest args)
  (apply #'error fmt args))


(defstruct fluent-descriptor
  name
  type
  now
  next)

(defstruct constrained-domain
  "Planning domain for constraint-based planning."

  ;; map from names to canonical name
  (canon (make-hash-table :test #'equal))

  ;; ;; map from fluent to types
  (fluent-map (make-hash-table :test #'eq))

  ;; list of fluents to output
  outputs

  ;; list of clauses in transition function (implicit and)
  transition-clauses

  ;; map of initial state
  (start-map (make-hash-table :test #'equal))

  ;; list of clauses in goal set (implicit and)
  goal-clauses

  ;; Caches
  (mangle-cache (make-hash-table :test #'equal))
  (unmangle-cache (make-hash-table :test #'equal)))

;(defun cpd-fluent-name (cpd fluent)


(defun cpd-canonize-fluent (cpd fluent
                            ;; &key
                                 ;;   (if-exists :supersede)
                                 ;;   (if-does-not-exist :create)
                                 )
  (let ((h (constrained-domain-canon cpd)))
    (multiple-value-bind (v exists) (gethash fluent h)
      (if exists v
          (if (atom fluent)
              (let ((list (list fluent)))
                (setf (gethash fluent h) list
                      (gethash list h) list))
              (setf (gethash fluent h) fluent))))))


(defun cpd-fluent-descriptor (cpd fluent)
  (if-let ((d (gethash (cpd-canonize-fluent cpd fluent)
                       (constrained-domain-fluent-map cpd))))
    d
    (cpdl-error "Fluent not declared: ~A" fluent)))

(defun cpd-fluent-now (cpd fluent)
  (fluent-descriptor-now (cpd-fluent-descriptor cpd fluent)))

(defun cpd-fluent-next (cpd fluent)
  (fluent-descriptor-next (cpd-fluent-descriptor cpd fluent)))

(defun cpd-fluent-type (cpd fluent)
  (fluent-descriptor-type (cpd-fluent-descriptor cpd fluent)))

;; (defun cpd-exp-now (domain exp)
;;   (flet ((fun (fluent)
;;            (cpd-fluent-now domain fluent)))
;;     (declare (dynamic-extent #'fun))
;;     (apply-rewrite-exp #'fun exp)))

;; (defun cpd-exp-next (domain exp)
;;   (flet ((fun (fluent)
;;            (cpd-fluent-next domain fluent)))
;;     (declare (dynamic-extent #'fun))
;;     (apply-rewrite-exp #'fun exp)))


(defun cpd-canonize-exp (cpd exp)
  ;; TODO: check
  (labels ((canonize (exp)
             (cpd-canonize-fluent cpd exp))
           (destructure (exp)
             (etypecase exp
               (atom (canonize exp))
               (cons
                (destructuring-case exp
                  ((now exp)
                   (cpd-fluent-now cpd exp))
                  ((next exp)
                   (cpd-fluent-next cpd exp))
                  ((t &rest args)
                   (declare (ignore args))
                   (canonize exp)))))))
    (apply-rewrite-exp #'destructure exp)))


(defun check-cpdl-fluent (cpd fluent &optional (exists t))
  (let* ((fluent (cpd-canonize-fluent cpd fluent))
         (actually-exists
          (hash-table-contains fluent (constrained-domain-fluent-map cpd))))
    (if exists
        (unless actually-exists
          (cpdl-error "Fluent not declared: ~A" fluent))
        (when actually-exists
          (cpdl-error "Fluent already declared: ~A" fluent)))))


(defun cpdl-declare-fluent (cpd name type)
  (let ((name (cpd-canonize-fluent cpd name))
        (h (constrained-domain-fluent-map cpd)))
      (if (hash-table-contains name h)
          (cpdl-error "Fluent already declared: ~A" name)
          (setf (gethash name (constrained-domain-fluent-map cpd))
                (make-fluent-descriptor :name name
                                        :type type
                                        :now (fluent-now name)
                                        :next (fluent-next name))))))

(defun eval-cpdl (cpd stmt)
  (destructuring-ecase stmt
    ((declare-fluent name  &optional (type 'bool))
     (cpdl-declare-fluent cpd name type))
    ((start thing)
     (flet ((add-start (fluent value)
              (let ((fluent (ensure-list fluent)))
                (check-cpdl-fluent cpd fluent t)
                (let ((hash (constrained-domain-start-map cpd)))
                  (when (hash-table-contains fluent hash)
                    (cpdl-error "Start value already declared: ~A" fluent))
                  (setf (gethash fluent hash) value)))))
       (if (consp thing)
           (destructuring-case thing
             ((not fluent)
              (add-start fluent 'false))
             ((= fluent exp)
              (add-start fluent exp))
             ((t &rest rest)
              (declare (ignore rest))
              (add-start thing 'true)))
           (add-start thing 'true))))
    ((goal clause)
     ;; TODO: check exp
     (push (cpd-canonize-exp cpd clause)
           (constrained-domain-goal-clauses cpd)))

    ((transition clause)
     ;; TODO: check exp
     (push (cpd-canonize-exp cpd clause)
           (constrained-domain-transition-clauses cpd)))

    ((output fluent)
     (let ((fluent (cpd-canonize-fluent cpd fluent)))
       (check-cpdl-fluent cpd fluent t)
       (push fluent (constrained-domain-outputs cpd)))))
  ;; Result
  cpd)

(defun parse-cpdl (stmts &optional (domain (make-constrained-domain)))
  (fold #'eval-cpdl domain stmts))


(defun map-cpd-fluents (result-type function cpd)
  (map-hash-result result-type
                   function
                   (constrained-domain-fluent-map cpd)))

(defun map-cpd-fluent-types (result-type function cpd)
  (map-cpd-fluents result-type
                   (lambda (name descriptor)
                     (funcall function name (fluent-descriptor-type descriptor)))
                   cpd))


(defun map-cpd-transitions (result-type function cpd)
  (map result-type
       function
       (constrained-domain-transition-clauses cpd)))

(defun map-cpd-start (result-type function cpd)
  (map-hash-result result-type
                   function
                   (constrained-domain-start-map cpd)))

(defun map-cpd-goals (result-type function cpd)
  (map result-type
       function
       (constrained-domain-goal-clauses cpd)))


(defun cpd-stmts (cpd)
  (nconc
   ;; fluents
   (map-cpd-fluent-types 'list
                         (lambda (name type)
                           `(declare-fluent ,name ,type))
                         cpd)
   ;; transition
   (map-cpd-transitions 'list
                        (lambda (c)
                          `(transition ,c))
                        cpd)

   ;; start
   (map-cpd-start 'list
                  (lambda (name value)
                    (case value
                      (true `(start ,name))
                      (false `(start (not ,name)))
                      (otherwise `(start (= ,name ,value)))))
                  cpd)
   ;; goal
   (map-cpd-goals 'list
                  (lambda (c) `(goal ,c))
                  cpd)))
