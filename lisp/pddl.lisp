(in-package :tmsmt)

(defparameter *pddl-package* (find-package :tmsmt))

;; TODO: handle keywords better
(defparameter *pddl-canonical-map*
  (fold (lambda (map symbol)
          (fold (lambda (map key)
                  (tree-map-insert map key symbol))
                map
                (list symbol
                      (string-upcase (string symbol))
                      (string-downcase (string symbol)))))
        (make-tree-map #'gsymbol-compare)
        '(= and or object define :domain -)))

(defstruct pddl-action
  "A PDDL action"
  name
  parameters
  precondition
  uncontrollable
  effect
  )

(defstruct pddl-typed
  "A PDDL type"
  name
  type
  )

;; (defstruct pddl-predicate
;;   "A PDDL predicate"
;;   name
;;   arity
;;   arguments)

(defstruct pddl-operators
  "A PDDL set of operators"
  name
  types
  (canon *pddl-canonical-map*)
  supertypes
  constants
  functions
  derived
  actions)


(defstruct (pddl-function (:include pddl-typed))
  arguments)

(defun pddl-operators-supertype (operators type)
  "Return the supertype of type as defined in operators"
  (multiple-value-bind (supertype exists)
      (gethash type (pddl-operators-supertypes operators))
    (unless exists
      (error "Type ~A not found" type))
    supertype))

(defstruct pddl-facts
  "A PDDL set of facts"
  name
  domain
  objects
  type-map
  init
  goal)

;; TYPE QUERIES
;; Given: argument type, objects and type
;; Find:  set of objects that match the argument

(defun load-operators (operators)
  "Load operators from `operators'."
  (etypecase operators
    (pddl-operators operators)
    (cons (parse-operators operators))
    ((or rope pathname) (parse-operators (load-sexp operators *pddl-package*)))))

(defun load-facts (facts &optional domain)
  "Load facts from `facts'."
  (etypecase facts
    (pddl-facts facts)
    (cons (parse-facts facts domain))
    ((or rope pathname) (parse-facts (load-sexp facts *pddl-package*) domain))))

(defun parse-typed-list (type-list)
  (labels ((collect-names (type-list)
             "(values names type rest-of-list)"
             (cond
               ((null type-list)
                (values nil t nil))
               ((eq (car type-list) '-)
                (destructuring-bind (dash type &rest rest) type-list
                  (assert (eq '- dash))
                  (values nil type rest)))
               (t
                (multiple-value-bind (names type rest-of-list)
                    (collect-names (cdr type-list))
                  (values (cons (car type-list) names)
                          type
                          rest-of-list)))))
           (rec (type-list)
             (when type-list
               (multiple-value-bind (names type type-list)
                   (collect-names type-list)
                 (append (loop for name in names
                            collect (make-pddl-typed :name name :type type))
                         (rec type-list))))))
    (rec type-list)))

(defun compute-type-map (types objects)
  "Find hash-table mapping type to all objects of that type (directly or subtype)"
  (let ((type-map (make-tree-map #'gsymbol-compare))
        (empty-set (make-tree-set #'gsymbol-compare)))
    ;; Add bool
    (tree-map-insertf type-map 'bool
                      (tree-set #'gsymbol-compare nil t))
    ;; Add each object to its direct type and t (the top-level type)
    (let ((t-set empty-set))
      (loop for x in objects
         for object-name = (pddl-typed-name x)
         for object-type = (pddl-typed-type x)
         for d-set = (tree-map-find type-map object-type empty-set)
         do
           (setq type-map (tree-map-insert type-map object-type
                                           (tree-set-insert d-set object-name))
                 t-set (tree-set-insert t-set object-name)))
      (setq type-map (tree-map-insert type-map t t-set)))
    ;; Add subtypes sets to their supertype set
    ;; continue until reaching the fixpoint
    (fixpoint (lambda (type-map)
                (fold (lambda (type-map typedef)
                        (let* ((type (pddl-typed-name typedef))
                               (supertype (pddl-typed-type typedef))
                               (type-set (tree-map-find type-map type empty-set))
                               (supertype-set (tree-map-find type-map supertype  empty-set)))
                          (if (tree-set-subset-p type-set supertype-set)
                              type-map
                              (tree-map-insert type-map supertype
                                               (tree-set-union type-set supertype-set)))))
                      type-map types))
              type-map #'eq)))

(defun parse-predicate (sexp)
  (destructuring-bind (name &rest arg-list) sexp
    (let ((type-list (parse-typed-list arg-list)))
      (make-pddl-function :name name
                          :type 'bool
                          :arguments type-list))))

(defun parse-pddl-functions (sexp)
  (let ((typed (parse-typed-list sexp)))
    (loop for x in typed
       for function = (pddl-typed-name x)
       collect (make-pddl-function :name (car function)
                                   :arguments (parse-typed-list (cdr function))
                                   :type (pddl-typed-type x)))))

(defstruct (pddl-derived (:include pddl-function))
  body)

(defstruct pddl-quantifier
  head
  parameters
  body)

(defun parse-pddl-exp (exp)
  ;; TODO: recurse
  (etypecase exp
    (atom exp)
    (list
     (destructuring-case exp
       (((exists forall) arglist body)
        (make-pddl-quantifier :head (car exp)
                              :parameters (parse-typed-list arglist)
                              :body body))
       (((or and not =) &rest rest)
        (cons (car exp)
              (map 'list #'parse-pddl-exp rest)))
       ((t &rest rest)
        (declare (ignore rest))
        exp)))))


(defun parse-operators (sexp)
  (destructuring-bind (-define (-domain name) &rest clauses)
      sexp
    (check-symbol -define :define)
    (check-symbol -domain :domain)
    (let* ((ops (make-pddl-operators :name name)))
      (dolist (clause clauses)
        (destructuring-ecase clause
          ((:requirements &rest ignore)
           ;; TODO: handle this
           (declare (ignore ignore)))
          ((:predicates &rest predicates)
           (loop for p in predicates do
                (push (parse-predicate p)
                      (pddl-operators-functions ops))))
          ((:action name &key parameters uncontrollable precondition effect)
           (push (make-pddl-action :name name
                              :parameters (parse-typed-list  parameters)
                              :uncontrollable uncontrollable
                              :precondition precondition
                              :effect effect)
                 (pddl-operators-actions ops)))
          ((:functions &rest sexp)
           (setf (pddl-operators-functions ops)
                 (append (pddl-operators-functions ops)
                         (parse-pddl-functions sexp))))
          ((:derived predicate body)
           (let ((fun (parse-predicate predicate)))
             (push (make-pddl-derived :name (pddl-function-name fun)
                                      :type (pddl-function-type fun)
                                      :arguments (pddl-function-arguments fun)
                                      :body (parse-pddl-exp body))
                   (pddl-operators-derived ops))))
          ((:constants &rest objs)
           (setf (pddl-operators-constants ops)
                 (parse-typed-list objs)))
          ((:types &rest type-list)
           (let ((typed-list (parse-typed-list type-list))
                 (hash (make-hash-table :test #'equal)))
             (setf (pddl-operators-types ops) typed-list
                   (pddl-operators-supertypes ops) hash)
             ;; add types
             (dolist (x typed-list)
               (let ((type (pddl-typed-name x))
                     (supertype (pddl-typed-type x)))
                 (when (hash-table-contains type hash)
                   (error "Duplicate type ~A" type))
                 ;; set supertype
                 (setf (gethash type  hash) supertype)
                 ;; note canonicalize type symbol
                 (tree-map-insertf (pddl-operators-canon ops) type type)
                 (tree-map-insertf (pddl-operators-canon ops) (string type) type)))
             ;; check super-types
             ;; if not explicitly given, create as subtype of t
             (dolist (x typed-list)
               (let ((supertype (pddl-typed-type x)))
                 (unless (hash-table-contains supertype hash)
                   (setf (gethash supertype hash) t))))))))
      ops)))

(defun parse-facts (sexp &optional domain)
  (destructuring-bind (-define (-problem name) &rest clauses)
      (if domain
          (canonize-exp sexp (pddl-operators-canon domain))
          sexp)
    (check-symbol -define :define)
    (check-symbol -problem :problem)
    (let ((facts (make-pddl-facts :name name)))
      (dolist (clause clauses)
        (destructuring-ecase clause
          ((:domain name)
           (setf (pddl-facts-domain facts)
                 name))
          ((:objects &rest objs)
           (let ((typed-list (parse-typed-list objs)))
             ;; set in struct
             (setf (pddl-facts-objects facts)
                   typed-list)))
          ((:init &rest things)
           (setf (pddl-facts-init facts)
                 things))
          ((:goal goal)
           (setf (pddl-facts-goal facts)
                 goal))))
      facts)))


(defun pddl-print (exp &optional (stream *standard-output*))
  ;; Use the lisp printer to pretty print the expressions, then fixup
  ;; the output with some regular expressions
  (let* ((cl-string (with-output-to-string (s)
                      (print exp s)))
         ;; eat CL case quotes
         (string-0 (ppcre:regex-replace-all "\\|([\\w\\-]+)\\|"
                                                cl-string
                                                "\\1"))
         ;; eat string quotes
         (string-1 (ppcre:regex-replace-all "\"([\\w\\-]+)\""
                                                string-0
                                                "\\1"))
         ;; replace NILs with ()
         (string-2 (ppcre:regex-replace-all "([\\s\\(\\)])NIL([\\s\\(\\)])"
                                            string-1
                                            "\\1()\\2")))
    (princ (string-downcase (substitute #\- #\_ string-2))
           stream))
  nil)
