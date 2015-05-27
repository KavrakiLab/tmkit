(in-package :tmsmt)


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

(defstruct pddl-predicate
  "A PDDL predicate"
  name
  arity
  arguments)

(defstruct pddl-operators
  "A PDDL set of operators"
  name
  types
  supertypes
  predicates
  actions)

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
    ((or string pathname) (parse-operators (load-sexp operators)))))

(defun load-facts (facts)
  "Load facts from `facts'."
  (etypecase facts
    (pddl-facts facts)
    (cons (parse-facts facts))
    ((or string pathname) (parse-facts (load-sexp facts)))))

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
      (make-pddl-predicate :name name
                           :arity (length type-list)
                           :arguments type-list))))

(defun parse-operators (sexp)
  (destructuring-bind (-define (-domain name) &rest clauses)
      sexp
    (check-symbol -define :define)
    (check-symbol -domain :domain)
    (let ((ops (make-pddl-operators :name name)))
      (dolist (clause clauses)
        (destructuring-ecase clause
          ((:requirements &rest ignore)
           ;; TODO: handle this
           (declare (ignore ignore)))
          ((:predicates &rest predicates)
           (setf (pddl-operators-predicates ops)
                 (map 'list #'parse-predicate predicates)))
          ((:action name &key parameters uncontrollable precondition effect)
           (push (make-pddl-action :name name
                              :parameters (parse-typed-list  parameters)
                              :uncontrollable uncontrollable
                              :precondition precondition
                              :effect effect)
                 (pddl-operators-actions ops)))
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
                 (setf (gethash type  hash) supertype)))
             ;; check super-types
             ;; if not explicitly given, create as subtype of t
             (dolist (x typed-list)
               (let ((supertype (pddl-typed-type x)))
                 (unless (hash-table-contains supertype hash)
                   (setf (gethash supertype hash) t))))))))
      ops)))

(defun parse-facts (sexp)
  (destructuring-bind (-define (-problem name) &rest clauses)
      sexp
    (check-symbol -define :define)
    (check-symbol -problem :problem)
    (let ((facts (make-pddl-facts :name name)))
      (dolist (clause clauses)
        (destructuring-ecase clause
          ((:domain name)
           (setf (pddl-facts-domain facts)
                 name))
          ((:objects &rest objs)
           (setf (pddl-facts-objects facts)
                 (parse-typed-list objs)))
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
