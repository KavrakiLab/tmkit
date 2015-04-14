(in-package :tmsmt)


(defvar *node-handle* )
(defvar *plan-context* )
(defvar *moveit-container* )

(defstruct plan-context
  moveit-container
  (tf-tree (make-tf-tree))
  (class-kwargs (make-tree-map #'string-compare))
  (object-init-map (make-tree-map #'string-compare))
  (object-goal-map (make-tree-map #'string-compare)))

;; TODO: handle ROS init and node handles in C library

(defun moveit-init ()
  (unless (and (boundp '*node-handle*)
               *node-handle*)
    (format t "~&Initializing ROS and moveit model~%")
    (ros-init :name "lisp")
    (setq *node-handle* (node-handle-create "lisp")))
  (unless (and (boundp '*plan-context*)
               *plan-context*)
    (setq *moveit-container* (container-create *node-handle*))
    (setq *plan-context* (make-plan-context :moveit-container *moveit-container*))))

(defun context-add-object (context parent relative-tf name)
  "Add object to container. Return absolute transform."
  ;; Add relative to tree
  (setf (plan-context-tf-tree context)
        (tf-tree-insert (plan-context-tf-tree context)
                        (tf-tag parent relative-tf name)))
  ;; Find absolute
  (tf-tag-tf (tf-tree-absolute-tf (plan-context-tf-tree context)
                                 name)))

(defun context-remove-object (context frame)
  (setf (plan-context-tf-tree context)
        (tf-tree-remove (plan-context-tf-tree context)
                        frame)))

(defun context-remove-all-objects (context)
  (setf (plan-context-tf-tree context)
        (make-tf-tree)))


(defun symbol-compare (a b)
  (string-compare (string a) (string b)))

(defun kwarg-map-insert-list (map argument-list)
  (if (null argument-list)
      map
      (destructuring-bind (keyword argument &rest argument-list)
          argument-list
        (assert (keywordp keyword))
        (kwarg-map-insert-list (tree-map-insert map keyword argument)
                               argument-list))))

(defun kwarg-map (argument-list)
  (kwarg-map-insert-list (make-tree-map #'gsymbol-compare)
                         argument-list))


(defun kwarg-map-insert-map (initial-map new-map)
  (fold-tree-map #'tree-map-insert initial-map new-map))

(defun kwarg-map-list (map)
  (fold-tree-map (lambda (list key value)
                   (list* key value list))
                 nil map))

(defun context-kwarg-apply (context classes kwargs)
  (let* ((class-kwargs  (plan-context-class-kwargs context))
         (class-map (fold (lambda (map class)
                            (kwarg-map-insert-map map (tree-map-find class-kwargs class)))
                          (kwarg-map nil)
                          classes)))
    (kwarg-map-insert-list class-map kwargs)))

(defun context-add-class (context name parents kwargs)
  (tree-map-insertf (plan-context-class-kwargs context)
                    name
                    (context-kwarg-apply context parents kwargs)))

(defun context-class-keyword-arguments (context keyword-arguments)
  "Apply class arguments to KEYWORD-ARGUMENTS."
  (destructuring-bind (&key class &allow-other-keys) keyword-arguments
    (context-kwarg-apply context class keyword-arguments)))

;;; OBJECT ADD DSL
;;;
;;; <E>               ::=  <ADD_OP> | <RM_OP> | <CLEAR_OP> | <SEQ_OP>
;;; <ADD_OP>          ::= :box      'NAME' (<TF_ARG> | <DIMENSION_ARG> | <COLOR_ARG> | <ALPHA_ARG>)*
;;;                     | :cylinder 'NAME' (<TF_ARG> | <HEIGHT_ARG> | <RADIUS_ARG> | <COLOR_ARG> | <ALHPA_ARG>)*
;;;                     | :sphere   'NAME' (<TRANSLATION_ARG> | <RADIUS_ARG> | <COLOR_ARG> | <ALHPA_ARG>)*
;;; <ROTATATION_ARG>  ::= :rotation 'ROTATION'
;;; <TRANSLATION_ARG> ::= :translation 'TRANSLATION'
;;; <TF_ARG>          ::= (<ROTATION_ARG> | <TRANSLATION_ARG>)*
;;; <RADIUS_ARG>      ::= :radius 'RADIUS'
;;; <HEIGHT_ARG>      ::= :height 'HEIGHT'
;;; <DIMENSION_ARG>   ::= :dimension 'DIMENSION'
;;; <COLOR_ARG>       ::= :color 'COLOR'
;;; <ALPHA_ARG>       ::= :alpha 'ALPHA'
;;; <RM_OP>           ::= 'NAME'
;;; <CLEAR_OP>        ::= :clear
;;; <CLASS_OP>        ::= :class 'NAME' 'PARENTS' ARGS*
;;; <SEQ_OP>          ::= :seq <E>*

;;; TODO: parent frames

(defun dbl (x)
  (coerce 'double-float x))

(defun moveit-scene-exp-eval (exp &key (context *plan-context*))
  (let ((container (plan-context-moveit-container context)))
    (destructuring-ecase exp
      ((:object name &rest keyword-arguments)
       (let* ((keyword-arguments-map (context-class-keyword-arguments context keyword-arguments))
              (keyword-arguments (kwarg-map-list keyword-arguments-map)))
         (destructuring-bind (&key parent
                                   class
                                   shape
                                   dimension rotation translation
                                   height radius
                                   color (alpha 1.0)
                                   affords
                                   grasps
                                   )
             keyword-arguments
           (declare (ignore class affords grasps))
           (let ((absolute-tf (context-add-object context parent (aa:tf rotation translation) name)))
                                        ;(print exp)
                                        ;(print absolute-tf)
             (ecase shape
               (:box
                (container-scene-add-box container name (aa:vec3 dimension) absolute-tf))
               (:cylinder
                (container-scene-add-cylinder container name height radius absolute-tf))
               (:sphere
                (container-scene-add-sphere container name radius (amino:translation absolute-tf))))
             (when color
               (etypecase color
                 (cons (container-scene-set-color container name
                                                  (coerce (vec-x color) 'single-float)
                                                  (coerce (vec-y color) 'single-float)
                                                  (coerce (vec-z color) 'single-float)
                                                  (coerce  alpha 'single-float)))))))
         (tree-map-insertf (plan-context-object-init-map context)
                           name keyword-arguments-map)))
      ((:rm name)
       (context-remove-object context name)
       (container-scene-rm container name))
      ((:goal name &key parent rotation translation)
       (tree-map-insertf (plan-context-object-goal-map context)
                           name (tf-tag parent (tf rotation translation) name)))
      ((:clear)
       (context-remove-all-objects context)
       (container-scene-clear container))
      ((:class name parents &rest keyword-arguments)
       (context-add-class context name parents keyword-arguments))
      ((:seq &rest ops)
       (dolist (exp ops)
         (moveit-scene-exp-eval exp :context context))))))


(defun moveit-scene-file (file &key (context *plan-context*))
  (let ((exp (cons :seq (load-all-sexp file))))
    (moveit-scene-exp-eval exp :context context)))

(defun moveit-scene-facts (context
                           &key
                             (resolution 0.1)
                             (problem 'itmp)
                             (domain 'itmp))

  (let ((object-init-map (plan-context-object-init-map context)))
    (labels ((kwarg-map (object)
               (tree-map-find object-init-map object))
             (kwarg-value (object keyword)
               (tree-map-find (kwarg-map object) keyword))
             (affords (object action)
               (if (find action (kwarg-value object :affords) :test #'string=)
                   t nil))
             (collect-affords (action)
               (fold-tree-map (lambda (list name kwarg-map)
                                (declare (ignore kwarg-map))
                                (if (affords name action)
                                    (cons name list)
                                    list))
                              nil object-init-map))
             (encode-location (obj x y)
               (smt-mangle obj
                           (round (/ x resolution))
                           (round (/ y resolution))))
             (location-predicate (object parent x y)
               (list 'at object (encode-location parent x y)))
             (occupied-predicate (parent x y)
               (list 'occupied (encode-location parent x y))))
      (let* ((moveable-objects (collect-affords "move"))
             (stackable-objects (collect-affords "stack"))
             (locations (loop for obj in stackable-objects
                          for dimension = (kwarg-value obj :dimension)
                          for x-max = (/ (- (first dimension) resolution)
                                         2)
                          for x-min = (- x-max)
                          for y-max = (/ (- (second dimension) resolution)
                                         2)
                          for y-min = (- y-max)
                           append (loop for x from x-min to x-max by resolution
                                     append (loop for y from y-min to y-max by resolution
                                               collect
                                                 (encode-location obj x y)))))
             (initial-true (loop for obj in moveable-objects
                              for translation = (kwarg-value obj :translation)
                              for parent = (kwarg-value obj :parent)
                              for x = (vec-x translation)
                              for y = (vec-y translation)
                              nconc (list (location-predicate obj parent x y)
                                          (occupied-predicate parent x y))))
             (goal-locations (map-tree-map :inorder 'list
                                           (lambda (name tf-tag)
                                             (let* ((translation (translation (tf-tag-tf tf-tag))))
                                               (location-predicate name (tf-tag-parent tf-tag)
                                                                   (vec-x translation)
                                                                   (vec-y translation))))
                                           (plan-context-object-goal-map context)))

             )

        `(define (problem ,problem)
             (:domain ,domain)
           (:objects ,@moveable-objects - block
                     ,@stackable-objects - table
                     ,@locations - location)
           (:init ,@initial-true)
           (:goal (and ,@goal-locations))
                     )))))

        ;; (values moveable-objects
        ;;         stackable-objects
        ;;         locations)))))
