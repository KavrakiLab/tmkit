(in-package :tmsmt)


(defvar *node-handle* )
(defvar *plan-context* )
(defvar *moveit-container* )

(defstruct plan-context
  moveit-container
  (tf-tree (make-tf-tree))
  (class-kwargs (make-tree-map #'string-compare)))

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
;;; <SEQ_OP>          ::= :seq <E>*

;;; TODO: parent frames

(defun dbl (x)
  (coerce 'double-float x))

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

(defun kwarg-map-list (map)
  (fold-tree-map (lambda (list key value)
                   (list* key value list))
                 nil map))

(defun moveit-scene-exp-eval (exp &key (context *plan-context*))
  (let ((container (plan-context-moveit-container context)))
    (destructuring-ecase exp
      (((:box :cylinder :sphere) name &rest keyword-args)
       (destructuring-bind (&key dimension rotation translation parent height radius class color (alpha 1.0))
           keyword-args
         (declare (ignore class))
         (let ((absolute-tf (context-add-object context parent (aa:tf rotation translation) name)))
           (print exp)
           (print absolute-tf)
           (ecase (car exp)
             (:box
              (container-scene-add-box container name (aa:vec3 dimension) absolute-tf))
             (:cylinder
              (container-scene-add-cylinder container name height radius absolute-tf))
             (:sphere
              (container-scene-add-sphere container name radius (amino:translation absolute-tf))))
           (when color
             (etypecase color
               (cons (container-scene-set-color container name
                                                (coerce (elt color 0) 'single-float)
                                                (coerce (elt color 1) 'single-float)
                                                (coerce (elt color 2) 'single-float)
                                                (coerce  alpha 'single-float))))))))
      ((:rm name)
       (context-remove-object context name)
       (container-scene-rm container name))
      ((:clear)
       (context-remove-all-objects context)
       (container-scene-clear container))
      ((:seq &rest ops)
       (dolist (exp ops)
         (moveit-scene-exp-eval exp :context context))))))


(defun moveit-scene-file (file &key (context *plan-context*))
  (let ((exp (cons :seq (load-all-sexp file))))
    (moveit-scene-exp-eval exp :context context)))
