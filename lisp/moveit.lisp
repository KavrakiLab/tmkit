(in-package :tmsmt)


(defvar *node-handle* )
(defvar *moveit-cx* )


(defun moveit-init ()
  (unless (and (boundp '*node-handle*)
               *node-handle*)
    (format t "~&Initializing ROS and moveit model~%")
    (ros-init :name "lisp")
    (setq *node-handle* (node-handle-create "lisp")))
  (unless (and (boundp '*moveit-cx*)
               *moveit-cx*)
    (setq *moveit-cx* (container-create *node-handle*))))

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

(defun moveit-scene-exp-eval (exp &key (context *moveit-cx*))
  (destructuring-ecase exp
    (((:box :cylinder :sphere) name &rest keyword-args)
     (destructuring-bind (&key dimension rotation translation parent height radius class color (alpha 1.0))
         keyword-args
       (declare (ignore class))
       (let ((absolute-tf (container-add-object context parent (aa:tf rotation translation) name)))
         (print exp)
         (print absolute-tf)
         (ecase (car exp)
           (:box
            (container-scene-add-box context name (aa:vec3 dimension) absolute-tf))
           (:cylinder
            (container-scene-add-cylinder context name height radius absolute-tf))
           (:sphere
            (container-scene-add-sphere context name radius (amino:translation absolute-tf))))
         (when color
           (etypecase color
             (cons (container-scene-set-color context name
                                              (coerce (elt color 0) 'single-float)
                                              (coerce (elt color 1) 'single-float)
                                              (coerce (elt color 2) 'single-float)
                                              (coerce  alpha 'single-float))))))))
    ((:rm name)
     (container-remove-object context name)
     (container-scene-rm context name))
    ((:clear)
     (container-remove-all-objects context)
     (container-scene-clear context))
    ((:seq &rest ops)
     (dolist (exp ops)
       (moveit-scene-exp-eval exp :context context)))))


(defun moveit-scene-file (file &key (context *moveit-cx*))
  (let ((exp (cons :seq (load-all-sexp file))))
    (moveit-scene-exp-eval exp :context context)))
