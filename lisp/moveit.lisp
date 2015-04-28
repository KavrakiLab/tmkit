(in-package :tmsmt)


(defvar *node-handle* )
(defvar *plan-context* )
(defvar *moveit-container* )

(defstruct plan-context
  moveit-container
  configuration
  (robot-graph (scene-graph nil))
  (object-graph (scene-graph nil))
  (class-kwargs (make-tree-map #'string-compare))
  (object-init-map (make-tree-map #'string-compare))
  (object-goal-map (make-tree-map #'string-compare)))

;; TODO: handle ROS init and node handles in C library

(defun moveit-init (urdf-file)
  ;; TODO: get URDF from moveit
  (unless (and (boundp '*node-handle*)
               *node-handle*)
    (format t "~&Initializing ROS and moveit model~%")
    (ros-init :name "lisp")
    (setq *node-handle* (node-handle-create "lisp")))
  (unless (and (boundp '*plan-context*)
               *plan-context*)
    (setq *moveit-container* (container-create *node-handle*))
    (setq *plan-context* (make-plan-context :moveit-container *moveit-container*
                                            :robot-graph (robray::urdf-parse urdf-file)))))

(defun context-add-frame (context parent relative-tf name)
  "Add object to container. Return absolute transform."
  ;; Add relative to tree
  (setf (plan-context-object-graph context)
        (scene-graph-add-frame (plan-context-object-graph context)
                               (scene-frame-fixed parent name
                                                  :tf relative-tf))))


(defun context-object-tf (context name)
  (robray::scene-graph-tf-absolute (plan-context-object-graph context)
                                   name))

(defun context-add-geometry (context parent name tf geometry &key
                                                               no-shadow
                                                               (color '(0 0 0))
                                                               (alpha 1d0)
                                                               (collision t)
                                                               (visual t))

  (setf (plan-context-object-graph context)
        (draw-geometry (plan-context-object-graph context)
                       parent name
                       :geometry geometry
                       :tf tf
                       :no-shadow no-shadow
                       :color color
                       :alpha alpha
                       :visual visual
                       :collision collision)))

(defun context-add-sphere (context parent name tf radius &key
                                                           no-shadow
                                                           (color '(0 0 0))
                                                           (alpha 1d0)
                                                           (collision t)
                                                           (visual t))
  ;; Scene Graph
  (context-add-geometry context parent name tf (scene-sphere radius)
                        :no-shadow no-shadow
                        :color color :alpha alpha
                        :collision collision :visual visual)
  ;; Move It Scene
  (when collision
    (container-scene-add-sphere (plan-context-moveit-container context)
                                name radius
                                (translation (robray::scene-graph-tf-absolute (plan-context-object-graph context)
                                                                              name)))
    (container-scene-set-color (plan-context-moveit-container context)
                               name color alpha)))

(defun context-add-box (context parent name tf dimensions &key
                                                           no-shadow
                                                            (color '(0 0 0))
                                                            (alpha 1d0)
                                                            (collision t)
                                                            (visual t))
  ;; Scene Graph
  (context-add-geometry context parent name tf (scene-box dimensions)
                        :no-shadow no-shadow
                        :color color :alpha alpha
                        :collision collision :visual visual)
  ;; Move It Scene
  (when collision
    (container-scene-add-box (plan-context-moveit-container context)
                             name dimensions
                             (robray::scene-graph-tf-absolute (plan-context-object-graph context)
                                                              name))
    (container-scene-set-color (plan-context-moveit-container context)
                               name color alpha)))


(defun context-add-cylinder (context parent name tf length radius
                             &key
                               no-shadow
                               (color '(0 0 0))
                               (alpha 1d0)
                               (collision t)
                               (visual t))
  ;; Scene Graph
  (context-add-geometry context parent name tf (scene-cylinder :height length :radius radius)
                        :no-shadow no-shadow
                        :color color :alpha alpha
                        :collision collision :visual visual)
  (when collision
    (error "Unimplimented")))


(defun context-add-cone (context parent name tf length start-radius end-radius
                         &key
                           no-shadow
                           (color '(0 0 0))
                           (alpha 1d0)
                           (collision t)
                           (visual t))
  ;; Scene Graph
  (context-add-geometry context parent name tf (scene-cone :height length
                                                                   :start-radius start-radius
                                                                   :end-radius end-radius)
                        :no-shadow no-shadow
                        :color color :alpha alpha
                        :collision collision :visual visual)
  (when collision
    (error "Unimplimented")))


(defun context-draw (context parent name
                      &key
                        geometry
                        tf
                        (options nil)
                        (no-shadow (draw-option options :no-shadow))
                        (color (draw-option options :color))
                        (alpha (draw-option options :alpha))
                        (visual (draw-option options :visual))
                        (collision (draw-option options :collision)))

  (setf (plan-context-object-graph context)
        (draw-geometry (plan-context-object-graph context)
                       parent name
                       :geometry geometry
                       :tf tf
                       :no-shadow no-shadow
                       :color color
                       :alpha alpha
                       :visual visual
                       :collision collision
                       :options options)))


(defun context-add-frame-marker (context frame-name &key
                                                      (alpha 0.5d0)
                                                      (length .25)
                                                      (width .025)
                                                      (arrow-width (* 2 width))
                                                      (arrow-length (* 1 arrow-width)))
  (labels ((subframe (dim)
             (concatenate 'string frame-name "_robray_marker_" dim)))
    (let* ((w/2 (/ width 2))
           (cone-radius (/ arrow-width 2))
           (options (draw-options :no-shadow t :alpha 1d0
                                          :visual t :collision nil))
           (cylinder (scene-cylinder :height length :radius w/2))
           (cone (scene-cone :height arrow-length
                             :start-radius (/ arrow-width 2)
                             :end-radius 0d0)))
      (context-draw context
                    frame-name (subframe "x")
                    :geometry cylinder
                    :tf (draw-tf-axis (vec 1d0 0 0))
                    :options options
                    :color '(1 0 0))
      (context-draw context
                    frame-name (subframe "y")
                    :geometry cylinder
                    :tf (draw-tf-axis (vec 0 1d0 0))
                    :options options
                    :color '(0 1 0))
      (context-draw context
                    frame-name (subframe "z")
                    :geometry cylinder
                    :tf (draw-tf-axis (vec 0 0 1d0))
                    :options options
                    :color '(0 0 1))


      (context-draw context
                    frame-name (subframe "x_arrow")
                    :geometry cone
                    :tf (draw-tf-axis (vec 1d0 0 0) (vec3* length 0 0))
                    :options options
                    :color '(1 0 0))

      (context-draw context
                    frame-name (subframe "y_arrow")
                    :geometry cone
                    :tf (draw-tf-axis (vec 0d0 1d0 0) (vec3* 0 length 0))
                    :options options
                    :color '(0 1 0))

      (context-draw context
                    frame-name (subframe "z_arrow")
                    :geometry cone
                    :tf (draw-tf-axis (vec 0d0 0 1d0) (vec3* 0 0 length))
                    :options options
                    :color '(0 0 1)))))

(defun context-remove-object (context frame-name)
  (setf (plan-context-object-graph context)
        (scene-graph-remove-frame (plan-context-object-graph context)
                                  frame-name)))

(defun context-remove-all-objects (context)
  (setf (plan-context-object-graph context)
        (scene-graph nil)))


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
                                   (color (vec 0d0 0d0 0d0))
                                   (alpha 1d0)
                                   affords
                                   grasps
                                   )
             keyword-arguments
           (declare (ignore class affords grasps))
           (let ((tf (tf* rotation translation))
                 (alpha (coerce alpha 'double-float)))
                                        ;(print exp)
                                        ;(print absolute-tf)
             (ecase shape
               (:box
                (context-add-box context parent name tf (vec3 dimension)
                                 :color color :alpha alpha))
               ;(:cylinder
                ;(container-scene-add-cylinder container name height radius absolute-tf))
               ;(:sphere
                ;(container-scene-add-sphere container name radius (amino:translation absolute-tf)))
               )))
         (tree-map-insertf (plan-context-object-init-map context)
                           name keyword-arguments-map)))
      ((:rm name)
       (context-remove-object context name)
       (container-scene-rm container name))
      ((:goal name &key parent rotation translation)
       (tree-map-insertf (plan-context-object-goal-map context)
                           name (tf-tag parent (tf* rotation translation) name)))
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
