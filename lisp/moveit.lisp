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

(defun context-object-tf (context name)
  (robray::scene-graph-tf-absolute (plan-context-object-graph context)
                                   name))

(defun context-add-plan-collision (context object)
  "Add object from CONTEXT's object-graph to the planning scene."
  (let* ((container (plan-context-moveit-container context))
         (scene-graph (plan-context-object-graph context))
         (object-frame (robray::scene-graph-lookup scene-graph object))
         (geometry (robray::scene-frame-collision object-frame))
         (visual (robray::scene-frame-visual object-frame))
         (tf (context-object-tf context object)))
    (etypecase geometry
      (scene-box
       (container-scene-add-box container
                                object (robray::scene-box-dimension geometry)
                                tf))
      (scene-cylinder
       (error "Unimplimented"))
      (scene-cone
       (error "Unimplimented"))
      (scene-sphere
       (container-scene-add-sphere container
                                   object (robray::scene-sphere-radius geometry)
                                   (translation tf))))
    (when visual
      (let ((color (robray::scene-visual-color visual))
            (alpha (robray::scene-visual-alpha visual)))
        (container-scene-set-color container object color alpha)))))

(defun context-draw (context parent name
                      &key
                        (actual-parent parent)
                        geometry
                        tf
                        (options nil))
  ;; Add to object-graph
  (setf (plan-context-object-graph context)
        (draw-geometry (plan-context-object-graph context)
                       parent name
                       :actual-parent actual-parent
                       :geometry geometry
                       :tf tf
                       :options options))
  ;; Maybe add to planning scene
  (when (and geometry (get-draw-option options :collision))
    (context-add-plan-collision context name)))

(defun context-add-frame-marker (context frame-name &key
                                                      (alpha 0.5d0)
                                                      (length .15)
                                                      (width .020)
                                                      (arrow-width (* 2 width))
                                                      (arrow-length (* 1 arrow-width)))
  (setf (plan-context-object-graph context)
        (robray::draw-items (plan-context-object-graph context)
                            frame-name
                            (robray::item-frame-marker (robray::draw-subframe frame-name "marker")
                                                       :length length
                                                       :width width
                                                       :arrow-width arrow-width
                                                       :arrow-length arrow-length)
                            :options (draw-options :no-shadow t :alpha alpha
                                                   :visual t :collision nil))))

(defun context-remove-object (context frame-name)
  (setf (plan-context-object-graph context)
        (scene-graph-remove-frame (plan-context-object-graph context)
                                  frame-name)))

(defun context-remove-all-objects (context)
  (setf (plan-context-object-graph context)
        (scene-graph nil)))


(defun context-attach-object (context group q-group frame link object)
  (let* ((container (plan-context-moveit-container context))
         (configuration-map (container-group-configuration-map container group q-group))
         (scene-graph (robray::scene-graph-merge  (plan-context-robot-graph context)
                                                  (plan-context-object-graph context)))
         (object-frame (robray::scene-graph-lookup scene-graph object))
         (collision (robray::scene-frame-collision object-frame))
         (tf (robray::scene-graph-tf-relative scene-graph
                                              frame object
                                              :configuration-map configuration-map)))
    (etypecase collision
      (robray::scene-box
       (container-scene-attach-box container link object (robray::scene-box-dimension collision)
                                   tf)))
    (setf (plan-context-object-graph context)
          (scene-graph-reparent (plan-context-object-graph context) frame object
                                :tf tf))))

;; (defun context-dettach-object (context group q-group object)
;;   (let* ((container (plan-context-moveit-container context))
;;          (configuration-map (container-group-configuration-map container group q-group))
;;          (scene-graph (robray::scene-graph-merge  (plan-context-robot-graph context)
;;                                                   (plan-context-object-graph context)))
;;          (object-frame (robray::scene-graph-lookup scene-graph object))
;;          (collision (robray::scene-frame-collision object-frame))
;;          (tf (robray::scene-graph-tf-absolute scene-graph object
;;                                               :configuration-map configuration-map)))
;;     (container-scene-rm container object)
;;     (setf (plan-context-object-graph context)
;;           (scene-graph-reparent (plan-context-object-graph context) frame object
;;                                 :tf tf))))



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
           (let* ((tf (tf* rotation translation))
                  (alpha (coerce alpha 'double-float))
                  (options (robray::draw-options-default :color color
                                                         :alpha alpha
                                                         :visual t
                                                         :collision t))
                  (geometry
                   (ecase shape
                     (:box
                      (scene-box (apply #'vec dimension)))
                     (:cylinder
                      (scene-cylinder :height height :radius radius))
                     (:sphere
                      (scene-sphere radius)))))
             (when geometry
               (context-draw context parent name
                             :geometry geometry
                             :tf tf
                             :options options))))
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
