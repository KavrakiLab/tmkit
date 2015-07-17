(in-package :tmsmt)


(defun itmp-encode-location (object x y resolution)
  (smt-mangle object
              (round (/ x resolution))
              (round (/ y resolution))))

(defun scene-facts (init-scene goal-scene
                    &key
                      (encoding :quadratic)
                      (resolution 0.1)
                      (problem 'itmp)
                      (domain 'itmp))
  (labels ((collect-type (scene type)
             (let ((frames (make-tree-set (lambda (a b)
                                            (string-compare (robray::scene-frame-name a)
                                                            (robray::scene-frame-name b))))))
               (robray::do-scene-graph-frames (frame scene
                                                     (tree-set-list frames))
                 (when (robray::scene-frame-geometry-isa frame type)
                   (setf (tree-set-find frames) frame)))))
           (location-predicate (object parent x y)
             (ecase encoding
               (:quadratic (list 'at object (itmp-encode-location parent x y resolution)))
               (:linear `(= (position ,object) ,(itmp-encode-location parent x y resolution)))))
           (occupied-predicate (parent x y)
             (list 'occupied (itmp-encode-location parent x y resolution)))
           (frame-predicates (frame &optional goal)
             (let* ((name  (robray::scene-frame-name frame))
                    (tf  (robray::scene-frame-fixed-tf frame))
                    (translation  (tf-translation tf))
                    (parent  (robray::scene-frame-parent frame))
                    (x  (vec-x translation))
                    (y  (vec-y translation))
                    (loc (location-predicate name parent x y)))
               (if (or goal (eq encoding :linear))
                   (list loc)
                   (list loc (occupied-predicate parent x y))))))
    (let* ((moveable-frames (collect-type init-scene "moveable"))
           (moveable-objects (map 'list #'robray::scene-frame-name moveable-frames))
           (stackable-frames (collect-type init-scene "stackable"))
           (stackable-objects (map 'list #'robray::scene-frame-name stackable-frames))
           (locations (loop for frame in stackable-frames
                         for name = (robray::scene-frame-name frame)
                         append (loop for g in (robray::scene-frame-geometry frame)
                                   for shape = (robray::scene-geometry-shape g)
                                   for dimension = (robray::scene-box-dimension shape)
                                   for x-max = (/ (- (elt dimension 0) resolution)
                                                  2)
                                   for x-min = (- x-max)
                                   for y-max = (/ (- (elt dimension 1) resolution)
                                                  2)
                                   for y-min = (- y-max)
                                   when (robray::scene-geometry-collision g)
                                   append (loop for x from x-min to x-max by resolution
                                             append (loop for y from y-min to y-max by resolution
                                                       collect
                                                         (itmp-encode-location name x y resolution))))))
           (initial-true (loop for frame in moveable-frames
                            nconc (frame-predicates frame)))
           (goal-locations (loop for frame in (collect-type goal-scene "moveable")
                            nconc (frame-predicates frame t))))
      `(define (problem ,problem)
           (:domain ,domain)
         (:objects ,@moveable-objects - block
                   ,@stackable-objects - table
                   ,@locations - location)
         (:init ,@initial-true)
         (:goal (and ,@goal-locations))))))


(defun itmp-transfer-z (scene-graph object)
  ;; todo: other shapes
  (let ((g (robray::scene-frame-geometry-collision (robray::scene-graph-lookup scene-graph object))))
    (assert (= 1 (length g)))
    (let ((shape (robray::scene-geometry-shape (elt g 0))))
      (etypecase shape
        (robray::scene-box (* .5d0 (vec-z (robray::scene-box-dimension shape))))))))

(defun itmp-transfer-action (scene-graph sexp
                             &key
                               encoding
                               q-all-start
                               resolution
                               (z-epsilon 1d-4)
                               (plan-context *plan-context*)
                               (link)
                               (frame)
                               (group))
  (declare (type number resolution)
           (type robray::scene-graph scene-graph))
  ;(print sexp)
  (destructuring-bind (-transfer object &rest rest)
      sexp
    (assert (equalp "TRANSFER" -transfer))
    (multiple-value-bind (src-name src-i src-j dst-name dst-i dst-j)
        (ecase encoding
          (:quadratic
           (values (first rest) (second rest) (third rest)
                   (fourth rest) (fifth rest) (sixth rest)))
          (:linear
           (let* ((frame (robray::scene-graph-lookup scene-graph object))
                  (parent (robray::scene-frame-parent frame))
                  (tf (robray::scene-frame-tf frame))
                  (v (tf-translation tf)))
             (values parent (round (vec-x v) resolution) (round (vec-y v) resolution)
                     (first rest) (second rest) (third rest)))))
      (let* ((dst-x (* dst-i resolution))
             (dst-y (* dst-j resolution))
             (tf-0 (robray::scene-graph-tf-relative scene-graph src-name object))
             ;;(src-x (* src-i resolution))
             ;;(src-y (* src-j resolution))
             (act-x (vec-x (tf-translation tf-0)))
             (act-y (vec-y (tf-translation tf-0)))
             (tf-dst (tf* nil ; TODO: is identity correct?
                          (vec3* dst-x dst-y (+ (itmp-transfer-z scene-graph object)
                                                (itmp-transfer-z scene-graph dst-name)
                                                z-epsilon)))))
        (assert (and (= src-i (round act-x resolution))
                     (= src-j (round act-y resolution))))
                                        ;(print object)
                                        ;(print tf-0)
                                        ;(print tf-dst)
        (context-apply-scene plan-context scene-graph)
        (act-transfer-tf plan-context group q-all-start frame link object *tf-grasp-rel*
                         dst-name tf-dst)))))


(defun itmp-rec (init-graph goal-graph operators
                 &key
                   (encoding :linear)
                   (max-steps 3)
                   (resolution 0.2d0)
                   (plan-context *plan-context*)
                   (frame "right_endpoint") ;; FIXME
                   (link *link*)
                   (group *group*))
  (let* ((task-facts (scene-facts init-graph goal-graph :encoding encoding :resolution resolution))
         (smt-cx (smt-plan-context :operators operators
                                   :facts task-facts))
         (plan-steps))

    (labels ((next ()
               (setq plan-steps nil)
               (let ((plan (smt-plan-next smt-cx :max-steps max-steps)))
                 (print plan)
                 (reify plan init-graph *q-all-start*)))
             (reify (task-plan graph start)
               (declare (type list task-plan)
                        (type robray::scene-graph graph))
               (when task-plan
                 (multiple-value-bind (plan graph)
                     (itmp-transfer-action graph (car task-plan)
                                           :encoding encoding
                                           :resolution resolution
                                           :plan-context plan-context
                                           :link link
                                           :frame frame
                                           :group group
                                           :q-all-start start)
                   (declare (type list plan)
                            (type robray::scene-graph graph))
                   (if plan
                       (progn
                         (push plan plan-steps)
                         (let* ((group-start (container-plan-endpoint (third plan)))
                                (all-start (container-merge-group *moveit-container* *group*
                                                                  group-start start)))
                           (reify (cdr task-plan) graph all-start)))
                       (progn
                         (next)))))))
      (next))
    (apply #'append (reverse plan-steps))))
