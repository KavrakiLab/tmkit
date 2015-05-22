(in-package :tmsmt)

(defun scene-facts (init-scene goal-scene
                    &key
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
                   (tree-set-insertf frames frame)))))
           (location-predicate (object parent x y)
             (list 'at object (encode-location parent x y)))
           (occupied-predicate (parent x y)
             (list 'occupied (encode-location parent x y)))
           (frame-predicates (frame &optional goal)
             (let* ((name  (robray::scene-frame-name frame))
                    (tf  (robray::scene-frame-fixed-tf frame))
                    (translation  (tf-translation tf))
                    (parent  (robray::scene-frame-parent frame))
                    (x  (vec-x translation))
                    (y  (vec-y translation))
                    (loc (location-predicate name parent x y)))
               (if goal
                   (list loc)
               (list loc (occupied-predicate parent x y)))))
           (encode-location (obj x y)
             (smt-mangle obj
                         (round (/ x resolution))
                           (round (/ y resolution)))))
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
                                                         (encode-location name x y))))))
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
