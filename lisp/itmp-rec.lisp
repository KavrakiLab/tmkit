(in-package :tmsmt)


;(defvar *itmp-cache*)

(defun itmp-encode-location (object x y resolution)
  (smt-mangle object
              (round (/ x resolution))
              (round (/ y resolution))))

(defun collect-range (dim increment)
  ;(print (list dim increment))
  (let ((a (loop for i from 0 to (/ dim 2) by increment collect i)))
    ;(print a)
    (append (map 'list #'- (reverse (cdr a)))
            a)))

(defun scene-facts (init-scene goal-scene
                    &key
                      (encoding :linear)
                      (resolution 0.2d0)
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
    (let* ((init-scene (scene-graph init-scene))
           (goal-scene (scene-graph goal-scene))
           (moveable-frames (collect-type init-scene "moveable"))
           (moveable-objects (map 'list #'robray::scene-frame-name moveable-frames))
           (stackable-frames (collect-type init-scene "stackable"))
           ;(stackable-objects (map 'list #'robray::scene-frame-name stackable-frames))
           (locations (loop for frame in stackable-frames
                         for name = (robray::scene-frame-name frame)
                         append (loop for g in (robray::scene-frame-geometry frame)
                                   for shape = (robray::scene-geometry-shape g)
                                   for dimension = (robray::scene-box-dimension shape)
                                   for xrange = (collect-range (elt dimension 0) resolution)
                                   for yrange = (collect-range (elt dimension 1) resolution)
                                   when (robray::scene-geometry-collision g)
                                   append
                                     (progn
                                       ;(print (list name dimension xrange yrange))
                                     (loop for x in xrange
                                        append (loop for y in yrange
                                                  collect
                                                    (itmp-encode-location name x y resolution)))))))
           (initial-true (cons '(= (last-transfer) no-object)
                               (loop for frame in moveable-frames
                                  nconc (frame-predicates frame))))
           (goal-locations (loop for frame in (collect-type goal-scene "moveable")
                            nconc (frame-predicates frame t))))
      `(define (problem ,problem)
           (:domain ,domain)
         (:objects ,@moveable-objects - block
                   ;,@stackable-objects - table
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
(defun itmp-abort ()
 ;(break)
  )

(defvar *itmp-cache*)

(defun itmp-rec (init-graph goal-graph operators
                 &key
                   (encoding :linear)
                   (max-steps 3)
                   (resolution 0.2d0)
                   (plan-context *plan-context*)
                   (frame "right_endpoint") ;; FIXME
                   (link *link*)
                   (group *group*))
  (with-smt (smt)
    (let* ((cache (make-hash-table :test #'equal))
           (motion-time 0d0)
           (init-graph (scene-graph init-graph))
           (goal-graph (scene-graph goal-graph))
           (task-facts (scene-facts init-graph goal-graph :encoding encoding :resolution resolution))
           (smt-cx (smt-plan-context :operators operators
                                     :facts task-facts
                                     :smt smt))
           (plan-steps))
      (setq *itmp-cache* cache)
      (labels ((next ()
                 (itmp-abort)
                 (setq plan-steps nil)
                 (let ((plan (smt-plan-next smt-cx :max-steps max-steps)))
                   (print plan)
                   (cache plan)))
               (cache (plan)
                 ;(print (hash-table-alist cache))
                 (let* ((prefixes (reverse (loop
                                              for trail on (reverse plan)
                                              collect trail)))
                                        ;(format t "~&keys: ~A" (hash-table-keys cache))
                        (prefix
                         (loop for p in prefixes
                            for n in (cdr prefixes)
                            for has-p = (gethash p cache)
                            for has-n = (gethash n cache)
                            until (not has-n)
                            finally (return p))))
                   (if (gethash prefix cache)
                       (let ((c (gethash prefix cache)))
                         (format t "~&prefix: ~A" prefix)
                         (setq plan-steps (first c))
                         (rec (subseq plan (length prefix))
                              (car plan-steps)
                              (second c)
                              prefix
                              *q-all-start*))
                       (progn
                         (format t "~&prefix: none")
                         (reify plan
                                init-graph *q-all-start*
                                nil)))))
                 ;; Find a prefix
               (rec (task-plan plan graph trail start)
                 (let* ((group-start (container-plan-endpoint (third plan)))
                        (all-start (container-merge-group *moveit-container* *group*
                                                          group-start start)))
                   (reify task-plan graph all-start trail)))
               (reify (task-plan graph start trail)
                 (declare (type list task-plan)
                          (type robray::scene-graph graph))
                 (itmp-abort)
                 (when task-plan
                   (let* ((op (car task-plan))
                          (task-plan (cdr task-plan))
                          (trail (cons op trail)))
                     (format t "~&Reify: ~A..." op)
                     (multiple-value-bind (plan graph)
                         (multiple-value-bind (result run-time)
                             (sycamore-util:with-timing
                               (multiple-value-list
                                (itmp-transfer-action graph op
                                                      :encoding encoding
                                                      :resolution resolution
                                                      :plan-context plan-context
                                                      :link link
                                                      :frame frame
                                                      :group group
                                                      :q-all-start start)))
                           (incf motion-time run-time)
                           (apply #'values result))
                       (declare (type list plan)
                                (type robray::scene-graph graph))
                       (if plan
                           (progn
                             (format t "success.~%")
                             (push plan plan-steps)
                             (setf (gethash trail cache)
                                   (list plan-steps graph))
                             (rec task-plan plan graph trail start))
                           (progn
                             (format t "failure.~%")
                             (next))))))))
        (next))
      (format t "~&IDITMP -- task time: ~F~&"
              (smt-runtime smt))
      (format t "~&IDITMP -- motion time: ~F~&"
              motion-time)
      (apply #'append (reverse plan-steps)))))
