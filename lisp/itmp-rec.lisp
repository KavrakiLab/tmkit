(in-package :tmsmt)


;(defvar *itmp-cache*)

(defun itmp-encode-location (object i j)
  (smt-mangle object i j))

(defun collect-range (dim increment)
  ;(print (list dim increment))
  (let ((a (loop for i from 0 to (/ dim 2) by increment collect i)))
    ;(print a)
    (append (map 'list #'- (reverse (cdr a)))
            a)))


(defun scene-collect-type (scene type)
  (let ((frames (make-tree-set (lambda (a b)
                                 (string-compare (robray::scene-frame-name a)
                                                 (robray::scene-frame-name b)))))
        (scene (scene-graph scene)))
    (robray::do-scene-graph-frames (frame scene
                                          (tree-set-list frames))
      (when (robray::scene-frame-geometry-isa frame type)
        (setf (tree-set-find frames) frame)))))

(defun scene-state-pairs (scene
                          &key
                            (resolution *resolution*))
  (labels ((frame-predicates (frame)
             (let* ((name  (robray::scene-frame-name frame))
                    (tf  (robray::scene-frame-fixed-tf frame))
                    (translation  (tf-translation tf))
                    (parent  (robray::scene-frame-parent frame))
                    (x  (round (vec-x translation) resolution))
                    (y  (round (vec-y translation) resolution)))
               (list name parent x y))))
    (let* ((scene (scene-graph scene))
           (moveable-frames (scene-collect-type scene "moveable")))
      (loop for frame in moveable-frames
         collect (frame-predicates frame)))))


(defun scene-state (scene resolution
                    &key
                      (encoding :linear)
                      goal)
  (labels ((location-predicate (object parent i j)
             (let ((parent-frame (robray::scene-graph-lookup scene parent)))
               (cond
                 ((robray::scene-frame-geometry-isa parent-frame "surface")
                  (ecase encoding
                    (:quadratic (list 'at object (itmp-encode-location parent i j)))
                    (:linear `(= (position ,object) ,(itmp-encode-location parent i j)))))
                 ((robray::scene-frame-geometry-isa parent-frame "stackable")
                  (assert (eq encoding :linear))
                  `(= (position ,object) ,parent))
                 (t (error "Unkown type of parent ~A" parent)))))
           (occupied-predicate (parent i j)
             (list 'occupied (itmp-encode-location parent i j)))
           (frame-predicates (name parent i j)
             (let ((loc (location-predicate name parent i j)))
               (if (or goal (eq encoding :linear))
                   (list loc)
                   (list loc (occupied-predicate parent i j))))))
    (loop for (name parent i j) in (scene-state-pairs scene :resolution resolution)
         nconc
         (frame-predicates name parent i j))))




(defun scene-locations (scene resolution &key
                                           max-count
                                           (round t)
                                           (encode t))
  (labels ((encode (list)
             (loop for (name x y) in list
                for i = (if round (round x resolution) x)
                for j = (if round (round y resolution) y)
                collect
                  (if encode
                      (itmp-encode-location name i j)
                      (list name i j))))
           (subset (list count)
             (subseq (sort list (lambda (a b)
                                  (destructuring-bind (n-a x-a y-a) a
                                    (destructuring-bind (n-b x-b y-b) b
                                      (let ((r-a (sqrt (+ (* x-a x-a) (* y-a y-a))))
                                            (r-b (sqrt (+ (* x-b x-b) (* y-b y-b)))))
                                        (if (= r-a r-b)
                                            (if (equal n-a n-a)
                                                (if (= x-a x-b)
                                                    (if (= y-a y-b)
                                                        (error "Equal locations")
                                                        (< y-a y-b))
                                                    (< x-a x-b))
                                                (cond-compare (n-a n-b #'gsymbol-compare)
                                                              t
                                                              nil
                                                              nil))
                                            (< r-a r-b)))))))
                     0 count)))


    (let* ((scene (scene-graph scene))
           (stackable-frames (scene-collect-type scene "surface"))
           (locations-list
            (loop for frame in stackable-frames
               for name = (robray::scene-frame-name frame)
               append (loop for g in (robray::scene-frame-geometry frame)
                         for shape = (robray::scene-geometry-shape g)
                         for dimension = (robray::scene-box-dimension shape)
                         for xrange = (collect-range (vec-x dimension) resolution)
                         for yrange = (collect-range (vec-y dimension) resolution)
                         when (robray::scene-geometry-collision g)
                         append
                           (progn
                                        ;(print (list name dimension xrange yrange))
                             (loop for x in xrange
                                append (loop for y in yrange
                                          collect
                                            (list name x y))))))))
      (encode
       (if max-count
           (subset locations-list max-count)
           locations-list)))))

(defun scene-facts (init-scene goal-scene
                    &key
                      max-locations
                      (encoding :linear)
                      (resolution 0.2d0)
                      (problem 'itmp)
                      (domain 'itmp))
  (let* ((init-scene (scene-graph init-scene))
         (goal-scene (scene-graph goal-scene))
         (moveable-frames (scene-collect-type init-scene "moveable"))
         (moveable-objects (map 'list #'robray::scene-frame-name moveable-frames))
         (stackable-frames (scene-collect-type init-scene "stackable"))
         (stackable-objects (map 'list #'robray::scene-frame-name stackable-frames))
         ;;(stackable-objects (map 'list #'robray::scene-frame-name stackable-frames))
         (locations (scene-locations init-scene resolution
                                     :max-count max-locations
                                     :encode t
                                     :round t)))
    `(define (problem ,problem)
         (:domain ,domain)
       (:objects ,@moveable-objects - block
                 ,@stackable-objects
                 ,@locations - location)
       (:init ,@(scene-state init-scene resolution
                                   :encoding encoding
                                   :goal nil))
       (:goal (and ,@(scene-state goal-scene resolution
                                  :encoding encoding
                                  :goal t))))))


(defun itmp-transfer-z (scene-graph object)
  ;; todo: other shapes
  (let ((g (robray::scene-frame-geometry-collision (robray::scene-graph-lookup scene-graph object))))
    (assert (= 1 (length g)))
    (let ((shape (robray::scene-geometry-shape (elt g 0))))
      (etypecase shape
        (robray::scene-box (* .5d0 (vec-z (robray::scene-box-dimension shape))))))))

(defun itmp-transfer-action (scene-graph sexp
                             &key
                               start
                               encoding
                               resolution
                               (z-epsilon 1d-4)
                               frame
                               ;(plan-context *plan-context*)
                               ;(link)
                               ;(group)
                               )
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
             (tf-0 (robray::scene-graph-tf-relative scene-graph src-name object
                                                    :configuration-map start))
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
        ;(context-apply-scene plan-context scene-graph)
        (act-transfer-tf scene-graph frame start object *tf-grasp-rel*
                         dst-name tf-dst)))))
(defun itmp-abort ()
 ;(break)
  )

(defvar *itmp-cache*)

(defvar *itmp-motion-time*)
(defvar *itmp-task-time*)
(defvar *itmp-int-time*)
(defvar *itmp-total-time*)

(defun tmp-reify (cache task-plan init-graph start &key
                                                     frame
                                                     naive
                                                     encoding
                                                     resolution)
  (declare (type list task-plan)
           (type hash-table cache))
  (let ((motion-time 0)
        (plan-steps))
    (labels ((cache (plan)
               ;;(print (hash-table-alist cache))
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
                            start))
                     (progn
                       (format t "~&prefix: none")
                       (rec-start plan)))))
             ;; Find a prefix
             (rec-start (task-plan)
               (next task-plan init-graph start nil))
             (rec (task-plan plan graph trail start)
               (declare (ignore start))
               (let ((start (tm-plan-endpoint plan)))
                 (next task-plan graph start trail)))
             (next (task-plan graph start trail)
               (declare (type list task-plan)
                        (type robray::scene-graph graph))
               (assert start)
               (itmp-abort)
               (if task-plan
                   (reify task-plan graph start trail)
                   (result plan-steps cache motion-time
                           nil nil nil nil)))
             (result (plan-steps cache motion-time end-graph op what-failed object)
               (values (apply #'append (reverse plan-steps)) cache motion-time
                       end-graph op what-failed object))
             (reify (task-plan graph start trail)
               (let* ((op (car task-plan))
                      (task-plan (cdr task-plan))
                      (trail (cons op trail)))
                 (cond
                   ((equal (car op) "NO-OP")
                    (push :no-op plan-steps))
                   (t
                    (format t "~&Reify: ~A..." op)
                    (multiple-value-bind (plan graph what-failed object)
                        (multiple-value-bind (result run-time)
                            (sycamore-util:with-timing
                              (multiple-value-list
                               (itmp-transfer-action graph op
                                                     :encoding encoding
                                                     :resolution resolution
                                                     :frame frame
                                                     :start start)))
                          (incf motion-time run-time)
                          (apply #'values result))
                      (declare (type list plan)
                               (type scene-graph graph))
                      (if plan
                          (progn
                            (assert (null what-failed))
                            (format t "~&success.~%")
                            (push plan plan-steps)
                            (setf (gethash trail cache)
                                  (list plan-steps graph))
                            (rec task-plan plan graph trail start))
                          ;; failed
                          (progn
                            (format t "~&failure (~A ~A).~%" what-failed object)
                            (result nil cache motion-time
                                    graph op what-failed object)))))))))
      (if naive
          (rec-start task-plan)
          (cache task-plan)))))


(defun itmp-rec (init-graph goal-graph operators
                 &key
                   q-all-start
                   max-locations
                   (encoding :linear)
                   (action-encoding :boolean)
                   (naive nil)
                   (max-steps 3)
                   (resolution 0.2d0)
                   frame
                   )
  (declare (optimize (speed 0) (debug 3))
           (type robray::configuration-map q-all-start))
  (with-smt (smt)
    (let* ((time-0 (get-internal-real-time))
           (cache (make-hash-table :test #'equal))
           (motion-time 0d0)
           (init-graph (scene-graph init-graph))
           (goal-graph (scene-graph goal-graph))
           (task-facts (scene-facts init-graph goal-graph :encoding encoding :resolution resolution
                                    :max-locations max-locations))
           (locations (scene-locations init-graph resolution :max-count max-locations
                                       :encode nil
                                       :round t))
           (smt-cx (smt-plan-context :operators operators
                                     :facts task-facts
                                     :action-encoding action-encoding
                                     :smt smt)))
      (setq *itmp-cache* cache)
      (labels ((next ()
                 (itmp-abort)
                 (let ((plan (smt-plan-next smt-cx :max-steps max-steps)))
                   (print plan)
                   (reify plan)))
               (result (plan-steps)
                 (setq *itmp-task-time* (smt-runtime smt)
                       *itmp-motion-time* motion-time
                       *itmp-total-time* (coerce (/ (- (get-internal-real-time) time-0)
                                                    internal-time-units-per-second)
                                                 'double-float))
                 (setq *itmp-int-time* (max (- *itmp-total-time*
                                               (+ *itmp-task-time* *itmp-motion-time*))
                                            0))
                 (format t "~&IDITMP -- total time:  ~,3F~&" *itmp-total-time*)
                 (format t "~&IDITMP -- task time:   ~,3F~&" *itmp-task-time*)
                 (format t "~&IDITMP -- motion time: ~,3F~&" *itmp-motion-time*)
                 (format t "~&IDITMP -- int. time:   ~,3F~&" *itmp-int-time*)
                 plan-steps)
               (reify (plan)
                 (multiple-value-bind (plan-steps new-cache new-motion-time
                                                  failed-graph failed-op what-failed object)
                     (tmp-reify cache plan init-graph q-all-start
                                :frame frame
                                :naive naive
                                :encoding encoding
                                :resolution resolution)
                   (setq cache new-cache)
                   (incf motion-time new-motion-time)
                   (if plan-steps
                       (result plan-steps)
                       ;; failed
                       (progn
                         (if naive
                             ;; naive
                             (smt-plan-invalidate-plan smt-cx action-encoding)
                             ;; informed
                             (let ((state (scene-state failed-graph resolution
                                                       :encoding encoding
                                                       :goal nil)))
                               (ecase what-failed
                                 (:place
                                  (smt-plan-invalidate-op smt-cx state failed-op))
                                 (:pick
                                  (dolist (loc locations)
                                        ;(print op)
                                        ;(print (list* "TRANSFER" object loc))
                                        ;(abort)
                                    (smt-plan-invalidate-op smt-cx
                                                            state
                                                            (list* "TRANSFER" object loc)))))))
                         (next))))))
        (next)))))
