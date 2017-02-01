(in-package :tmsmt)


;(defvar *itmp-cache*)


(defun scene-collect-type (scene type)
  (let ((frames (make-tree-set (lambda (a b)
                                 (string-compare (robray::scene-frame-name a)
                                                 (robray::scene-frame-name b)))))
        (scene (scene-graph scene)))
    (robray::do-scene-graph-frames (frame scene
                                          (tree-set-list frames))
      (when (robray::scene-frame-geometry-isa frame type)
        (setf (tree-set-find frames) frame)))))

(defun scene-state (function scene configuration &optional operators)
  (canonize-exp (funcall function scene configuration)
                (when operators (pddl-operators-canon operators))))

(defun scene-facts (init-scene goal-scene
                    &key
                      operators
                      (problem 'itmp)
                      domain
                      (configuration (robray::make-configuration-map))
                      (state-function *scene-state-function*)
                      (goal-function *goal-state-function*)
                      (objects-function *scene-objects-function*))
  (let ((start-state (scene-state state-function init-scene configuration operators))
        (goal-state (scene-state goal-function goal-scene configuration operators))
        (objects (canonize-exp (funcall objects-function init-scene)
                               (when operators (pddl-operators-canon operators))))
        (domain (or domain
                    (when operators (pddl-operators-name operators))
                    'itmp)))
    `(define (problem ,problem)
         (:domain ,domain)
       (:objects ,@(loop for o in objects
                      nconc (append (cdr o)
                                    (list '- (car o)))))
       ,(cons :init start-state)
       (:goal ,(cons 'and goal-state)))))

(defun itmp-action (scene-graph sexp
                             &key
                               start)
  (let (planner error)
    (labels ((helper ()
               (handler-case
                   (let ((action-op (tm-op-action sexp scene-graph start)))
                     (if-let (function (gethash (car sexp) *refine-functions*))
                       ;; Have a refinement function
                       (tm-plan action-op
                                (funcall function
                                         scene-graph start
                                         sexp))
                       ;; No refinement function (pure task action)
                       action-op))
                 (planning-failure (e)
                   (setq planner (slot-value e 'planner)
                         error e)))))
      (multiple-value-bind (result run-time)
          (sycamore-util:with-timing (helper))
        (incf *itmp-motion-time* run-time)
        (if error
            (error 'planning-failure
                   :planner planner
                   :scene-graph scene-graph
                   :operator sexp)
            result)))))



(defun itmp-abort ()
 ;(break)
  )

(defvar *itmp-cache*)

(defvar *itmp-motion-time*)
(defvar *itmp-task-time*)
(defvar *itmp-int-time*)
(defvar *itmp-total-time*)

(defun tmp-refine (task-plan init-graph start &key
                                                     naive)
  (declare (type list task-plan)
           (type hash-table *itmp-cache*))
  (let ()
    (labels ((cache (plan)
               (let* ((prefixes (reverse (loop
                                            for trail on (reverse plan)
                                            collect trail)))
                      (prefix
                       (loop for p in prefixes
                          for n in (cdr prefixes)
                          for has-p = (gethash p *itmp-cache*)
                          for has-n = (gethash n *itmp-cache*)
                          until (not has-n)
                          finally (return p))))
                 (if-let ((c (gethash prefix *itmp-cache*)))
                   (progn
                     (format t "~&prefix: ~A" prefix)
                     (rec (subseq plan (length prefix))
                          c
                          prefix))
                   (progn
                     (format t "~&prefix: none")
                     (rec-start plan)))))
             ;; Find a prefix
             (rec-start (task-plan)
               (next task-plan nil init-graph start nil))
             (rec (task-plan tm-plan trail)
               (let ((start (tm-plan-final-config tm-plan))
                     (graph (tm-plan-final-scene-graph tm-plan)))
                 (next task-plan tm-plan graph start trail)))
             (next (task-plan tm-plan graph start trail)
               (declare (type list task-plan)
                        (type robray::scene-graph graph))
               (assert start)
               (itmp-abort)
               (if task-plan
                   (refine task-plan tm-plan graph start trail)
                   ;; Result
                   tm-plan))
             (refine (task-plan tm-plan graph start trail)
               (let* ((op (car task-plan))
                      (task-plan (cdr task-plan))
                      (trail (cons op trail)))
                 (cond
                   ((equal (car op) "NO-OP")
                    (abort))
                   (t
                    (format t "~&Refine: ~A..." op)
                    ;; Failure will raise a condition
                    (let ((new-tm-plan (itmp-action graph op :start start)))
                      (declare (type (or null tm-plan tm-op) new-tm-plan))
                      (format t "~&  success.")
                      (let ((tm-plan (tm-plan tm-plan new-tm-plan)))
                        (setf (gethash trail *itmp-cache*) tm-plan)
                        (rec task-plan tm-plan trail))))))))
      (if naive
          (rec-start task-plan)
          (cache task-plan)))))


(defun itmp-times ()
  (format t "~&IDITMP -- total time:  ~,3F~&" *itmp-total-time*)
  (format t "~&IDITMP -- task time:   ~,3F~&" *itmp-task-time*)
  (format t "~&IDITMP -- motion time: ~,3F~&" *itmp-motion-time*)
  (format t "~&IDITMP -- int. time:   ~,3F~&" *itmp-int-time*))

(defun itmp-rec (init-graph goal-graph operators
                 &key
                   facts
                   q-all-start
                   (action-encoding :boolean)
                   (naive nil)
                   (max-steps 3)
                   )
  (declare (optimize (speed 0) (debug 3))
           (type robray::configuration-map q-all-start))
  (with-smt (smt)
    (let* ((time-0 (get-internal-real-time))
           (*itmp-cache* (make-hash-table :test #'equal))
           (*itmp-motion-time* 0d0)
           (operators (load-operators operators))
           (init-graph (scene-graph init-graph))
           (goal-graph (scene-graph goal-graph))
           (task-facts (merge-facts facts
                                    (scene-facts init-graph goal-graph
                                                 :operators operators)))
           (smt-cx (smt-plan-context :operators operators
                                     :facts task-facts
                                     :action-encoding action-encoding
                                     :smt smt)))
      (labels ((next ()
                 (itmp-abort)
                 (if-let ((plan (smt-plan-next smt-cx :max-steps max-steps)))
                   (progn
                     (print plan)
                     (refine plan))
                   (error "no plan found after max steps")))
               (result (plan-steps)
                 (setq *itmp-task-time* (smt-runtime smt)
                       *itmp-total-time* (coerce (/ (- (get-internal-real-time) time-0)
                                                    internal-time-units-per-second)
                                                 'double-float))
                 (setq *itmp-int-time* (max (- *itmp-total-time*
                                               (+ *itmp-task-time* *itmp-motion-time*))
                                            0))
                 (itmp-times)
                 plan-steps)
               (add-constraint (scene-graph op planner)
                 (format t "~&  failed")
                 (cond
                   ;; Naive
                   (naive
                    (smt-plan-invalidate-plan smt-cx action-encoding))
                   ;; domain function
                   ((and (boundp '*constraint-function*)
                         *constraint-function*)
                    (let* ((c-list (robray::motion-planner-collisions planner))
                           (c-set (loop with h = (make-hash-table :test #'equal)
                                     for (a . b) in c-list
                                     do (setf (gethash a h) t
                                              (gethash b h) t)
                                     finally (return (hash-table-keys h)))))
                      (format t "~&  c-list: ~A" c-list)
                      (format t "~&  c-set: ~A" c-set)
                      (if c-set
                          (let ((e (canonize-exp (funcall *constraint-function* scene-graph op c-set))))
                            (format t "~&  collision exp: ~A" e)
                            (smt-plan-invalidate-op smt-cx e op))
                          ;;(smt-plan-invalidate-plan smt-cx action-encoding)
                          (smt-plan-invalidate-op smt-cx nil op)
                          )))
                   ;; Informaed
                   (t
                    (let ((state (scene-state *scene-state-function* scene-graph
                                              (robray::make-configuration-map)
                                              operators)))
                      ;; TODO: failed transfer picks should apply to all possible object locations
                      ;;       Will have to handle in a domain script function
                      (smt-plan-invalidate-op smt-cx state op)))))
               (refine (plan)
                 (handler-case
                     (result (tmp-refine plan init-graph q-all-start
                                        :naive naive))
                   ;; Handle failure
                   (planning-failure (e)
                     ;;(incf *itmp-motion-time* new-motion-time)
                     (with-slots (scene-graph operator planner) e
                       (add-constraint scene-graph operator planner))
                     (next)))))
        (next)))))





;; (defun itmp-encode-location (object i j)
;;   (smt-mangle object i j))

;; (defun collect-range (dim increment)
;;   ;(print (list dim increment))
;;   (let ((a (loop for i from 0 to (/ dim 2) by increment collect i)))
;;     ;(print a)
;;     (append (map 'list #'- (reverse (cdr a)))
;;             a)))


;; (defun scene-state-pairs (scene
;;                           &key
;;                             (resolution *resolution*))
;;   (labels ((frame-predicates (frame)
;;              (let* ((name  (robray::scene-frame-name frame))
;;                     (tf  (robray::scene-frame-fixed-tf frame))
;;                     (translation  (tf-translation tf))
;;                     (parent  (robray::scene-frame-parent frame))
;;                     (x  (round (vec-x translation) resolution))
;;                     (y  (round (vec-y translation) resolution)))
;;                (list name parent x y))))
;;     (let* ((scene (scene-graph scene))
;;            (moveable-frames (scene-collect-type scene "moveable")))
;;       (loop for frame in moveable-frames
;;          collect (frame-predicates frame)))))


;; (defun scene-state (scene resolution
;;                     &key
;;                       other-scene-graph
;;                       moveable-objects
;;                       (encoding :linear)
;;                       goal)
;;   (labels ((find-parent (parent)
;;              (or (scene-graph-find scene parent)
;;                  (scene-graph-find other-scene-graph parent)
;;                  (error "Could not find parent ~A" parent)))
;;            (fun-position (object location)
;;              `(= (position ,object) ,location))
;;            (surface-location (object parent i j)
;;              (ecase encoding
;;                (:quadratic (list 'at object (itmp-encode-location parent i j)))
;;                (:linear (fun-position object (itmp-encode-location parent i j)))))
;;            (parent-location (object parent)
;;              (fun-position object parent))
;;            (location-predicate (object parent i j)
;;              (let ((parent-frame (find-parent parent)))
;;                (cond
;;                  ((robray::scene-frame-geometry-isa parent-frame "surface")
;;                   (surface-location object parent i j))
;;                  ((robray::scene-frame-geometry-isa parent-frame "stackable")
;;                   (assert (eq encoding :linear))
;;                   `(= (position ,object) ,parent))
;;                  (t (error "Unkown type of parent ~A" parent)))))
;;            (occupied-predicate (parent i j)
;;              (list 'occupied (itmp-encode-location parent i j)))
;;            (frame-predicates (name parent i j)
;;              (let ((loc (location-predicate name parent i j)))
;;                (if (or goal (eq encoding :linear))
;;                    (list loc)
;;                    (list loc (occupied-predicate parent i j))))))
;;     (append (loop for object in moveable-objects
;;                for f = (scene-graph-find scene object)
;;                when f
;;                collect (parent-location object (scene-graph-parent-name scene object)))
;;             (loop for (name parent i j) in (scene-state-pairs scene :resolution resolution)
;;                nconc
;;                  (frame-predicates name parent i j)))))




;; (defun scene-locations (scene resolution &key
;;                                            max-count
;;                                            (round t)
;;                                            (encode t))
;;   (labels ((encode (list)
;;              (loop for (name x y) in list
;;                 for i = (if round (round x resolution) x)
;;                 for j = (if round (round y resolution) y)
;;                 collect
;;                   (if encode
;;                       (itmp-encode-location name i j)
;;                       (list name i j))))
;;            (subset (list count)
;;              (subseq (sort list (lambda (a b)
;;                                   (destructuring-bind (n-a x-a y-a) a
;;                                     (destructuring-bind (n-b x-b y-b) b
;;                                       (let ((r-a (sqrt (+ (* x-a x-a) (* y-a y-a))))
;;                                             (r-b (sqrt (+ (* x-b x-b) (* y-b y-b)))))
;;                                         (if (= r-a r-b)
;;                                             (if (equal n-a n-a)
;;                                                 (if (= x-a x-b)
;;                                                     (if (= y-a y-b)
;;                                                         (error "Equal locations")
;;                                                         (< y-a y-b))
;;                                                     (< x-a x-b))
;;                                                 (cond-compare (n-a n-b #'gsymbol-compare)
;;                                                               t
;;                                                               nil
;;                                                               nil))
;;                                             (< r-a r-b)))))))
;;                      0 count)))


;;     (let* ((scene (scene-graph scene))
;;            (stackable-frames (scene-collect-type scene "surface"))
;;            (locations-list
;;             (loop for frame in stackable-frames
;;                for name = (robray::scene-frame-name frame)
;;                append (loop for g in (robray::scene-frame-geometry frame)
;;                          for shape = (robray::scene-geometry-shape g)
;;                          for dimension = (robray::scene-box-dimension shape)
;;                          for xrange = (collect-range (vec-x dimension) resolution)
;;                          for yrange = (collect-range (vec-y dimension) resolution)
;;                          when (robray::scene-geometry-collision g)
;;                          append
;;                            (progn
;;                                         ;(print (list name dimension xrange yrange))
;;                              (loop for x in xrange
;;                                 append (loop for y in yrange
;;                                           collect
;;                                             (list name x y))))))))
;;       (encode
;;        (if max-count
;;            (subset locations-list max-count)
;;            locations-list)))))

;; (defun scene-facts (init-scene goal-scene
;;                     &key
;;                       object-alist
;;                       moveable-types
;;                       max-locations
;;                       (encoding :linear)
;;                       (resolution *resolution*)
;;                       (problem 'itmp)
;;                       (domain 'itmp))
;;   (let* ((init-scene (scene-graph init-scene))
;;          (goal-scene (scene-graph goal-scene))
;;          (moveable-frames (scene-collect-type init-scene "moveable"))
;;          (moveable-objects (map 'list #'robray::scene-frame-name moveable-frames))
;;          (stackable-frames (scene-collect-type init-scene "stackable"))
;;          (stackable-objects (map 'list #'robray::scene-frame-name stackable-frames))
;;          (extra-moveable-objects (loop for (type . objects) in object-alist
;;                                     when (find type moveable-types)
;;                                     append objects))
;;          ;;(stackable-objects (map 'list #'robray::scene-frame-name stackable-frames))
;;          (objects (loop for (type . objects) in object-alist
;;                      append `(,@objects - ,type)))
;;          (locations (scene-locations init-scene resolution
;;                                      :max-count max-locations
;;                                      :encode t
;;                                      :round t)))
;;     ;(print locations)
;;     `(define (problem ,problem)
;;          (:domain ,domain)
;;        (:objects ,@moveable-objects - block
;;                  ;,@stackable-objects
;;                  ,@locations - location
;;                  ,@objects)
;;        (:init ,@(scene-state init-scene resolution
;;                              :moveable-objects extra-moveable-objects
;;                              :encoding encoding
;;                              :goal nil))
;;        (:goal (and ,@(scene-state goal-scene resolution
;;                                   :moveable-objects extra-moveable-objects
;;                                   :encoding encoding
;;                                   :other-scene-graph init-scene
;;                                   :goal t))))))



;; (defun itmp-transfer-z (scene-graph object)
;;   ;; todo: other shapes
;;   (let ((g (robray::scene-frame-geometry-collision (scene-graph-find scene-graph object))))
;;     (assert (= 1 (length g)))
;;     (let ((shape (robray::scene-geometry-shape (elt g 0))))
;;       (etypecase shape
;;         (robray::scene-box (* .5d0 (vec-z (robray::scene-box-dimension shape))))))))

;; (defun itmp-transfer-action (scene-graph sexp
;;                              &key
;;                                start
;;                                encoding
;;                                resolution
;;                                (z-epsilon 1d-4)
;;                                frame
;;                                ;(plan-context *plan-context*)
;;                                ;(link)
;;                                ;(group)
;;                                )
;;   (declare (type number resolution)
;;            (type robray::scene-graph scene-graph))
;;   ;(print sexp)
;;   (destructuring-bind (-transfer object &rest rest)
;;       sexp
;;     (assert (equalp "TRANSFER" -transfer))
;;     (multiple-value-bind (src-name src-i src-j dst-name dst-i dst-j)
;;         (ecase encoding
;;           (:quadratic
;;            (values (first rest) (second rest) (third rest)
;;                    (fourth rest) (fifth rest) (sixth rest)))
;;           (:linear
;;            (let* ((frame (scene-graph-find scene-graph object))
;;                   (parent (robray::scene-frame-parent frame))
;;                   (tf (robray::scene-frame-tf frame))
;;                   (v (tf-translation tf)))
;;              (values parent (round (vec-x v) resolution) (round (vec-y v) resolution)
;;                      (first rest) (second rest) (third rest)))))
;;       (let* ((dst-x (* dst-i resolution))
;;              (dst-y (* dst-j resolution))
;;              (tf-0 (robray::scene-graph-tf-relative scene-graph src-name object
;;                                                     :configuration-map start))
;;              ;;(src-x (* src-i resolution))
;;              ;;(src-y (* src-j resolution))
;;              (act-x (vec-x (tf-translation tf-0)))
;;              (act-y (vec-y (tf-translation tf-0)))
;;              (tf-dst (tf* nil ; TODO: is identity correct?
;;                           (vec3* dst-x dst-y (+ (itmp-transfer-z scene-graph object)
;;                                                 (itmp-transfer-z scene-graph dst-name)
;;                                                 z-epsilon)))))
;;         (assert (and (= src-i (round act-x resolution))
;;                      (= src-j (round act-y resolution))))
;;                                         ;(print object)
;;                                         ;(print tf-0)
;;                                         ;(print tf-dst)
;;         ;(context-apply-scene plan-context scene-graph)
;;         (act-transfer-tf scene-graph frame start object *tf-grasp-rel*
;;                          dst-name tf-dst)))))

;; (defun itmp-stack-action (scene-graph sexp
;;                           &key
;;                             start
;;                             (z-epsilon 1d-4)
;;                             frame)
;;   (destructuring-bind (-stack obj-a obj-b)
;;       sexp
;;     (assert (rope= "STACK" -stack))
;;     (let* ((z-a (itmp-transfer-z scene-graph obj-a))
;;            (z-b (itmp-transfer-z scene-graph obj-b))
;;            (tf-dst (tf* nil (vec3* 0 0 (+ z-a z-b z-epsilon)))))
;;       ;(break)
;;       (act-transfer-tf scene-graph frame start obj-a *tf-grasp-rel*
;;                        obj-b tf-dst)
;;       )))

;; (defvar *tf-push-rel*)

;; (defun itmp-push-action (scene-graph sexp
;;                           &key
;;                             start
;;                             (z-epsilon 1d-4)
;;                             frame)
;;   (declare (ignore z-epsilon))
;;   (destructuring-bind (action obj dst)
;;       sexp
;;     (assert (rope= "PUSH-TRAY" action))
;;     (act-push-tf scene-graph frame start obj *tf-push-rel* dst)))




;; (defun itmp-action (scene-graph sexp
;;                              &key
;;                                start
;;                                encoding
;;                                resolution
;;                                (z-epsilon 1d-4)
;;                                frame
;;                                )
;;   (declare (type number resolution)
;;            (type robray::scene-graph scene-graph))
;;   ;(print sexp)
;;   (destructuring-bind (action &rest args)
;;       sexp
;;     (declare (ignore args))
;;     (multiple-value-bind (plan what frame)
;;         (cond
;;           ((rope= "TRANSFER" action)
;;            (itmp-transfer-action scene-graph sexp
;;                                  :start start
;;                                  :encoding encoding
;;                                  :resolution resolution
;;                                  :z-epsilon z-epsilon
;;                                  :frame frame))
;;           ((rope= "STACK" action)
;;            (itmp-stack-action scene-graph sexp
;;                               :start start
;;                               :z-epsilon z-epsilon
;;                               :frame frame))
;;           ((rope= "PUSH-TRAY" action)
;;            (itmp-push-action scene-graph sexp
;;                              :start start
;;                              :z-epsilon z-epsilon
;;                              :frame frame))
;;           (t (error "Urecognized action: ~A" sexp)))
;;       (values (when plan
;;                 (tm-plan (tm-op-action sexp scene-graph start)
;;                          plan))
;;                 what frame))))
