(in-package :tmsmt)

(defun placement-graph-type (node)
  (ecase (elt node 0)
    ((#\B #\I) :base)
    (#\S :surface)))

(defun parse-placement-graph (file)
  (with-open-file (s file)
    (loop for line = (read-line  s nil)
       while line
       nconc
         (ppcre:register-groups-bind (src dst)
             ("([BIS]__[0-9]+)--([BIS]__[0-9]+)" line)
             (let ((list-type
                    (let ((src-type (placement-graph-type src))
                          (dst-type (placement-graph-type dst)))
                      (cond
                        ((and (eq src-type :base)
                              (eq dst-type :base))
                         :base)
                        ((and (eq src-type :base)
                              (eq dst-type :surface))
                         :surface)
                        ((and (eq src-type :surface)
                              (eq dst-type :surface))
                         :block)
                        (t (error "Unknown node types ~A -> ~A" src-type dst-type))))))
               (list (list list-type src dst)))))))


(defun placement-graph-facts (edges
                              &key
                                (robot-start "B__0")
                                location-alist ; (list (label . locations))
                                object-alist   ; (list (object . start))
                                goal-location
                                )
  (let ((objs (map 'list #'car object-alist)))
    `(define (problem scene)
         (:domain graph)
       (:objects ,@objs)
       (:init (hand-empty)
              ,(list (strcat "ROBOT-ON-" robot-start))
              ,@(loop for (object . surface) in object-alist
                   nconc
                     (list
                      (list (strcat "FULL-" surface))
                      (list (strcat "ON-" surface) object))))
       ;; (:goal (and ,@(loop for object in objs
       ;;                  for location in (cdr (assoc goal-location location-alist))
       ;;                  collect
       ;;                    (list (strcat "ON-" location) object))))

       (:goal (and ,@(loop for object in objs
                        collect
                          `(or ,@(loop for location in (cdr (assoc goal-location location-alist))
                                    collect
                                      (list (strcat "ON-" location) object))))))
      )
     ))


(defun placement-graph-domain (edges)
  (let ((block-map (make-hash-table :test #'equal))
        (predicates (make-hash-table :test #'equal))
        (actions))
    ;; collect blocking nodes
    (loop for e in edges
       do
         (destructuring-case e
           ;; TODO: does a block b or does b block a?
           ((:block a b)
            (push a
                  (gethash b block-map nil)))))
    ;; create actions
    (labels ((pred-robot-on (base)
               (list (strcat "ROBOT-ON-" base)))
             (pred-full (s)
               (list (strcat "FULL-" s)))
             (pred-on-x (surface obj)
               (list (strcat "ON-" surface) obj))
             (pred-holding (obj)
               (list 'holding obj))
             (preds-blocked-empty (surface)
               (loop for s in (gethash surface block-map)
                  collect  `(not ,(pred-full s))))
             (add-predicate (pred)
               (setf (gethash pred predicates) t))
             (transit-action (src dst)
               `(:action ,(strcat "TRANSIT-" src "-" dst)
                         :parameters ()
                         :precondition ,(pred-robot-on src)
                         :effect (and (not ,(pred-robot-on src))
                                      ,(pred-robot-on dst)))))
      ;; predicates
      (add-predicate (pred-holding '?obj))
      (add-predicate '(hand-empty))
      (dolist (e edges)
        (destructuring-case e
          ((:base src dst)
           (add-predicate (pred-robot-on dst))
           (add-predicate (pred-robot-on src)))
          ((:surface base surface)
           (add-predicate (pred-full surface))
           (add-predicate (pred-on-x surface '?obj))
           (add-predicate (pred-robot-on base)))))
        ;; actions
        (setq actions
              (loop for e in edges
                 nconc
                   (destructuring-case e
                     ((:base a b)
                      (list (transit-action a b)
                            (transit-action b a)))
                     ((:surface base surface)
                      `((:action ,(strcat "PICK-" base "-" surface)
                                 :parameters (?obj)
                                 :precondition (and ,(pred-robot-on base)
                                                    ,(pred-full surface) ;; this precondition is redundant
                                                    ,(pred-on-x surface '?obj)
                                                    (hand-empty)
                                                    ,@(preds-blocked-empty surface))
                                 :effect (and (not ,(pred-full surface))
                                              (not ,(pred-on-x surface '?obj))
                                              (not (hand-empty))
                                              ,(pred-holding '?obj))
                                 )
                        (:action ,(strcat "PLACE-" base "-" surface)
                                 :parameters (?obj)
                                 :precondition (and ,(pred-robot-on base)
                                                    (not ,(pred-full surface))
                                                    ,(pred-holding '?obj)
                                                    (not (hand-empty))  ;; redundant precondition
                                                    ,@(preds-blocked-empty surface))
                                 :effect (and ,(pred-full surface)
                                              (hand-empty)
                                              (not ,(pred-holding '?obj))
                                              ,(pred-on-x surface '?obj)))))

                     )))
        `(define (domain graph)
             (:predicates ,@(hash-table-keys predicates))
           ,@actions)
        )))


(defun placement-graph-domain-2 (edges)
  (let ((block-map (make-hash-table :test #'equal))
        (predicates (make-hash-table :test #'equal))
        (locations (make-hash-table :test #'equal))
        (actions))
    ;; collect blocking nodes
    (loop for e in edges
       do
         (destructuring-case e
           ;; TODO: does a block b or does b block a?
           ((:block a b)
            (push a
                  (gethash b block-map nil)))))
    ;; collect locations nodes
    (loop for e in edges
       do
         (destructuring-case e
           ((:surface base surface)
            (declare (ignore base))
            (setf (gethash surface locations)
                  t))))
    ;; create actions
    (labels ((pred-full (s)
               (list (strcat "FULL-" s)))
             (pred-on-x (surface obj)
               (list (strcat "ON-" surface) obj))
             (preds-blocked-empty (surface)
               (loop for s in (gethash surface block-map)
                  collect  `(not ,(pred-full s))))
             (add-predicate (pred)
               (setf (gethash pred predicates) t)))
      ;; predicates
      (dolist (e edges)
        (destructuring-case e
          ((:surface base surface)
           (declare (ignore base))
           (add-predicate (pred-full surface))
           (add-predicate (pred-on-x surface '?obj)))))
        ;; actions
      (print (hash-table-keys locations))
      (setq actions
            (loop for loc-1 in (hash-table-keys locations)
               append (loop for loc-2 in (hash-table-keys locations)
                         unless (equal loc-1 loc-2)
                         collect
                           `(:action ,(strcat "transfer-" loc-1 "-" loc-2)
                                     :parameters (?obj)
                                     :precondition (and ,(pred-full loc-1) ;; this precondition is redundant
                                                        ,(pred-on-x loc-1 '?obj)
                                                        (not ,(pred-full loc-2))
                                                        ,@(preds-blocked-empty loc-1)
                                                        ,@(preds-blocked-empty loc-2))
                                     :effect (and (not ,(pred-full loc-1))
                                                  (not ,(pred-on-x loc-1 '?obj))
                                                  ,(pred-full loc-2)
                                                  ,(pred-on-x loc-2 '?obj))))))
        `(define (domain graph)
             (:predicates ,@(hash-table-keys predicates))
           ,@actions)
        )))

(defun placement-graph-facts-2 (edges
                              &key
                                (robot-start "B__0")
                                location-alist ; (list (label . locations))
                                object-alist   ; (list (object . start))
                                goal-location
                                )
  (let ((objs (map 'list #'car object-alist)))
    `(define (problem scene)
         (:domain graph)
       (:objects ,@objs)
       (:init ;(hand-empty)
              ;,(list (strcat "ROBOT-ON-" robot-start))
              ,@(loop for (object . surface) in object-alist
                   nconc
                     (list
                      (list (strcat "FULL-" surface))
                      (list (strcat "ON-" surface) object))))
       ;; (:goal (and ,@(loop for object in objs
       ;;                  for location in (cdr (assoc goal-location location-alist))
       ;;                  collect
       ;;                    (list (strcat "ON-" location) object))))

       (:goal (and ,@(loop for object in objs
                        collect
                          `(or ,@(loop for location in (cdr (assoc goal-location location-alist))
                                    collect
                                      (list (strcat "ON-" location) object))))))
      )
     ))
