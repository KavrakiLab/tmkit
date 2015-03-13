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
                                location-alist ; (list (label . location))
                                object-alist   ; (list (object . start))
                                goal-location
                                )
  `(define (problem scene)
       (:domain graph)
     (:objects ,@(map 'list #'car object-alist)
     (:init (hand-empty)
            (strcat "ROBOT-AT-" robot-start)
            ,@(loop for (object . surface) in object-alist
                 nconc
                   (list
                    (list (strcat "FULL-" surface))
                    (list (strcat "AT-" surface) object)))))))


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
    (labels ((pred-robot-at (base)
               (list (strcat "ROBOT-AT-" base)))
             (pred-full (s)
               (list (strcat "FULL-" s)))
             (pred-at-x (surface obj)
               (list (strcat "AT-" surface) obj))
             (pred-holding (obj)
               (list 'holding obj))
             (preds-blocked-empty (surface)
               (loop for s in (gethash surface block-map)
                  collect  `(not ,(pred-full s))))
             (add-predicate (pred)
               (setf (gethash pred predicates) t)))
      ;; predicates
      (add-predicate (pred-holding '?obj))
      (add-predicate '(hand-empty))
      (dolist (e edges)
        (destructuring-case e
          ((:base src dst)
           (add-predicate (pred-robot-at dst))
           (add-predicate (pred-robot-at src)))
          ((:surface base surface)
           (add-predicate (pred-full surface))
           (add-predicate (pred-at-x surface '?obj))
           (add-predicate (pred-robot-at base)))))
        ;; actions
        (setq actions
              (loop for e in edges
                 nconc
                   (destructuring-case e
                     ((:base src dst)
                      `((:action ,(strcat "TRANSIT-" src "-" dst)
                                 :precondition ,(pred-robot-at src)
                                 :effect (and (not ,(pred-robot-at src))
                                              ,(pred-robot-at dst)))))
                     ((:surface base surface)
                      `((:action ,(strcat "PICK-" base "-" surface)
                                 :parameters (?obj)
                                 :precondition (and ,(pred-robot-at base)
                                                    ,(pred-full surface) ;; this precondition is redundant
                                                    ,(pred-at-x surface '?obj)
                                                    (hand-empty)
                                                    ,@(preds-blocked-empty surface))
                                 :effect (and (not ,(pred-full surface))
                                              (not ,(pred-at-x surface '?obj))
                                              (not (hand-empty))
                                              ,(pred-holding '?obj))
                                 )
                        (:action ,(strcat "PLACE-" base "-" surface)
                                 :parameters (?obj)
                                 :precondition (and ,(pred-robot-at base)
                                                    (not ,(pred-full surface))
                                                    ,(pred-holding '?obj)
                                                    (not (hand-empty))  ;; redundant precondition
                                                    ,@(preds-blocked-empty surface))
                                 :effect (and ,(pred-full surface)
                                              (hand-empty)
                                              (not ,(pred-holding '?obj))
                                              ,(pred-at-x surface '?obj))))))))
        `(define (domain graph)
             (:predicates ,@(hash-table-keys predicates))
           ,@actions)
        )))
