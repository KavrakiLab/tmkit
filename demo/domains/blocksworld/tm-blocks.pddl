; Task-Motion extension of the 4-operator blocks world domain from the
; 2nd International Planning Competition.

;;; Extensions:
;;; ===========
;;; * Object types for BLOCK and LOCATION
;;; * ONTABLE, PICK-UP, and PUT-DOWN take a second argument for the location

(define (domain blocks)
    (:requirements :typing)
  (:types block - object
          location - object)
  (:predicates (on ?x - block ?y - block)
               (ontable ?x - block ?loc - location)
               (clear ?x - block)
               (handempty)
               (holding ?x - block))
  (:action pick-up
           :parameters (?x - block ?loc - location)
           :precondition (and (clear ?x)
                              (ontable ?x ?loc)
                              (handempty))
           :effect (and (not (ontable ?x ?loc))
                        (not (clear ?x))
                        (not (handempty))
                        (holding ?x)))
  (:action put-down
           :parameters (?x - block ?loc - location)
           :precondition (holding ?x)
           :effect (and (not (holding ?x)) (clear ?x) (handempty)
                        (ontable ?x ?loc)))
  (:action stack
           :parameters (?x - block ?y - block)
           :precondition (and (holding ?x) (clear ?y))
           :effect (and (not (holding ?x)) (not (clear ?y)) (clear ?x)
                        (handempty) (on ?x ?y)))
  (:action unstack
           :parameters (?x - block ?y - block)
           :precondition (and (on ?x ?y) (clear ?x) (handempty))
           :effect (and (holding ?x) (clear ?y) (not (clear ?x))
                        (not (handempty)) (not (on ?x ?y)))))
