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
               (clear ?x)
               (handempty)
               (safety-light)
               (holding ?x - block))
  (:action enable-motion
           :parameters ()
           :effect (and (safety-light)))
  (:action disable-motion
           :parameters ()
           :effect (and (safety-light)))
  (:action pick-up
           :parameters (?x - block ?loc - location)
           :precondition (and (clear ?x)
                              (safety-light)
                              (ontable ?x ?loc)
                              (handempty))
           :effect (and (not (ontable ?x ?loc))
                        (not (clear ?x))
                        (not (handempty))
                        (holding ?x)
                        (clear ?loc)))
  (:action put-down
           :parameters (?x - block ?loc - location)
           :precondition (and (holding ?x)
                              (safety-light)
                              (clear ?loc))
           :effect (and (not (holding ?x))
                        (handempty)
                        (clear ?x)
                        (ontable ?x ?loc)
                        (not (clear ?loc))))
  (:action stack
           :parameters (?x - block ?y - block)
           :precondition (and (holding ?x)
                              (safety-light)
                              (clear ?y))
           :effect (and (not (holding ?x))
                        (handempty)
                        (not (clear ?y))
                        (clear ?x)
                        (on ?x ?y)))
  (:action unstack
           :parameters (?x - block ?y - block)
           :precondition (and (on ?x ?y)
                              (safety-light)
                              (clear ?x)
                              (handempty))
           :effect (and (holding ?x)
                        (not (handempty))
                        (not (clear ?x))
                        (clear ?y)
                        (not (on ?x ?y)))))
