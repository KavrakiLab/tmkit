(define (domain itmp)
  (:requirements :typing)
  (:types block location - object)
  (:predicates)
  (:functions (position ?obj - block) - location)
  (:derived (occupied ?loc - location)
            (exists (?obj - block) (= (position ?obj) location)))
  (:action transfer
           :parameters (?obj - block
                        ?loc-1 - location)
           :precondition (not (occupied ?loc-1))
           :effect (and (= (position ?obj)
                           ?loc-1))))
