(define (domain itmp)
  (:requirements :typing)
  (:types block
          location - object
          )
  (:predicates (at ?obj - block
                   ?loc - location)
               (occupied ?loc - location))
  (:action transfer
           :parameters (?obj - block
                        ?loc-0 ?loc-1 - location)
           :precondition (and (at ?obj ?loc-0)
                              (not (occupied ?loc-1)))
           :effect (and (not (at ?obj ?loc-0))
                        (not (occupied ?loc-0))
                        (at ?obj ?loc-1)
                        (occupied ?loc-1))))
