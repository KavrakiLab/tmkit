(define (domain itmp)
  (:requirements :typing)
  (:types location - object
          abstract-block - object
          block - abstract-block)
  (:predicates)
  (:constants no-object - abstract-block)
  (:functions (position ?obj - block) - location
              (last-transfer) - abstract-block)
  (:derived (occupied ?loc - location)
            (exists (?obj - block) (= (position ?obj)
                                      ?loc)))
  (:action transfer
           :parameters (?obj - block
                        ?loc-1 - location)
           :precondition (and (not (occupied ?loc-1))
                              (not (= ?obj (last-transfer))))
           :effect (and (= (position ?obj)
                           ?loc-1)
                        (= (last-transfer) ?obj))))
