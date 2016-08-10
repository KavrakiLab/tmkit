(define (domain blocksworld)
  (:requirements :typing)
  (:types abstract-location - object
          location - abstract-location
          fixed-location - abstract-location
          abstract-object - abstract-location
          block - abstract-object)
  (:constants no-object - abstract-object)
  (:functions (position ?obj - abstract-object) - abstract-location)
  (:derived (occupied ?loc - abstract-location)
            (exists (?obj - block) (= (position ?obj)
                                      ?loc)))
  (:derived (moveable ?obj - block)
            (not (occupied ?obj)))
  (:action transfer ; move object to other location
           :parameters (?obj - block
                        ?loc-1 - location)
           :precondition (and (moveable ?obj)
                              (not (occupied ?loc-1)))
           :effect (and (= (position ?obj)
                           ?loc-1)))
  (:action stack ; stack one object on another
           :parameters (?obj - block
                        ?loc-1 - block)
           :precondition (and (moveable ?obj)
                              (not (occupied ?loc-1)))
           :effect (and (= (position ?obj)
                           ?loc-1))))
