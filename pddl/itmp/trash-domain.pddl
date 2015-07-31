(define (domain itmp-pour-trash)
  (:requirements :typing)
  (:types block - object
          container - block
          abstract-location - object
          location - abstract-location)
  (:constants gripper trash - abstract-location)
  (:predicates (full ?obj - container))
  (:functions (position ?obj - block) - abstract-location)
  (:derived (occupied ?loc - abstract-location)
            (exists (?obj - block)
                    (= (position ?obj) ?loc)))
  (:derived (reachable ?obj - block)
            (not (= trash (position ?obj))))
  (:derived (graspable ?obj - block)
            (or (= gripper (position ?obj))
                (and (not (occupied gripper))
                     (reachable ?obj))))
  (:action transfer ; Move ?OBJ to ?LOC-1
           :parameters (?obj - block
                        ?loc-1 - location)
           :precondition (and (graspable ?obj)
                              (not (occupied ?loc-1)))
           :effect (and (= (position ?obj)
                           ?loc-1)))
  (:action pour ; Pour contents of ?SRC into ?DST
           :parameters (?src - container
                        ?dst - container)
           :precondition (and (graspable ?src)
                              (reachable ?dst)
                              (full ?src)
                              (not (full ?dst)))
           :effect (and (= gripper (position ?src))
                        (not (full ?src))
                        (full ?dst)))
  (:action discard ; Place ?obj into trash
           :parameters (?obj - block)
           :precondition (and (graspable ?obj))
           :effect (and (= trash (position ?obj)))))
