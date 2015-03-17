(in-package :tmsmt)

(smt-plan :operators "/home/ntd/git/tmsmt/pddl/blocksworld/blocks-domain.pddl"
          :facts "/home/ntd/git/tmsmt/pddl/blocksworld/sussman-anomaly.pddl")

(smt-plan :operators "/home/ntd/git/tmsmt/pddl/placement-graph/graph-0.pddl"
          :facts "/home/ntd/git/tmsmt/pddl/placement-graph/scene-0.pddl"
          :steps 3
          :max-steps 3)

(with-output-to-file (s "/home/ntd/git/tmsmt/pddl/placement-graph/graph-0.pddl" :if-exists :supersede)
  (pddl-print
   (placement-graph-domain
    (parse-placement-graph "/home/ntd/git/itmp-code/itmp/Non_Reactive/JournalExp/graph.gv")) s))

(with-output-to-file (s "/home/ntd/git/tmsmt/pddl/placement-graph/scene-9.pddl" :if-exists :supersede)
  (pddl-print
   (placement-graph-facts (parse-placement-graph "/home/ntd/git/itmp-code/itmp/Non_Reactive/JournalExp/graph.gv")
                          :object-alist '((Cup1 . S__82)
                                          (Cup2 . S__78)
                                          (Cup3 . S__70)
                                          (cup4 . S__44)
                                          (cup6 . S__46)
                                          (cup7 . S__47)
                                          (cup8 . S__62)
                                          (cup8 . S__69)
                                          )
                          ;:object-alist '((Cup1 . S__82))
                          :location-alist '((dishwasher S__33 S__34 S__35 S__36 S__37 S__38 S__39 S__40 S__43))
                          :goal-location 'dishwasher)
   s))


(sb-sprof:with-profiling  (:loop nil :report :flat)
  (smt-plan :operators "/home/ntd/git/tmsmt/pddl/placement-graph/graph-0.pddl"
            :facts "/home/ntd/git/tmsmt/pddl/placement-graph/scene-0.pddl"
            :steps 3
            :max-steps 3))
