(in-package :tmsmt)

(smt-plan :operators "/home/ntd/git/tmsmt/pddl/blocksworld/blocks-domain.pddl"
          :facts "/home/ntd/git/tmsmt/pddl/blocksworld/sussman-anomaly.pddl")

(smt-plan :operators "/home/ntd/git/tmsmt/pddl/placement-graph/graph-0.pddl"
          :facts "/home/ntd/git/tmsmt/pddl/placement-graph/scene-0.pddl"
          :steps 3
          :max-steps 8)

(with-output-to-file (s "/home/ntd/git/tmsmt/pddl/placement-graph/graph-quad.pddl" :if-exists :supersede)
  (pddl-print
   (placement-graph-domain-2
    (parse-placement-graph "/home/ntd/git/itmp-code/itmp/Non_Reactive/JournalExp/graph.gv")) s))

(with-output-to-file (s "/home/ntd/git/tmsmt/pddl/placement-graph/scene-quad-3.pddl" :if-exists :supersede)
  (pddl-print
   (placement-graph-facts-2 (parse-placement-graph "/home/ntd/git/itmp-code/itmp/Non_Reactive/JournalExp/graph.gv")
                          :object-alist '((Cup1 . S__44)
                                          (Cup2 . S__78)
                                          (Cup3 . S__77)
                                          (cup4 . S__46)
                                          (cup5 . S__43)
                                          (cup6 . S__76)
                                          (cup7 . S__62)
                                          (cup8 . S__67)
                                          (cup9 . S__63)
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
 ;(sb-sprof:with-profiling  (:loop t :report :flat :max-samples 500)

  (with-smt (smt)
    (let ((cx (smt-plan-context
               :operators "/home/ntd/git/tmsmt/pddl/itmp/itmp-0.pddl"
               :facts "/home/ntd/git/tmsmt/pddl/itmp/scene-0.pddl"
               :smt smt)))
      (smt-plan-next cx)
      ))
