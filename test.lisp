(in-package :tmsmt)

(smt-plan "/home/ntd/git/tmsmt/pddl/blocksworld/blocks-domain.pddl"
          "/home/ntd/git/tmsmt/pddl/blocksworld/sussman-anomaly.pddl")


(with-output-to-file (s "/home/ntd/git/tmsmt/pddl/placement-graph/graph-0.pddl" :if-exists :supersede)
  (pddl-print
   (placement-graph-domain
    (parse-placement-graph "/home/ntd/git/itmp-code/itmp/Non_Reactive/JournalExp/graph.gv")) s))

(placement-graph-facts (parse-placement-graph "/home/ntd/git/itmp-code/itmp/Non_Reactive/JournalExp/graph.gv")
                       :object-alist '((Cup1 . S__82) (Cup2 . S__78) (Cup3 . S__70)))
