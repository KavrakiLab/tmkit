(define (problem simple-trash)
  (:domain itmp-pour-trash)
  (:objects block-a block-b - block
            loc-0 loc-1 loc-2 - location)
  (:init (= loc-0 (position block-a))
         (= loc-1 (position block-b)))
  (:goal (and (= loc-1 (position block-a))
              (= loc-0 (position block-b)))))
