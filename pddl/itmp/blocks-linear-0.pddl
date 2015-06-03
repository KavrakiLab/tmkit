(define (problem simple-blocks)
  (:domain itmp)
  (:objects block-a block-b - block
            loc-0 loc-1 loc-2 - location)
  (:init (= loc-0 (position block-a))
         (= loc-1 (position block-b)))
  (:goal (and (= loc-1 (position block-a))
              (= loc-1 (position block-a)))))
