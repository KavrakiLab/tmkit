(define (problem simple-trash)
  (:domain itmp-pour-trash)
  (:objects block-a block-b - block
            loc-0 loc-1 loc-2 loc-3 loc-4 loc-5 loc-6 loc-7 loc-8 loc-9  - location
            bottle-0 cup-0
            bottle-1 cup-1
            bottle-2 cup-2
            bottle-3 cup-3
            ;bottle-4 cup-4
            ;bottle-5 cup-5
            - container
            )
  (:init (= loc-0 (position block-a))
         (= loc-1 (position block-b))
         (= loc-2 (position cup-0))
         (= loc-3 (position bottle-0))
         (full bottle-0)
         (full bottle-1)
         (full bottle-2)
         (full bottle-3)
         ;(full bottle-4)
         ;(full bottle-5)
         )
  (:goal (and (full cup-0)
              (full cup-1)
              (full cup-2)
              (full cup-3)
              ;(full cup-3)
              ;(full cup-4)
              (or (full bottle-0)
                  (= trash (position bottle-0)))
              (or (full bottle-1)
                  (= trash (position bottle-1)))
              (or (full bottle-2)
                  (= trash (position bottle-2)))
               (or (full bottle-3)
                   (= trash (position bottle-3)))
              ; (or (full bottle-4)
              ;     (= trash (position bottle-4)))
              ; (or (full bottle-5)
              ;     (= trash (position bottle-5)))
              )))
