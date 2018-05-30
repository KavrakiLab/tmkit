(define (problem air)
  (:domain air-cargo)
  (:objects cargo-0 cargo-1 cargo-2 - cargo
            plane-0 plane-1 plane-2 - plane
            ATL SFO - airport)
  (:init
         (at plane-0 ATL)
         (at plane-1 SFO)
         (at cargo-0 ATL)
         (at cargo-1 SFO))
  (:goal (and (at cargo-0 SFO)
              (at cargo-1 ATL))))
