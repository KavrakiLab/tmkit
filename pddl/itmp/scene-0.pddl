(define (problem asdf)
  (:domain itmp)
  (:objects cup0 - cup cup1 - cup
            dripper0 - dripper
            french-roast - ingredient decaf - ingredient
            bowl0 - bowl bowl1 - bowl
            x - location y - location z - location )
  (:init (at cup0 x) (occupied x)
         (at cup1 y) (occupied y)
         (at dripper0 z) (occupied z)
         (contains bowl0 french-roast)
         (contains bowl1 decaf)
         (empty cup0)
         (empty cup1)
         (empty dripper0)
         (hand-empty)
         )
  (:goal (and (contains-beverage cup1 french-roast)
              (not (covered cup1))
              (contains-beverage cup0 decaf)
              (not (covered cup0))
              )))
