(define (problem pb_logistics)
  (:domain logistics)

  (:objects
     plane1 - airplane
     plane2 - airplane
     truck1 - truck
     truck2 - truck
     cdg lhr - airport
     south north - location
     paris london - city
     p1 p2 - package)

  (:init (in-city cdg paris)
         (in-city lhr london)
         (in-city north paris)
         (in-city south paris)
         (at plane1 lhr)
         (at plane2 lhr)
         (at truck1 cdg)
         (at truck2 cdg)
         (at p1 lhr)
         (at p2 lhr)
  )

  (:goal (and (at p1 south) (at p2 south)))
)
