(define (problem play-basic) (:domain starcraft)
(:objects
    terran - specie
    level1 - map
)

(:init
    (= (cristals terran) 0)
    (= (depots terran) 0)
    (= (barracks terran) 0)
    (= (supply terran) 0)
    (= (marines terran) 0)
    (= (available level1) 10000)
)

(:goal 
    (= (marines terran) 5)
)
)