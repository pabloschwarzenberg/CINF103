;Header and description
(define (domain starcraft)
;remove requirements that are not needed
(:requirements :typing :durative-actions :fluents :negative-preconditions)
(:types specie map)

(:predicates
    (has-barracks ?s - specie)
    (idle ?s - specie)
)

(:functions
    (cristals ?s - specie)
    (depots ?s - specie)
    (barracks ?s - specie)
    (supply ?s - specie)
    (marines ?s - specie)
    (available ?m - map))

(:durative-action collect
    :parameters (?s - specie ?m - map)
    :duration (= ?duration 1)
    :condition (and
        (at start (>= (available ?m) 0))
        (at start (idle ?s))
    )
    :effect (and
        (at start (not(idle ?s))) 
        (at start (decrease (available ?m) 10))
        (at end (increase (cristals ?s) 10))
        (at end (idle ?s))
    )
)

(:durative-action build-depot
    :parameters (?s - specie)
    :duration (= ?duration 40)
    :condition  
        (at start (>= (cristals ?s) 100))
    :effect (and
        (at start (decrease (cristals ?s) 100))
        (at end (increase (depots ?s) 1))
        (at end (increase (supply ?s) 10))
    )
)

(:durative-action build-barracks
    :parameters (?s - specie)
    :duration (= ?duration 80)
    :condition  
        (at start (>= (cristals ?s) 150))
    :effect (and
        (at start (decrease (cristals ?s) 150))
        (at end (increase (barracks ?s) 1))
        (at end (has-barracks ?s))
    )
)

(:durative-action train-marine
    :parameters (?s - specie)
    :duration (= ?duration 20)
    :condition (and
        (at start (>= (cristals ?s) 50))
        (at start (>= (supply ?s) 1))
        (over all (has-barracks ?s))
    )
    :effect (and
        (at start (decrease (supply ?s) 1))
        (at start (decrease (cristals ?s) 50))
        (at end (increase (marines ?s) 1))
    )
)
)