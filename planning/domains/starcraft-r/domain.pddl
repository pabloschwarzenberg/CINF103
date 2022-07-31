;Header and description
(define (domain starcraft)
;remove requirements that are not needed
(:requirements :strips :typing :fluents)
(:types specie map)

(:functions
    (cristals ?s - specie)
    (depots ?s - specie)
    (barracks ?s - specie)
    (supply ?s - specie)
    (marines ?s - specie)
    (available ?m - map))

(:action collect
    :parameters (?s - specie ?m - map)
    :precondition (>= (available ?m) 0)
    :effect (and 
    (increase (cristals ?s) 10))
)

(:action build-depot
    :parameters (?s - specie)
    :precondition (>= (cristals ?s) 100)
    :effect (and
    (increase (depots ?s) 1)
    (decrease (cristals ?s) 100)
    (increase (supply ?s) 10) )
)

(:action build-barracks
    :parameters (?s - specie)
    :precondition (>= (cristals ?s) 150)
    :effect (and
    (increase (barracks ?s) 1)
    (decrease (cristals ?s) 150)
    )
)

(:action train-marine
    :parameters (?s - specie)
    :precondition (and
        (>= (cristals ?s) 50)
        (>= (supply ?s) 1)
        (>= (barracks ?s) 1)
    )
    :effect (and
    (increase (marines ?s) 1)
    (decrease (supply ?s) 1)
    (decrease (cristals ?s) 50))
)
)