;Header and description

(define (domain mecanica)

;remove requirements that are not needed
(:requirements :strips :fluents)

; un-comment following line if constants are needed
(:constants suelo)

(:predicates ;todo: define predicates here
(En ?x ?y)
(Libre ?x)
)

(:action Quitar
    :parameters (?neumatico ?lugar)
    :precondition (En ?neumatico ?lugar)
    :effect (and
    (not (En ?neumatico ?lugar))
    (En ?neumatico suelo)
    (Libre ?lugar)
    )
)

(:action Poner :parameters (?neumatico ?lugar)
:precondition
(and (En ?neumatico suelo)
(Libre ?lugar))
:effect
 (and (not (En ?neumatico suelo))
(En ?neumatico ?lugar)
(not (Libre ?lugar))))
)