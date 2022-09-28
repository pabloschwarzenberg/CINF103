(define (problem reemplazar_neumatico_pinchado) (:domain mecanica)
(:objects 
pinchado repuesto eje maletero
)

(:init
    (En pinchado eje)
    (En repuesto maletero)
)

(:goal 
    (and (En repuesto eje)
    (En pinchado maletero))
))