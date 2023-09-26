(define (domain automated-drone-delivery)
	
	(:requirements :typing :fluents :durative-actions)

	(:types drone package location)

	(:predicates
		(drone-empty ?d - drone)
		(holding ?d - drone ?p - package)
		(at-drone ?d - drone ?l - location)
		(at-package ?p - package ?l - location)
		(is-warehouse ?l - location))
	
	(:functions
	    (load-time)
	    (move-time ?from ?to - location)
	    (weight ?p - package)
	    (capacity)
	    (charge ?d - drone))

	(:durative-action LOAD
		:parameters (?d - drone ?p - package ?l - location)
		:duration (= ?duration(load-time))
		:condition (and (over all (at-drone ?d ?l))
						(at start(drone-empty ?d))
						(at start(at-package ?p ?l))
						(over all(is-warehouse ?l)))
		:effect (and (at end(holding ?d ?p))
					 (at start(not (drone-empty ?d)))
					 (at start(not (at-package ?p ?l)))))

	(:durative-action UNLOAD
		:parameters (?d - drone ?p - package ?l - location)
		:duration (= ?duration(load-time))
		:condition (and (over all(at-drone ?d ?l))
						(at start(holding ?d ?p)))
		:effect (and (at start(not (holding ?d ?p)))
					 (at end(drone-empty ?d))
					 (at end(at-package ?p ?l))))

	(:durative-action DELIVER
		:parameters (?d - drone ?p - package ?from ?to - location)
		:duration (= ?duration(move-time ?from ?to))
		:condition (and (at start(at-drone ?d ?from))
						(over all(holding ?d ?p))
						(over all(is-warehouse ?from))
						(at start(>= (charge ?d) (+ (* (move-time ?from ?to) (+ 1 (/ (weight ?p) 100))) (move-time ?from ?to)))))
		:effect (and (at end(at-drone ?d ?to))
					 (at start(not (at-drone ?d ?from)))
					 (at end(decrease (charge ?d) (* (move-time ?from ?to) (+ 1 (/ (weight ?p) 100)))))))

	(:durative-action RETURN
		:parameters (?d - drone ?from ?to - location)
		:duration (= ?duration(move-time ?from ?to))
		:condition (and (at start(at-drone ?d ?from))
						(over all(drone-empty ?d))
						(over all(is-warehouse ?to)))
		:effect (and (at end(at-drone ?d ?to))
					 (at start(not (at-drone ?d ?from)))
					 (at end(decrease (charge ?d) (move-time ?from ?to)))))

	(:durative-action RECHARGE
		:parameters (?d - drone ?l - location)
		:duration (= ?duration (/ (- (capacity) (charge ?d)) 10))
		:condition (and (at start(is-warehouse ?l))
						(at start(at-drone ?d ?l))
						(over all(drone-empty ?d)))
		:effect (at end(assign (charge ?d) (capacity))))
)