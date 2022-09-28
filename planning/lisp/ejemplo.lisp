(defun sum (a b) (+ a b))

(defun factorial (n) (if (= n 1) 1 (* n (factorial (- n 1)))))

(setq n (read))
(princ "El factorial es:")
(write (factorial n))