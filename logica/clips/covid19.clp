(deftemplate Paciente
	 (field nombre)
     (field pcr)
     (field temperatura)
     (multifield sintomas))

(deftemplate Diagnostico
	(field nombre)
	(field enfermedad))     

(deffacts Pacientes
     (Paciente (nombre Juan) (pcr no) (temperatura 37) (sintomas dolor_cabeza tos perdida_olfato))
     (Paciente (nombre Jose) (pcr no) (temperatura 39) (sintomas tos erdida_gusto))
     (Paciente (nombre Luis) (pcr positivo) (temperatura 39) (sintomas dolor_garganta dolor_cabeza)))

(defrule rule1
     (Paciente (nombre ?N) (pcr positivo))
      =>
     (printout t crlf ?N " queda en cuarentena" crlf)
     (assert (Diagnostico (nombre ?N) (enfermedad covid19))))
     
(defrule rule2
	 (Paciente (nombre ?N) (temperatura ?T) (sintomas $? tos $?))
	 (test (> ?T 38))
	 =>
	 (assert (Diagnostico (nombre ?N) (enfermedad covid19))))
	 
(defrule rule3
	 (Paciente (nombre ?N) (sintomas ? ? ?))
	 =>
	 (assert (Diagnostico (nombre ?N) (enfermedad covid19))))