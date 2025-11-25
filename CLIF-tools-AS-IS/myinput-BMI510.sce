(cl:comment '
Axiomatization of change in BFO2020 as described in the FOIS 2025 paper
Towards Representing Change in the BFO
Authors: Werner Ceusters, Alan Ruttenberg
version 2025/06/29 - work in progress

This work is licensed under a Creative Commons "Attribution 4.0 International" license:
https://creativecommons.org/licengses/by/4.0/

History:
 - Since 2025/03/15:
 -	corrected ett-03: added process-boundary as exclusion next to process
 -  corrected insce-03: added that t1 and t2 may not be identical and that c must exist at t2
 -  time indexing removed from happens-in as it is between occurrents
To be done:
	- distinct declarations including with BFO2020
	- disjoint declarations
	- further subtyping of changes (increases, decreases, motions, part loss and acquisitions, ...)
	- tighter integration with BFO2020 relations
	- ...'

 (cl:text

  (cl:ttl Testing Scenarios for BFO2020 extension for changes

   (cl:outdiscourse 
		change-profile-of
		changes-to
		continuant-part-of
		mono-sequential-change-of
		exists-at
		exists-throughout
		gains-type
		happens-in
		happens-throughout
		happens-to
		has-first-instant
		has-last-instant
		individuates-at
		inheres-in
		instance-of
		is-sequence-part-of
		loses-type
		occupies-temporal-region
		occupies-spatial-region 
		occurrent-part-of
		overlaps
		participates-in
		particular
		precedes
		proper-temporal-part-of
		proper-occurrent-part-of
		replaces-type
		temporal-part-of
		temporal-layer-of
		ceases-to-exist-at
		uni-equivalent
		universal

 )


(cl:comment ' ------- PROSPECTED MODELS ------- ' )





(cl:comment ' 


	(cl:comment "A car has a part, then loses it and this is compositional change [sce-020]"
	   (and 
	        (instance-of car1 object tt)
			(instance-of wheel1 object tt)
			(instance-of comp1 compositional-change tt)
			(has-first-instant tt temp1)  
			(has-last-instant tt temp2)
			(happens-to comp1 car1 tt)
	        (continuant-part-of wheel1 car1 temp1) 
		    (not(continuant-part-of wheel1 car1 temp2))

		)    
	)



 (cl:comment ".......c1 [dec-000]"  
	   (and (particular c1) 
	        (particular t1) 
			(particular x1)
	    )
 )


	(cl:comment "A car has a quality, then loses it and this is qualitative change [sce-024]"
	   (and 
	        (instance-of car1 object t)
			(instance-of q1 disposition t)
			(instance-of c qualitative-change t)
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c car1 t)
	        (inheres-in q1 car1 t1) 
		    (not(inheres-in q1 car1 t2))

		)    
	)


	(cl:comment "A car has a disposition, then loses it and this is dispositional change [sce-025]"
	   (and 
	        (instance-of car1 object t)
			(instance-of d1 disposition t)
			(instance-of c dispositional-change t)
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c car1 t)
	        (inheres-in d1 car1 t1) 
		    (not(inheres-in d1 car1 t2))

		)    
	)

  ' )
  
	(cl:comment "Bob Dylan gains the role of Nobel Prize nominee, but does not participate in the process of notimation[sce-026]"
	   (and 
	        (instance-of bd object t)
			(instance-of r1 role t)
            (instance-of p1 process t)
			(instance-of c role-gain t) 
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c bd t)
	        (inheres-in r1 bd) 
			(not (exists-at r1 t1))
			(exists-at r1 t2) 
		    (not(participates-in bd p1 t))

		)    
	)









(cl:comment ' ------- PROSPECTED ANTIMODELS ------- ' )




(cl:comment ' 

	(cl:comment "A spatial region has a part, then loses it and this is compositional change [sce-021]"
	   (and 
	        (instance-of s1 spatial-region t)
			(instance-of w1 object t)
			(instance-of c compositional-change t)
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c s1 t)
	        (continuant-part-of w1 s1 t1) 
		    (not(continuant-part-of w1 s1 t2))

		)    
	)

(cl:comment "A quality has a part, then loses it and this is compositional change [sce-022]"
	   (and 
	        (instance-of q1 quality t)
			(instance-of w1 object t)
			(instance-of c compositional-change t)
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c q1 t)
	        (continuant-part-of w1 q1 t1) 
		    (not(continuant-part-of w1 q1 t2))

		)    
	)

	(cl:comment "A car has a part, then loses it and this is NOT compositional change [sce-023]"
	   (and 
	        (instance-of car1 object t)
			(instance-of w1 object t)
			(not (instance-of c compositional-change t) )
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c car1 t)
	        (continuant-part-of w1 car1 t1) 
		    (not(continuant-part-of w1 car1 t2))

		)    
	)

	(cl:comment "Bob Dylan is in a role gain change,, but gains no role[sce-027]"
	   (and 
	        (instance-of bd object t)
			(instance-of r1 role t)
			(instance-of c role-gain t) 
			(has-first-instant t t1)  
			(has-last-instant t t2)
			(happens-to c bd t)
			(not( exists (x)  
			        (and (instance-of x role t)
					     (inheres-in x bd) 
			             (not (exists-at r1 t1))
			             (exists-at r1 t2)   ) ))
		)  



  ' )






)))


