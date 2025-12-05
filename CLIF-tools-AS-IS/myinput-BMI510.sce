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
		proper-continuant-part-of 
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






	(cl:comment "A car has a part, then loses it and this is compositional change [sce-020]"
	   (and 
	        (instance-of car1 object tt)
			(instance-of wheel1 object tt)
			(instance-of tt temporal-interval tt)
			(instance-of comp1 compositional-change tt)
			(has-first-instant tt temp1)  
			(has-last-instant tt temp2)
			(happens-to comp1 car1 tt)
	        (proper-continuant-part-of wheel1 car1 temp1) 
		    (not(proper-continuant-part-of wheel1 car1 temp2))
			(forall (ch) (if (happens-to ch car1 tt) (= ch comp1)) )

		)    
	)





)))


