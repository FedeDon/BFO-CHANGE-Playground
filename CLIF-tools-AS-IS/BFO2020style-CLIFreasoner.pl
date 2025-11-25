/* history
TODO: mpp with all remaining non-fullfilled conditionals?
TODO: implement resolution ideas in current forward-chaining approach?
2025-11-15: improvement: detect scenario-input in kowalski input
2025-04-10: bug fix
2024-01-24: bug fix. It was already checked whether an input fact duplicates an ontology fact, but not
					 whether it contradicts such fact or a generalization
2024-01-02: improvement: unify identities in input scenarios
2024-01-01: bug fix: in 'false_fact'
2023-12-24: improvement: elimination of double rules without skolem constants
*/
:- include("CLIFreasonerinit.txt").			%% contains input- and output parameters
:- style_check(+singleton).
:- set_prolog_flag(occurs_check, true).
:- set_prolog_flag(stack_limit,  34_359_738_368).				
:- dynamic r/6,				% rule from Kowalski file
							%	arg1=index of rule (integer)
							%	arg2=number of antecedents (integer); 0 = true, indicating the consequents are facts
							%	arg3=list of indices of skolem functions figuring in the rule consequents
							%	arg4=list of indices of skolem functions figuring in the rule antecedents
							%	arg5=axiom index from CLIF-file, i.e. anything between [...] if anything at all
							%	arg6='kow(X,Y)' where
							%			X = 'true' or 'if(L)' where L is list of predicates in list format [functor, arg, arg, ...]
							%			Y = 'false' or 'then(P)' or 'then_or(L)' with L as above
		   rr/6,			% like r/6 but with non-unique skolem functions 
		   p/1,				% unground predicate pattern from the antecedent or consequent of an r/6
		   eqp/5,			% equivalent predicates
							%	arg1=axiomID in which the one to remove
							%	arg2=equivalent predicate to remove
							%	arg3=axiomID in which the one to keep
							%	arg4=equivalent predicate to keep
							%	arg5=c(ertain) / p(ossible)
		   pax/3,			%% predicate use in axiom
							%	arg1=Predicate name
							%	arg2=count of axioms used in
							%	arg3=axiom list
		   o_rel/1,			% label of a relation in the ontology
		   o_c/1,			% non-relation constant in the ontology
		   i_oc/1,			% constant from input scenario identical with an ontology constant
		   i_orel/1,		% relation from input scenario identical with an ontology relation
		   i_noc/1,			% constant from input scenario not identical with any ontology constant
		   i_nor/1,			% relation from input scenario not identical with any ontology relation
		   rilr/7,			% info about p/1 in some r/6: 
							%		arg1=predicate pattern,
							%		arg2=index number of r/6, 
							%		arg3=number of antecedents in r/6,
							%		arg4=number of consequents in rule (0=falsehood rule),
							%		arg5=indices of skolem constants the rule would generate left to right ([]=none),
							%		arg6=position of p/1 in antecedent list, first = 1.
							%		arg7=CLIF axiom index
		   rirl/7,			% info about p/1 in some r/6: 
							%		arg1=predicate pattern,
							%		arg2=index number of r/6, 
							%		arg3=number of antecedents in r/6,
							%		arg4=number of consequents in rule (0=falsehood rule),
							%		arg5=indices of skolem constants the rule would generate right to left ([]=none),
							%		arg6=position of p/1 in consequent list, first = 1.
							%		arg7=CLIF axiom index
		   m/4,				% info about p/1: 	arg1 = the predicate type (= )
							%					arg2 is the max number of antecedents in any r/6 of type arg4 in which p/1 is antecedent
							%					arg3 is the number of rules of type arg4 in which p/1 is antecedent
							%					arg4 = rule type: 0 for falsehood rules, 1 for then-rules, 2 for then_or rules
		   f/7,				% derived or inputted fact
							%	arg1=the fact in [predicate,arg1, arg2, ....] format
							%	arg2=order in which inputted or generated, unique over all worlds
							%	arg3=0 if it is proven, -1 when it is proven false, a positive integer when assumed
							%	arg4=condition under which true or false when insufficient info available
							%	arg5=number of args in arg1
							%	arg6=the 'world' in which the fact is valid as indicated in arg3. World 0 is universally correct and accessible.
							%	arg7=fact number in the world of arg6
		   d/6,				% info about f/7: 	arg1=the fact (== arg1 of f/7)
							% 					arg2=list of r/6 indexes that derive f/7. Last element is first generator.
							%					arg3=list of r/6 indexes of rules in which f/7 is used,
							%					arg4=[[R,M,I|[F]]]|...]  where R is the rule that fired. M the reasoning mode,
							%											I the axiom index and F the list of facts that made R fire.
							%					arg5=the index of the fact (= arg2 in f/7)
							%					arg6=the world in which f/7 is valid
		   counter/2,		% global counter: counter(name, count)
							% Counters in use:
							%	facts(World)	 facts in World
							%	facts			 facts in all worlds
							%	pfacts(World)	 positive facts in World
							%	nfacts(World)	 negative facts in World
							%	mfacts(World)	 possible facts in World
							%	rules(World)	 rule firings in World
							%	skolem(0)	 	 number of skolem functions/constants in World
							%	skcycle(H)		 number of times skolem function H was prevented to generate a skolem constant
							%	na(RN1, RN2)	 number of times rule RN1 was prevented to fire by rule RN2 
							%	abp				 assumption based proofs
							%	rule_block(RN,Mod,Index)	possible world larger than base world
							%	or				 index for remaining then_or alternatives
							%	e(N,World)		 how often a sklome function [e,N,...] has been created in base world (0) or
							%						during alternative world reasoning (1)
		   ru/2,			% info about r/6: arg2 = number of times it fired
		   inconsistent/4,	% contains a list of facts that satisfy a rule with false or inconsistent conclusion.
							%	arg1=list of inconsistent facts
							%	arg2=list with three members:
							%		m1=number of rule which identified the inconsistency
							%		m2=fact, if any, that selected the rule which led to an inconsistency
							%		m3=inconsistent facts
							%	arg3=world under scrutiny
							%	arg4=index of the source axiom in CLIF file
		   skolem/2,		% numbering skolem-constants (1=index,2=full form)
		   lif/3,			% label in fact
							%	arg1=the label
							%	arg2=absolute fact number (arg2 in f/7)
							%	arg3=World
		   lbl/2,			% label: any label used in fact
							%	arg1=label
							%	arg2=World
		   pf/7,			% short-skolemized version of f/7, not used for reasoning, only for output
		   t/1,				% input instance data
		   pl/1,			% arity of predicate with greatest arity
		   thor/5,			% stores a list of then_or rule consequences with already proven conditions
							%	arg1=rule number
							%	arg2=list of remaining alternatives (may be equal to arg3)
							%	arg3=all alternatives
							%	arg4=indices of supporting facts
							%	arg5=index from CLIF file
		   ff/7,			% intermediate variable for derivation proofs in mtta mode ff(F,TFA,Rn,Ax,Mod,SFnew,BaseNew)
							%	arg1=fact
							%	arg2=true (0) or false (-1)
							%	arg3=rule number of firing rule
							%	arg4=axiom index
							%	arg5=derivation mode
							%	arg6=list of support facts in alternative world
							%	arg7=list of support facts in base world
		   ffn/3,
		   ffx/1,			% semafoor to prevend infinite loop in alternative worlds computation
		   idem/4,			% stores identicals 
							%	arg1=0/-1/...
							%	arg2=identity to check
							%	arg3=identity to use
							%	arg4=world
		   todo/3,			% part of speed-up mechanism: keep tracks of which facts to process
							%	arg1=reasoning mode, arg2=fact number, arg3=world
		   skcycle/2,		% stores occurrences of facts prevented to form due to skolem function cycle
		   blocked/1,		% semafoor for further processing in possible world stopped
		   logfile/1,		% output stream for log file
		   assumed/1,
	% from the CLIFreasonerinit file
		   ontologies/1,
		   scenario/1,
		   inputdata/1,
		   outputfiles/1,
		   skolem_level/1,
		   sk_cycle_level/1,
		   max_ante_arg_matches/1.
		   
:-writeln("BFO2020 Style CLIF reasoner, Version April 16, 2025").
:-writeln("Copyright: Werner Ceusters. All rights reserved.").
:-writeln("").
:-writeln("Exclusively for use with -kowalski.txt generated by the BFO2020 Style CLIF reasoner with following init-settings:").
:-writeln("   skolem_mode(scoped)").
:-writeln("   variable_mode(unbound)").
:-writeln("").
%:-writeln("Type 'run' to start reasoner.").


run:-
	 writeln("PRE-PROCESSING"),
	 start_conditions_ok(Out),	% Check whether all needed information is present
% from here to next '%end' should ideally move to the parser
	 writeln("Optimizing Kowalski input ..."),
	 write_dupl(Out),
	 detect_equivalent_predicates,	
	 print_eqp(Out),
	 assert(pl(0)),				% initialize arity value
	 list_question_types, 		% process kowalski-input
	 ontology_constants,		% store any constant found in the ontology in appropriate table
% end
	 open_log(Out,Stream),
	 forward(Out),				% do main processing
	 close(Stream),
	 writeln(""),
	 writeln("OUTPUT"),
	 print_skolems(Out),
	 saveData(Out,_),
	 print_rules_used(Out),
	 print_possibilia(Out),		% must stay after print_skolems to eliminate unused skolems in possibilia
	 print_not_added(Out),
	 print_counters(Out),
	 writeln(""),
	 writeln("Press any character key to finish."),
	 get_single_char(_),
	 halt,!.
run:-writeln(""),
	 logfile(Stream),
	 close(Stream),
	 writeln("Press any character key to finish."),
	 get_single_char(_),
	 halt,!.

open_log(Name, Stream):-
    string_concat(Name,"-derivations.txt",File),
	open(File,write,Stream),
	assert(logfile(Stream)),!.


% Check start conditions 
% Arguments:
%	-1: returns outputfile prefix provided in CLIFreasonerinit.txt
start_conditions_ok(Out):-							% for documentation: see CLIFreasonerinit.txt
	write("Checking start conditions ..."),
	( ontologies(X),
	  expand_file_name(X,H),
		( H = [],
		  writeln("Specified ontologies do not exist. Check CLIFreasonerinit.txt for the 'ontologies(\"...\")' parameter."),
		  !,fail
		; 	style_check(-singleton),
			consult_input_files(H),
			(	outputfiles(Out),
				true
			;	writeln("No output specified. Check CLIFreasonerinit.txt for the 'outputfiles(\"...\")' parameter. Defaults now to \"CLR-ANONYMOUS\""),
				Out="CLR-ANONYMOUS"
			),
			(	inputdata(Data),				% for input data in 't([...])' format
				expand_file_name(Data,Input),
				(	Input = [],
					writeln("Specified inputdata do not exist. Check CLIFreasonerinit.txt for the 'inputdata(\"...\")' parameter."),
					!,fail
				;	consult_input_files(Input)
				)
			;	scenario(SCE),					% for input scenarion in Kowalski files
				findall( PosFact,
						 ( r(_,_,_,_,ScenarioID,kow(true,then(PosFact))),
						   string_concat(SCE, _, ScenarioID)
						 ),
						 PosFacts),
				forall(member(PosFact, PosFacts),
						assertz(t([0|PosFact]))),
				findall( NegFact,
						 ( r(_,_,_,_,ScenarioID,kow(if([NegFact]),false)),
						   string_concat(SCE, _, ScenarioID)
						 ),
						 NegFacts),
				forall(member(NegFact, NegFacts),
						assertz(t([-1|NegFact])))
			;	writeln("No input data specified. Check CLIFreasonerinit.txt for the 'inputdata(\"...\")' parameter."),
				!,fail
			),
			(	skolem_level(_)
					-> true
			;	asserta(skolem_level(2))
			),
			(	sk_cycle_level(_)
					-> true
			;	asserta(sk_cycle_level(0))
			),
			(	max_ante_arg_matches(_)
					-> true
			;	asserta(max_ante_arg_matches(5))
			)
		)
	; writeln("No ontologies specified. Check CLIFreasonerinit.txt for the 'ontologies(\"...\")' parameter."),
	  !,fail
	),
	writeln("OK!"),!.

consult_input_files([]):-style_check(+singleton).
consult_input_files([H|T]):-
	consult(H),
	!,consult_input_files(T).




%------------ 	PREPARATION: get predicate templates from Kowalski rules and compute some variables such as tally of antecedents, 
%				consequents, occurrence of predicate templates, etc

list_question_types:-					% process kowalski-input
	r(N, Cs, Sk, Ska, Axiom, kow(if(IF), Con)),		% read first kowalski-rule
	questions(rilr, 1, Cs, N, IF, Con, Sk, Axiom),	% separate the rules' antecedents in predicate templates and store some optimization parameters
	(	Con = then(T)				
		->	questions(rirl, 1, Cs, N, [T], IF, Ska, Axiom)
	;	Con = then_or(T)
		->	questions(rirl, 1, Cs, N, T, IF, Ska, Axiom)
	),
	fail.								% next rule
list_question_types:-					% when all rules are processed
	p(Q),								% read first predicate template (it is a template because it contains variables)
	p_length(Q),
	rule_types(Q),						% get number of rules and max number of antecedents appearing therein for predicate template Q
	fail.								% next predicate
list_question_types:-!.

p_length(Q):-
	length(Q,L),
	pl(ML),
	(	L > ML,
		retract(pl(_)),
		assert(pl(L))
	;	true),!.



questions(_,_,_, _, [],_,_,_):-!.		% return to 'list_question_types' when all the rule's antecedents are processed
questions(LRorRL ,Pos, Cs, N, [Q|R], Con, Sk, Axiom):-		% process the first antecedent Q
	\+ground(Q),											% but only when it contains variables
	(	LRorRL == rilr
		->	predicates(Con, NC),									% count number of predicates	
			asserta_once(rilr(Q, N, Cs, NC, Sk, Pos, Axiom))	% store in a rilr() structure:
								% 1) the predicate, 
								% 2) the rule number, 
								% 3) the number of antecedents in that rule, 
								% 4) the number of consequents, 
								% 5) list of index numbers of skolem functions in the rule's consequents, [] if none
								% 6) position of p/1 in antecedent list, first = 1.
								% 7) Axiom index
	;	predicates([Q|R], NC),
		asserta_once(rirl(Q, N, Cs, NC, Sk, Pos, Axiom))		% similar for right to left application, e.g. tollendo tollens
	),
	findall(P,p(P),Ps),
	(variant_member(Q,Ps)
		-> true
	; asserta(p(Q))),							% store the predicate template in a p()-structure
	plus(Pos,1,PosNext),						% increment the position counter for the predicate abiout which ri/6 contains optimization info
	!,questions(LRorRL, PosNext, Cs, N, R, Con, Sk, Axiom).	% next antecedent
questions(LRorRL, Pos, Cs, N, [Q|R], Con, Sk, Axiom):-			% skip all ground antecedents.
	ground(Q),
	plus(Pos,1,PosNext),						% increment the position counter for the predicate about which ri/6 contains optimization info
	!,questions(LRorRL, PosNext, Cs, N, R, Con, Sk, Axiom).

predicates(false, 0):-!.	% i,o	% no predicates when antecedents resolve to false
predicates(then(_), 1):-!.			% one consequent for then-rule
predicates(then_or(T), NC):-		% more predicates for then-or rules, so count them.
	length(T,NC),!.
predicates(T, NC):-		% more predicates for then-or rules, so count them.
	length(T,NC),!.

variant_member(X,[Y|_]):-X=@=Y,!.
variant_member(X,[_|R]):-!,
	variant_member(X,R).

rule_types(Q):-rule_type(Q,0),fail.	% get number of falsehood rules and max number of antecedents appearing therein for predicate template Q
rule_types(Q):-rule_type(Q,1),fail.	% get number of then-rules and max number of antecedents appearing therein for predicate template Q
rule_types(Q):-rule_type(Q,2),fail.	% get number of then_or rules and max number of antecedents appearing therein for predicate template Q

rule_type(Q, N):-		% i,o
	N<2,
	findall(X,rilr(Q, _, X, N,_,_,_),Xs),	% find all rules of type N in which this predicate is one of the antecedents
	length(Xs,XL),						% tally such rules
	max_list(Xs,M),						% get the maximum number of antecedents in any of these rules per rule-type (4th argument of rilr() )
	asserta(m(Q, M, XL, N)),!.			% store in a m()-strcuture: 1) the antedecent Q, 2) the max number of antecedents, 3) the tally of rules with Q, 4) rule-type
rule_type(Q, 2):-
	findall(X,or_rule(Q, X),Xs),		% find all rules in which this predicate is one of the antecedents
	length(Xs,XL),						% tally such rules
	max_list(Xs,M),						% get the maximum number of antecedents in any of these rules per rule-type (4th argument of rilr() )
	asserta(m(Q, M, XL, 2)),!.			% store in a m()-structure: 1) the antedecent Q, 2) the max number of antecedents, 3) the tally of rules with Q, 4) rule-type
	
or_rule(Q, X):-				% i,o		% get number of antecedents of then_or-rule.
	rilr(Q, _, X, N, _, _,_),
	N > 1.


% create a list of constants used in the ontologies
ontology_constants:-
	p([Rel|Args]),
	asserta_once(o_rel(Rel)),
	member(X,Args),
	ground(X),
	asserta_once(o_c(X)),
	fail.
% assess whether constants have double use relation and non-relation constant
ontology_constants:-
	o_rel(X),
	o_c(X),
	writeln(""),
	write("Label  - "),
	write(X),
	write("  - is used both for a relation and for a domain individual in the (combined) ontology."),
	writeln("Press any character key to continue."),
	get_single_char(_),
	fail.
ontology_constants:-!.



% i
write_dupl(Name):-
   string_concat(Name,"-OPTIMIZATIONS.txt",File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       duplicate_rules(Out),
       close(Out)),
   !.

% ++1: output stream
%% Iterate over all rules to find the ones which have the same conditions and consequences	
duplicate_rules(Out):-
	r(_, _, _, _, _, Kow),								% BP1: pick the disjunctions of the first rule on the rule stack
	setof([N, Axiom], r(N, _, _, _, Axiom, Kow), Xs),	% find the rule number and axiom ID of all rules with these disjunctions
	length(Xs, L), L>1,									% if there are less than 2, bacltrack to BP1, otherwise ...
	writeln(Out,""),
	ana_dup(Out,Xs,1),									% process the list of rule-number axiom ID pairs									
	fail.												% backtrack to BP1
duplicate_rules(Out):-
	rr(_, _, _, _, _, Term),
	setof([N, Axiom], rr(N, _, _, _, Axiom, Term), Xs),
	length(Xs, L),
	L>1,
	writeln(Out,""),
	ana_dup(Out,Xs,2),
	fail.
duplicate_rules(_):-!.

%% Not used yet
sim_rule(N1, Axiom1, N2, Axiom2):-
	r(N1, _, _, _, Axiom1, Term1),
	r(N2, _, _, _, Axiom2, Term2),
	N1 \== N2,
	Term1 =@= Term2.
%%Not used yet
subsumes_rule(N1,Axiom1,N2,Axiom2):-
	r(N1, _, _, _, Axiom1, Term1),
	r(N2, _, _, _, Axiom2, Term2),
	N1\==N2,
	subsumes_term(Term1,Term2).

ana_dup(Out,D, Type):-
	forall(member([R,A],D),
			((	Type == 1 -> r(R, _, _, _, A, Kow); Type == 2 -> rr(R, _, _, _, A, Kow)	),
			 numbervars(Kow,0,_),
			 write_term(Out,Kow,[quoted(true),numbervars(true),nl(true)]))),
	setof(Axiom, member(Axiom,D), Axioms),
	forall(member(X, Axioms), (write(Out,X), write(Out," "))),
	writeln(Out,""),
	(	Type == 1 ->
		D = [_|Remove],
		forall(member(Axiom,Remove), 
				(Axiom = [R,A],
				retract(r(R,_,_,_,A,Kow)), 
				write(Out,Axiom), writeln(Out, " removed.")))
	; true).


detect_equivalent_predicates:-
	r(_,1,[],[],AxID1,kow(if([[PA|A]]),then([PC|C]))),	% pick the first rule with one antecedent and one conclusion
	( \+eqp(AxID1,_,_,_,_), \+eqp(_,_,AxID1,_,_) ),			% if the axiom to which the rule belongs has not yet been processed
	r(_,1,[],[],AxID2,kow(if([[PC|C]]),then([PA|A]))),	% pick an inverse rule from the first rule
	length(A,AL),
	length(C,CL),
	AL == CL,											% if the two predicates have the same number of arguments
	term_variables(A,AV),								% isolate the variables from the 1st rule's atecedent 
	length(AV, AVL),
	term_variables(C,CV),								% isolate the variables from the 1st rule's consequent 
	length(CV, CVL),
	AVL == CVL,											% if the two predicates have the same number of variables
	sort(AV,AVs),										
	sort(CV,CVs),										% idem for the consequent
	PA\==PC,											% if the predicates are different
	AVs =@= CVs,										% if the variables figuring in antecedent and consequent are equivalent
	pax(PA,PAC,_),										% get usage count of PA
	pax(PC,PCC,_),										% get usage count of PC
	( AxID1 == AxID2 -> CT = c ; CT = p ),
	( PAC >= PCC										% store the predicate with lowest occurrence is the one to replace									
		->	assertz(eqp(AxID2,PC,AxID1,PA,CT))
	;	assertz(eqp(AxID1,PA,AxID2,PC,CT))
	),
	fail.												% backtrack over all rules
detect_equivalent_predicates:-!.


print_eqp(Name):-
   string_concat(Name,"-OPTIMIZATIONS.txt",File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, append, Out),
       eqp_output(Out),
       close(Out)),
   !.

eqp_output(Out):-
	writeln(Out,""),
	writeln(Out, "Detected inverse relations"),
	eqp(AxID,PC,AxID,PA,c),
	writeln(Out, eqp(AxID,PC,AxID,PA,c)),
	fail.
eqp_output(_):-
	\+eqp(_,_,_,_,p),!.
eqp_output(Out):-
	writeln(Out,""),
	writeln(Out, "Possible inverse relations"),
	eqp(AxID1,PC,AxID2,PA,p),
	writeln(Out, eqp(AxID1,PC,AxID2,PA,p)),
	fail.
eqp_output(_):-!.

	
/*
unify_rules:-
	r(N1, _, _, _, Axiom1, kow(IF1, Con1)),		% read first kowalski-rule
	r(N2, _, _, _, Axiom2, kow(IF2, Con2)),		% read other kowalski-rule
		
*/



%--------- data input
forward(Name):-							% accept facts as input
	writeln("Reading data input ..."),
	read_input,
	findall(A, f(_,A,_,_,_,_,_), As),
	asserta(all_input(As)),
	fact_count(0, Nfacts),
	(	Nfacts > 0
		->	writeln(""),
			writeln("REASONING"),
%			writeln(""),trace,
			increase_by(or,-10,_),					% set unresolved then_or alternative index to -9 so first will be -1
			(	time(process(1, 0, Nfacts)),		% start the inference loop with rules with one antecedent. Don't use "->" !!! 
					writeln(""),writeln("Listing remaining alternatives ..."),
					sure_ors(0, end),
					\+inconsistent(_,_,_,_)
			;	inconsistent(X, [Rule, Then, Facts], 0, Index)				% inconsistency found
				->	writeln(""),
					write("INCONSISTENCY FOUND: "), writeln(X),
					write("Rule: "), writeln(Rule),
					write("Axiom: "), writeln(Index),
					writeln(Then),
					write("Inconsistent facts: "), writeln(Facts),
					getFactNo(Facts,[],FactNos),
					counter(facts,LastFact),
					plus(LastFact,1,Error),
					asserta(pf([inconsistency], Error, -2, 0,0,0,0)),
					asserta(d(_,_,_,[[Rule|[Index|[inc|FactNos]]]],Error,0)),
					prft([Error|FactNos],[],[],FList),				% conflicting facts used as seeds to retrieve facts that caused them
					write_inconsistency_proof(Name,FList),
					print_skolems(Name),
					writeln("Press any character key to finish."),
					get_single_char(_),
					halt,!
			)
	;	writeln("NO FACTS FOUND in input!"),
		writeln("Press any character key to finish."),
		get_single_char(_),
		halt,!
	),!.	


getFactNo([],In,Out):-
	flatten(In, In1),
	sort(In1, Out),!.
getFactNo([H|T],In,Out):-
	findall(X, f(H,X,_,_,_,0,_),Xs),
	!,getFactNo(T,[Xs|In],Out).

getFactsThroughFactno([],In,In):-!.
getFactsThroughFactno([H|R],In,Out):-
	f(F,H,_,_,_,0,_),
	!, getFactsThroughFactno(R,[F|In],Out).


% i,i,o
why_rule_fired(FactNo,World,[RuleLine|Why]):-	
	d(_, _, _, Mots,FactNo,World),
	length(Mots,ML),
	nth1(ML,Mots,Mot),
	[RuleLine|Why]=Mot,
	!.
	
prft([], In, [], Out):-			% i,i,i,o	  walks a linearized tree of facts that caused rules to fire
	sort(In,Out1),							% remove multiply applying facts by sorting lowest to higher
	reverse(Out1,Out),!.					% reverse order so proof tree (prft) has root on top
prft([FactNo], In, [], Out):-
	why_rule_fired(FactNo,0,[_|[_|[_|Why]]]),
	!, prft(Why, [FactNo|In], [], Out).
prft([FactNo|T], In, R, Out):-
	why_rule_fired(FactNo,0,[_|[_|[_|Why]]]),
	flatten([Why,R], Next),
	!, prft(T, [FactNo|In], Next, Out).
prft([], In, [H|R], Out):-		
	!, prft([H], In, R, Out).


%  o_rel/1,			% label of a relation in the ontology
%  o_c/1,			% non-relation constant in the ontology
%  i_oc/1,			% constant from input scenario identical with an ontology constant
%  i_orel/1,		% relation from input scenario identical with an ontology relation
%  i_noc/1,			% constant from input scenario not identical with any ontology constant
%  i_nor/1,			% relation from input scenario not identical with any ontology relation
	
read_input:-
	(	t([TFA|[Rel1|Args1]]),
		(	\+ scenario(_)
				-> terms_to_atoms(Args1,[],Args),
				   term_to_atom(Rel1,Rel)
		;	Rel = Rel1,
			Args = Args1
		),
		(	\+o_rel(Rel)
			-> 	write("Input relation  - "),
				write(Rel),
				write("  - does not occur as a relation in any loaded ontology."),
				writeln("Press any character key to continue."),
				asserta_once(i_nor(Rel)),
				get_single_char(_)
		;	asserta_once(i_orel(Rel))
		),
		(	o_c(Rel)
			-> 	write("Input relation label  - "),
				write(Rel),
				write("  - is used as non-relation constant in at least one loaded ontology."),
				writeln("Press any character key to continue."),
				get_single_char(_)
		;	true
		),
		input_constants(Args),
		check_input([Rel|Args]),
%		replace_idems(Args,0,[],NewArgs),
		check_skolems([Rel|Args],0,TFA,[],[],0,input,unmarked,0),
		fail
	;	\+t(_),
		writeln(""),
		writeln("No scenario data found in input file.")
	),!.
read_input:-!.


terms_to_atoms([],In,Out):-
	reverse(In,Out),!.
terms_to_atoms([H|T],In,Out):-
	term_to_atom(H,H1),
	!,terms_to_atoms(T,[H1|In],Out).

% Store and check input constants
input_constants([]):-!.
input_constants([H|T]):-
	(	o_c(H)
			->	asserta_once(i_oc(H))
	;	asserta_once(i_noc(H))),
	(	i_orel(H)
			-> 	write("Input label  - "),
				write(H),
				write("  - is used both as label for an individual and for an ontology relation."),
				writeln("Press any character key to continue."),
				get_single_char(_),!
	;	true),
	(	i_nor(H)
			-> 	write("Label  - "),
				write(H),
				write("  - is used both as label for an input individual and for an input relation."),
				writeln("Press any character key to continue."),
				get_single_char(_),!
	;	true),
	input_constants(T).


check_input(Fact):-
	p(Fact),!.
check_input(Fact):-
	write("Component of -  "),
	write(Fact),
	writeln("  - not in any loaded ontology."),
	writeln("Press any character key to continue."),
	get_single_char(_),!.


% i,i,i,i,i,i,i
store_fact(Fact, Cause, TFA, Facts, World, Modus, Index, Thor):-	% trace,	
% (ground(Args),true;!,fail),   /* mtt generates facts with variables when rule has more vars in antecedent than consequent. 
								%  Might be good, but need to check */

	

	(	TFA > 0,								% if fact is marked a possible (note: > 0 values not yet used though), and
		(	f(Fact,_,FTFA,Thor,_, 0,_) 			%	if it already exist as fact with possibility marker FTFA either in World
				-> true
		;	f(Fact,_,FTFA,Thor,_, World,_)		%		or in the generally accessible world
		),										% and
		FTFA < 1								%	in either world it is known as true, false or Thor alternative
			-> !, true								% do nothing, else

	% TFA is now 0 or -1, or < -9
	;	% the fact might be in the ontology as true or false, in which case store it first as such
		(	TFA == 0, 												% if the fact is positive
			r(RNR1,_,_,_,Index2,kow(true,then(Fact))),				%	look for a 'true'-rule
			retract(r(RNR1,_,_,_,Index2,kow(true,then(Fact)))),		% when found, retract it to avoid infinite cycle
			store_fact(Fact, RNR1, 0, Facts, World, ont, Index2, 0),	% and store it as derived fact
			fail								% this fail forces the d()-struct of the fact to be updated as caused by other rules too
		;	TFA == -1,												% similarly for negative facts
			r(RNR2,_,_,_,Index3,kow(if([Fact]),false)),
			retract(r(RNR2,_,_,_,Index3,kow(if([Fact]),false))),
			store_fact(Fact, RNR2, -1, Facts, World, ont, Index3, 0),
			fail
		)
	;	(	f(Fact,FE,TFA,0,_,0,_)				% if the fact already exist with the conveyed possibility
				-> true							
		;	f(Fact,FE,TFA,Thor,_,World,_)			
		),
		(	d(Fact, Causes, Uses, Mots, FE, World)	% add the reason why the fact was found again to the existing reasons
				->	(	\+memberchk(Cause, Causes)
							->	retract(d(Fact, Causes, Uses, Mots, FE, World)),
								asserta(d(Fact, [Cause|Causes], Uses, [[Cause|[Index|[Modus|Facts]]]|Mots], FE, World))
					;	true
					)
		;	asserta(d(Fact, [Cause], [], [[Cause|[Index|[Modus|Facts]]]], FE, World))
		)
	;	% it is now sure that the fact does not yet exist as fact and is either 0 or -1, or < -9 so create it and keep statistics

		increment(facts,UF),					% unique fact number over all worlds
% next bit to check for replacements during source code checking 
% (FactIn == Fact -> true ; (World > 0 -> true; writeln(""),writeln(FactIn),writeln(Fact),writeln(UF), trace)),

		length(Fact,FL),						% Determine number of arguments in Fact
		plus(FL,-1,FL2),

		nshort_skolem(Fact, UF, New, World),			% Compute the short skolem form of any skolem constant in Fact
													% This does not transform fact!
		(	TFA > -2
				->	increment(facts(World),F),				% fact number in the world
					create_lif(Fact,UF,World)				% Create the index with labels for this fact
		;	F is -1 * UF
		),
		(	World == 0
			-> ABPS = 0, ABPW = 0
		;	counterValue(abp, ABPS),
			plus(ABPS, World, ABPW)
		),
		logfile(Stream),
		write_term(Stream,ds1(World, ABPS, ABPW, UF, F, TFA, Cause, Index, Modus, Fact, Facts),
						 [back_quotes(string),nl(true),fullstop(true)]),
						 
		asserta_once(pf(New, UF, TFA, Thor, FL2, World, F)),		% fact stored with short skolem version
		asserta_once(d(Fact, [Cause], [], [[Cause|[Index|[Modus|Facts]]]], UF, World)),	
		(	Cause == 0,							% if fact was entered as input
			true								%	do nothing at this point
		;	ru(Cause, N),						% else if the fact is caused by some fired rule and the rule fired before
			plus(N,1,N1),						%	update the fire counter for that rule 
			retract(ru(Cause,N)),		/* DO PER WORLD !!! */
			assert(ru(Cause,N1))
		;	assert(ru(Cause,1)),				% else initialize the fire counter for that rule as 1 
			increment(rules(World),_)			% increment the counter keeping track of how many rules fired at least once
		),

		% determine whether the newly created fact may be used for further reasoning
		% Outside the base world, there is no further condition
		(	World \== 0
			-> (	TFA == 0							% increment in World the appropriate fact type counter
					-> 	increment(pfacts(World),_),
						asserta_once(todo(mpp,UF,World)),
						asserta_once(todo(mpt,UF,World)),
						asserta_once(todo(mtp,UF,World))
				;	TFA == -1
					-> 	increment(nfacts(World), _),
						asserta_once(todo(mtt,UF,World))
				;	increment(mfacts(World), _)
				)
		% but in the base world, do not use unresolved alternatives which are there for mere display
		;	 (	TFA == 0, Thor == 0
					-> 	increment(pfacts(World),_),
						asserta_once(todo(mpp,UF,World)),
						asserta_once(todo(mpt,UF,World)),
						asserta_once(todo(mtp,UF,World))
			 ;	TFA == -1, Thor == 0
					-> 	increment(nfacts(World), _),
						asserta_once(todo(mtt,UF,World))
			 ;	increment(mfacts(World), _)
			 )

		),		

		% it might however already exist in opposite TFA, so there is a contradiction to be marked
		(Thor == 0 ->
		  (	TFA == -1,
			(	f(Fact, FN, 0, 0, _, 0,_) ; f(Fact, FN, 0, 0, _, World,_)	)  /* use d() to display reason ? */
			->	assert_inconcistency([], [-101, [], [Fact]], World, Index)
		  ;	r(RNR100,_,_,_,Index200,kow(true,then(Fact)))				%	look for a 'true'-rule
			->	assert_inconcistency([], [RNR100, [], [Fact]], World, Index200)
		  ;	true
		  ),
		  (	TFA == 0, 
			(	f(Fact, FN, -1, 0, _, 0, _) ; f(Fact, FN, -1, 0, _, World, _)	),
			asserta_once(f(Fact, UF, TFA, Thor, FL2, World, F))
			->	assert_inconcistency([], [-102, [], [Fact]], World, Index)
		  ; r(RNR200,_,_,_,Index300,kow(if([Fact]),false))
			->	assert_inconcistency([], [RNR200, [], [Fact]], World, Index300)
		  ;	true
		  )
		; true
		) ,
		
		(	\+inconsistent(_,_,World,_),
			Fact = [Relation|Args],
			(	TFA == 0,
				Relation == identical,
				Args = [Idem1, Idem2],						% obtain the two labels
				Idem1\==Idem2
					-> (	idem(0,Idem1,Pref1,World),		% if both have already a prefered alternative
							idem(0,Idem2,Pref2,World) ->
							(	Pref1 == Pref2	
									->	repl_nonprefs(World, Idem1, Pref1, UF),	% Replace all facts in which Syn, Syn with Pref
										idem_labels(World,Idem1,Pref1),
										repl_nonprefs(World, Idem2, Pref1, UF),	% Replace all facts in which Syn, Syn with Pref
										idem_labels(World,Idem2,Pref1)
							;	idem_pref(0,Pref1,Pref2,World,_,Pref),		% determine which one is the pref 
								repl_nonprefs(World, Idem1, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
								idem_labels(World,Idem1,Pref),
								repl_nonprefs(World, Idem2, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
								idem_labels(World,Idem2,Pref)
							)
						;	idem(0,Idem1,Pref1,World) ->
							idem_pref(0,Pref1,Idem2,World,_,Pref),
							repl_nonprefs(World, Idem2, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
							idem_labels(World,Idem2,Pref),
							repl_nonprefs(World, Pref1, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
							idem_labels(World,Pref1,Pref)
						;	idem(0,Idem2,Pref2,World) ->
							idem_pref(0,Pref2,Idem1,World,_,Pref),
							repl_nonprefs(World, Idem1, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
							idem_labels(World,Idem1,Pref),
							repl_nonprefs(World, Pref2, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
							idem_labels(World,Pref2,Pref)
						;	idem_pref(0,Idem1,Idem2,World,Syn,Pref),		% determine which one is the pref 
							repl_nonprefs(World, Syn, Pref, UF),			% Replace all facts in which Syn, Syn with Pref
							idem_labels(World,Syn,Pref)
						),
						asserta_once(f(Fact, UF, TFA, Thor, FL2, World, F))
					
			;	asserta_once(f(Fact, UF, TFA, Thor, FL2, World, F)),
				create_identities(Args,UF,World,Thor)
			)
		;	asserta_once(f(Fact, UF, TFA, Thor, FL2, World, F))
		)
	),!.


%% not used. Idea does not work, but perhaps useful elsewhere
% i
mpp_allowed([_|Args]):-
	\+member([e|_],Args),!.
mpp_allowed([_|Args]):-
	member([e|[Sk|_]],Args),
	sk_use(Sk,_,Conds,_),
	Conds\==[], !.


create_identities([],_,_,_):-!.
create_identities([H|T],UF,World,Thor):-
	\+f([identical,H,H],_,0,_,_,World,_),
	\+o_c(H),			% H should not be an ontology constant,
	ground(H),
	check_skolems([identical,H,H],0,0,[UF],0,World,none,identity,Thor),
	!,create_identities(T,UF,World,Thor).
create_identities([_|T],UF,World,Thor):-
	!,create_identities(T,UF,World,Thor).


% i,i,i
create_lif([],_,_):-!.				% Create the index with literals
create_lif([H|R],UF,World):-
	(	ground(H)
			->	asserta_once(lbl(H,World)),
				asserta_once(lif(H,UF,World)),
				(	is_list(H)
						-> create_lif(H,UF,World)
				;	true
				)
	;	true
	),
	create_lif(R,UF,World),!.

idem_labels(World,Syn,Pref):-
	lbl(LBL,World),
	memberNestList(Syn,LBL),
	assert(oldNew(Syn,Pref)),
	replace2(LBL,NLBL),
	retract(oldNew(Syn,Pref)),
	lbl(NLBL,World),
	asserta_once(idem(0,LBL,NLBL,World)),
	fail.
idem_labels(_,_,_):-!.

		
		
% i,i,i,i
repl_nonprefs(World, Syn, Pref, IdemRuleNbr):-		% replace facts
	\+inconsistent(_,_,World,_),

	lif(Syn, FN, World),						% Find a FN in which Syn is used
	retract(f(Fact, FN, TFA, Thor, _, World, _)),
	decrement(facts(World),_),
	(	inconsistent(_,_,World,_)					% stop identity resolution when inconsistency detected
		-> true
	;	assert(oldNew(Syn,Pref)),
		replace2(Fact, RFact),
		retract(oldNew(Syn,Pref)),
		(	TFA == 0
				->	retractall(todo(mpp,FN,World)),
					retractall(todo(mpt,FN,World)),
					retractall(todo(mtp,FN,World))
		;	TFA == -1
				-> 	retractall(todo(mtt,FN,World))
		;	trace,true),
		store_fact(RFact, -3, TFA, [FN,IdemRuleNbr], World, repl, identity, Thor),
		fail
	),!.

repl_nonprefs(World, Syn, Pref, IdemRuleNbr):-		% replace thors()
	\+inconsistent(_,_,World,_),
	thor(RN, RestAlts, AllAlts, SupportFN, Index),
	memberNestList(Syn,AllAlts),
	retract(thor(RN, RestAlts, AllAlts, SupportFN, Index)),
	assert(oldNew(Syn,Pref)),
	replace2(RestAlts, NewRests),
	replace2(AllAlts, NewAlls),
	retract(oldNew(Syn,Pref)),
	assertz_once(thor(RN, NewRests, NewAlls, [IdemRuleNbr|SupportFN], Index)),
	fail.
repl_nonprefs(_,_,_,_):-!.


	
% i,i,i,i,o,o
% not used yet,2 comparants,World,Syn,Pref 
idem_pref(0,A,B,World,C,D):-								% determine which label to keep for identities
	(	is_list(A),	is_list(B)							% if both are skolems
			->	( memberNestList(A,B)					% 	if one is listmember of the other, store the one as pref
					-> asserta_once(idem(0,B,A,World)),
					   C=B, D=A
				; memberNestList(B,A)
					-> asserta_once(idem(0,A,B,World)),
					   C=A,D=B
				; list_depth(A,Ad),				% otherwise, store the one with the lowest depth as pref
				  list_depth(B,Bd),
				  ( Ad > Bd
						-> asserta_once(idem(0,A,B,World)),
						   C=A, D=B
					; asserta_once(idem(0,B,A,World)),
					  C=B,D=A
				  )
				)
	;	is_list(B)
			-> asserta_once(idem(0,B,A,World)),
			   C=B,D=A
	;	is_list(A)
			-> asserta_once(idem(0,A,B,World)),
			   C=A,D=B
	; 	atom_length(A,AL),
		atom_length(B,BL),
		( AL > BL
			-> 	asserta_once(idem(0,A,B,World)),
				C=A, D=B
		; asserta_once(idem(0,B,A,World)),
				C=B,D=A
		)
	),!.


% i,i,o,i	
nshort_skolem(Fact, UF, New, World):-
	nth0(I,Fact,[e,Sk,H]),									% true if Fact has a skolem constant in the Ith position in function format
	(	World == 0
			->	increment(e(Sk,0),_)
		; increment(e(Sk,1),_)),
	(	skolem(Skol,[e,Sk,H]) ->						% if that skolem constant has already been generated
		replace_nth0(Fact, I, [e,Sk,H], Skol, NewFact)		%	replace in Fact that constant with its short notation
	;	increment(skolem(0), S),						% otherwise, generate a new short skolem constant index
		atomic_concat(sk,S,SKS),							%	use the index to create a short name of the form 'sk[index]'
		asserta_once(skolem(SKS, [e,Sk,H])),			%	store the short name and the function form in memory
		replace_nth0(Fact, I, [e,Sk,H], SKS, NewFact)		%	replace in Fact that constant with its short notation
	),
	!,nshort_skolem(NewFact,UF, New, World).					% look for other skolem constants in function form in the Fact
nshort_skolem(Fact,UF,New,W):-									
	nth0(I,Fact,s(X)),trace,								% replace left-over s(X) constructs with X. If so, error in parser.
	replace_nth0(Fact, I, s(X), X, NewFact),
	!,nshort_skolem(NewFact,UF,New,W).
nshort_skolem(New,_,New,_):-!.								% if nothing to replace anymore, return result.


%---------- INFERENCE LOOP

process(_, World, _):-					% i,i,i			% stop when there is an inconsistency
	(	inconsistent(_,_, World,_) ; inconsistent(_,_, 0,_)	),
	!, fail.
process(_, World, _):-					% i,i,i			% stop when processing in World is stopped on criterion
	blocked(World),
	fail.
process(_, World, _):-
	\+blocked(World),
	counter(facts(World), Nstart),
	modus_ponens(World, 1),
	fact_count(World, _),
	infer_falses(World),					% derive negative facts from falsehood rules
	fact_count(World, _),
	(	World == 0
		->	writeln("modus tollendo tollens ..."), flush_output
	; true),
	modus_tollens(World),					% derive negative facts from negative ones
	fact_count(World, _),
	sure_ors(World, main),				% derive facts through then_or rules
	fact_count(World, Nend),
	Nend>Nstart,
	!,process(1, World, Nend).
process(_, 0, _):-
	\+inconsistent(_,_, _,_),
	counter(facts(0), Nstart),			% obtain the number of facts after the inference loop
	then_ors_with_cds,
	counter(facts(0), Cend2),			% obtain the number of facts after the inference loop
	writeln(""),
	Cend2 > Nstart,
	!,process(1, 0, Cend2).
/*process(_, 0, Nstart):-
	\+inconsistent(_,_, _,_),
	retract(skolem_level(X)),
	X<3,
	plus(X,1,NL),
	asserta(skolem_level(NL)),
	all_input(As),
	reuse_input(As),trace,
	!,process(1, 0, Nstart).*/
process(_,_,_):-!.


% i,o
fact_count(World, FactCount):-
	counter(facts(World), FactCount),								% check whether facts have been generated
	(	World == 0
		->	write("Total facts: "),
			writeln(FactCount)
	;	true
	),!.

reuse_input([]):-!.
reuse_input([H|R]):-
	asserta(todo(mpp,H,0)),
	!,reuse_input(R).


% i, i
% Fails only when inconsistency detected
% Generates positive facts on the basis of positive facts
modus_ponens(World, Call):-
	assess_block(World),								% if blocking condition not satisfied
	(	World == 0, Call == 1							% when in base world and called from main process inference loop
		->	writeln(""),
			writeln("modus ponendo ponens ...")
	;	true),
	retract(todo(mpp,F,World)),							% select from the todo-list for mpp the fact number of first one to process
	f(Fact,F,0,_,_,World,_),							% retrieve the fact with that fact number
	findall(X, pick_then_rule(Fact, F, World, _, X), Xs1),	% collect in Xs unused then-rules being a template for Fact 
	sort(0, @<, Xs1, Xs),												
	derive(Xs, Fact, F, World),							% if there are such rules, turn their consequence into a fact
	(	inconsistent(_,_,World,_)						% fail indefinitely when inconsistency detected
		->	!, fail
	; fail).											% process next one on the todo-list
modus_ponens(World, Call):-
	assess_block(World),								% if blocking condition not satisfied
	todo(mpp,_,World),									% if the todo-list was extended in the previous round
	plus(Call, 1, NewRound),							% process the additions
	!, modus_ponens(World, NewRound).
modus_ponens(_, _):-!.


assess_block(World):-
	(	blocked(World)
		-> fail
	;	(	World > 0, 
			skolem_level(SKL), SKL > 2					/* use adjustible init parameter rather than 2*/
			->	counterValue(facts(0),BaseWorld),
				counterValue(facts(World),PW),
				(	PW < BaseWorld
					->	true
				;	write(":Inconclusive"), 
					asserta_once(blocked(World)),
					fail
				)
		;	true)
	),!.


% i,i,i,i,o
pick_then_rule(Fact, F, World, Len, [SL,Len,RN]):-		
	rilr(Fact, RN, Len, 1, Sk, _, Index),	% (1) check any rule of Type in which a template for Fact is one of the 'Len' number of antecedents
	d(Fact, Y, X, _, F, World),				% obtain the list X with rule indexes of rules containing the Fact template that already fired for this fact's generation
	\+memberchk(RN,X),						% (2) check that the rule with index RN is not in list X
	\+memberchk(RN,Y),						% (2) check that the rule with index RN is not in list Y
	length(Sk,SL),							% obtain number of skolem constants that would be generated
	r(RN, Len, Sk, _, Index, _).		% if both conditions are satisfied, the rule may be picked.



% fails if check_skolem detects inconsistency 
derive([],_,_,_):-!.			% i					% stop if all picked rules are tried
derive([[_,_,RN]|R],Fact, F, World):-				% process first rule on the stack
	r(RN, _, Sk, _, Index, kow(if(Facts),then(THEN))),
%	writeln(""),
%	writeln(kow(if(Facts),then(THEN))),
	skolem_cycle(RN,Index,Fact,Go),			% check whether the rule introduces a skolem function which is already in the Fact
	determ_nth1(FactPosition, Facts, Fact),		% bring the fact that triggered rule upfront for the rule's antecedent matching
	(	FactPosition > 1
			-> 	select(Fact, Facts, Facts1),
				Facts2 = [Fact|Facts1]
	;	Facts2 = Facts, true	),
	(	Go==1,
		collect_satisfiers(ruler(Fact,Facts2,THEN),World,0,Satisfiers),	% collect all antecedent-matching fact combinations for the rule
		solutions(Satisfiers, rule(Facts,[THEN]), [], Solutions),		% find all matching combinations (within further specified limits)
		store_solutions(Solutions, RN, Sk, World, mpp, Index),			% store the new solutions as facts
		fact_used_in(Fact, F, RN)					%		update the list with rules that were fired because of this Fact
	;	
/*writeln(""),
writeln(Fact),
writeln(Facts2),
writeln(THEN),
trace,
*/		true
	),
	!,derive(R, Fact, F, World). 					% process the rest of the stack


determ_nth1(A,B,C):-
	nth1(A,B,C),!.


% i,i,i,o
% first argument useless, avoids currently to have to change the calling clauses
skolem_cycle(RN,Index,Fact,0):-				% return 0 if a skolem-cycle at the threshold level was prevented
	sub_term([e,H,P],Fact),				 	% check whether the fact contains a skolem function of type H,
	sk_cycle_level(X),						% if so, determine the accepted cycle-depth specified in the init-file
	cyclical_skolem(H,P,N),					% determine the depth of the cycle if one would occur
	(	X>=N								% fail the clause of the allowed depth-level is higher or equal than the actual depth that would arise
		-> fail
	;	increment(skcycle(RN,Index,H),_),	% otherwise, store then also which function H cycled, due to which rule RN of which axiom Index
		true, !).
skolem_cycle(_,_,_,1):-!.					% return 1 if a possible cycle would be below the threshold-level.


% i,i,o
cyclical_skolem(H, Fact, N):-			% determine the depth of a possible cycle
	sub_term([e,H,P], Fact),			% if the fact contains a skolem function of type H, AND
%	ground(P),							%	the arguments of the skolem function H are ground
	cyclical_skolem(H,P,M),				% recursively check all deeper levels
	N is M+1.
cyclical_skolem(_,_,0).

% i,i,i,o
collect_satisfiers(ruler(Fact, Facts,THEN), World, TFA, Satisfiers):-
	fact_satisfiers(ruler(Fact, Facts,THEN), World, TFA, Facts, [], FSS),	% build list FSS with an element for each rule antecedent condition 
	list_comb2(FSS, Satisfiers),
%	writeln(""),
%	writeln(FSS),
%	writeln(""),
%	writeln(Satisfiers),
%	writeln(""),
%	trace,
	!.


% i,i,i,i,i,o	
fact_satisfiers(_, _, _, [], FSS, FSSout):-
	reverse(FSS,FSSout),
%	writeln(FSSout),trace,
	!.
fact_satisfiers(ruler(Fact, Facts,THEN), World, TFA, [H|RestFacts], In, Out):-
	max_ante_arg_matches(M),
	findall(H, ( f(H,FN,TFA,0,_,0,_) *-> true; f(H,FN,TFA,0,_,World,_) ), Mbag),
	sort(Mbag,Mbag1),
	length(Mbag1, MBL),
	(	MBL > M
			->	findnsols(M, H, ( f(H,FN,TFA,0,_,0,_) *-> true; f(H,FN,TFA,0,_,World,_) ), FNS1),
				sort(FNS1,FNS)
%				,write("Max argument matches reached ..."), writeln(Mbag), get_single_char(_)
	;	FNS = Mbag1
	),
	(	FNS==[], !, fail
	;	!,
%		writeln(""),writeln(H),writeln([FNS|In]),writeln(""),trace,
		fact_satisfiers(ruler(Fact, Facts,THEN),World,TFA, RestFacts, [FNS|In], Out)
	).


solutions([], _, Out, Out):-!.
solutions([Test|Rest], rule(Facts,[THEN]), In, Out):-
	copy_term(rule(Facts,[THEN]), C),
	(	rule(Test,[Solution]) = rule(Facts,[THEN])
			->	!,solutions(Rest, C, [rule(Facts,[Solution])|In],Out)
	; !, solutions(Rest, C, In, Out)
	).


store_solutions([], _, _, _, _, _):-!.
store_solutions([rule(Test,[Solution])|RestS], RN, Sk, World, mpp, Index):-
	fn_of_facts(Test,[],Out),
	check_skolems(Solution, RN, 0, Out, Sk, World, mpp, Index,0),			% 	if so, apply appropriate conclusion
	!,store_solutions(RestS, RN, Sk, World, mpp, Index).


fn_of_facts([],FNS,FNS):-!.
fn_of_facts([H|Frest],In, Out):-
	f(H,FN,_,_,_,_,_),
	!,fn_of_facts(Frest,[FN|In],Out).


fact_used_in(_,F, RN):-				/* check whether updated in all modes !!! */
	f(Fact,F,0,_,_,World,_),
	d(Fact,Causes,Uses,Mots,F,World),
	(	memberchk(RN, Uses),
		true
	;	retract(d(Fact,Causes,Uses, Mots,F,World)),
		asserta(d(Fact,Causes,[RN|Uses],Mots,F,World))
	),!.


% Fails when inconsistency found
% i,i,i,i,i,i,i,i,i
% /* Needs (perhaps) improvement */
% Current mechanism: with Sk not being [], a skolem constant is created only within a certain
%	level of embedding as set in init-file. 
check_skolems(ConcIn, RN, TFA, Facts, Sk, World, Modus, Index, Thor):- 
	% Unground skolem in Conc might indicate bad quantification in axiom Index
	(	Modus\==mtt,
		memberchk([e,NoNum,_], ConcIn),
		\+ground(NoNum),
		writeln(""),writeln(ConcIn), write("Inappropriate universal quantification possibly in axiom "),
		write(Index),write("?"),writeln(""),
		get_single_char(_),
		!,fail
	; true
	),
	replace_idems(ConcIn,World,[],Conc),
	(	\+Sk==[],
		skolem_level(SKL),
		\+within_depth(Conc, _, SKL)
		-> gen_skol(Conc,[],Gen,World)
	;	Gen = Conc
	),
	(	(	f(Gen,FID,TFA,_,_,0,_),			% if pos/neg fact exists already, no further f()-storage
			d(Gen,Rules,_,_,FID,0), 
			!
		; 	f(Gen,FID,TFA,_,_,World,_), 
			d(Gen,Rules,_,_,FID,World), !
		),
		(	Gen \== Conc
			->	last(Rules,Rule),
				increment(na(RN, Rule),_)		% prevented / preventing
		; true
		),
		true 
	;	\+inconsistent(_,_,World,_),
		store_fact(Conc, RN, TFA, Facts, World, Modus, Index, Thor)
	),!. 


replace_idems([],_,TermIn,TermOut):-
	reverse(TermIn,TermOut),!.
replace_idems([H|T],World,In,Out):-
	idem(0,H,Pref,World),
	!,replace_idems(T,World,[Pref|In],Out).
replace_idems([H|T],World,In,Out):-
	!,replace_idems(T,World,[H|In],Out).



% i,o,o
% fact; skolem depth; difference of skolem depth with skolem_level
skolem_depth(Fact, Depth, Diff):-
	skolem_level(SKL),
	list_depth(Fact, FD),
	Depth is (FD-1)/2,
	Diff is Depth - SKL,!.


% i,i,o,i
gen_skol([],In,Out,_):-			
	reverse(In,Out),!.
gen_skol([H|T],In,Out,W):-
	(	(	idem(0, H, Pref, 0) 
				-> true
		; idem(0, H, Pref, W)
		),
		gen_skol(T,[Pref|In],Out,W)
	;	is_list(H),
		gen_skol(T,[_|In],Out,W)
	;	gen_skol(T,[H|In],Out,W)
	),!.
	

pick_false_rule(Fact, [Fact, Conds, RN, FactPos, Sk, Index]):-	% i,o
	rilr(Fact, RN, _, 0, Sk, FactPos, Index),						% pick the index of any falsehood rule in which a template for Fact is an antecedent
	r(RN, _, _, _, Index, kow(if(Conds),false)).					% get the incompatible conditions.


/* Need to be made complete like mpp ? I think it is already*/
infer_falses(World):-
	(	World == 0
		->	writeln("modus ponendo tollens ..."), flush_output
	; true),
	retract(todo(mpt,F,World)),
	\+blocked(World),								% if blocking condition not satisfied
	skolem_level(SKL),
	f(Fact, F, 0, Thor, _, World,_),
	(	inconsistent(_,_,World,_)
		-> true
	;	(	SKL > 2,								/* try to use max depth generated */
			\+within_depth(Fact, _, SKL),		% if the skolem depth of the candidate fact is not within the maximum 
			fail
		; true),
		pick_false_rule(Fact, [Fact, Conds, RN, FactPos, _, Index]),  %(RN==210,trace;true),
		nth1(FactPos,Conds,FactCond),
		FactCond=Fact,  
		false_fact(Fact, F, World, [Fact, Conds, RN, FactPos], [], Out1, [], Out2, [], Out3),
		length(Conds, CL),
		length(Out2, CO2),
		(	CL == CO2		%% 2024-01-01: because of this test, o8 in false_fact/10 may not be sorted
			->	assert_inconcistency([], [RN, [], Out3], World, Index),
				!,fail
			;	(	Out1 = [X],
%					ground(X),		/*20231113*/					% avoid creating falses with variables as some rules would do?
					store_fact(X, RN, -1, Out2,  World, mpt, Index, Thor)	% no check_skolem allowed
				; true)
		),
		fail
	).
infer_falses(World):-	
	assess_block(World),!.
infer_falses(_):-!.


% i1,i2,i3,i4,i5,o6,i7,o8,i9,o10
% i1:seed fact, i2:seed factnum, i3:world,
% i5/o6: term that may be derived as false when all other terms listed in 2nd member of i4 are true
% i7/o8: fact numbers of terms listed in 2nd member of i4 known to be true. %% 2024-01-01: may not be sorted !
% i9/o10: terms listed in 2nd member of i4 known to be true
false_fact(_, _, _, [_, [],_, _], Out1, Out11, Out2, Out2, Out3, Out3):-
	(	ground(Out1)
		->	sort(Out1,Out11)			% single fact that may be derived as false
	;	Out11 = Out1
	),!.
false_fact(THEN, F, World, [THEN, [THEN|R], RN, _], In1, Out1, In2, Out2, In3, Out3):-		% on + list if seed fact proven positive
	!,false_fact(THEN, F, World, [THEN, R, RN, _], In1, Out1, [F|In2], Out2, [THEN|In3], Out3).
false_fact(THEN, F, World, [THEN, [[identical,A,B]|R], RN, _], In1, Out1, In2, Out2, In3, Out3):-
	f([identical,B,A],FN,0,0,_,0,_),																% also if it exist in reference world										
	false_fact(THEN, F, World, [THEN, R, RN, _], In1, Out1, [FN|In2], Out2, [[identical,B,A]|In3], Out3).
false_fact(THEN, F, World, [THEN, [[identical,A,B]|R], RN, _], In1, Out1, In2, Out2, In3, Out3):-
	f([identical,B,A],FN,0,0,_,World,_),															% also if only in alternative world														
	false_fact(THEN, F, World, [THEN, R, RN, _], In1, Out1, [FN|In2], Out2, [[identical,B,A]|In3], Out3).
false_fact(THEN, F, World, [THEN, [H|R], RN, _], In1, Out1, In2, Out2, In3, Out3):-
	f(H,FN,0,0,_,0,_),																% also if it exist in reference world										
	false_fact(THEN, F, World, [THEN, R, RN, _], In1, Out1, [FN|In2], Out2, [H|In3], Out3).
false_fact(THEN, F, World, [THEN, [H|R], RN, _], In1, Out1, In2, Out2, In3, Out3):-
	f(H,FN,0,0,_,World,_),															% also if only in alternative world														
	false_fact(THEN, F, World, [THEN, R, RN, _], In1, Out1, [FN|In2], Out2, [H|In3], Out3).
false_fact(THEN, F, World, [THEN, [H|R], RN, _], In1, Out1, In2, Out2, In3, Out3):-			% true candidate if not in either world
	\+f(H,_,0,0,_,0,_),
	\+f(H,_,0,0,_,World,_),
	false_fact(THEN, F, World, [THEN, R, RN, _], [H|In1], Out1, In2, Out2, In3, Out3).


/* Made complete like mpp but by removing cuts*/
modus_tollens(World):-
  % generates many negative facts which are never used, slowing everything down, but also true positives
	skolem_level(SL),
	SL < 3,
	todo(mtt,FN,World),
	f(F,FN,-1,Thor,_,X,_),											
	(	inconsistent(_,_,World,_)
		-> true
	;	(X == 0 ; X > 0, X == World),
		r(RN, _, _, _, Index, kow(if(Conds),then(F))), 
		all_but_one_proven(World, Conds, [], [TheOne], [], Support),
		check_skolems(TheOne, RN, -1, [FN|Support], [a], World, mtt, Index, Thor),
		fail	% this fail makes in all_but_one_proven back-tracking on second clause possible!
	).
% for then_ors with all directly stated consequences resolving to negative facts: rare case! 
modus_tollens(World):-
	retract(todo(mtt,FN,World)),
	f(F,FN,-1,Thor,_,X,_),											
	(	inconsistent(_,_,World,_)
		-> true
	;	(X == 0 ; X > 0, X == World),
		r(RN, _, _, _, Index, kow(if(Conds),then_or(Concs))),
		memberchk(F, Concs),
		all_false(World, Concs, [], ConcNos),
		all_but_one_proven(World, Conds, [], [TheOne], [], Support),
		union(ConcNos, Support, Support2),
		check_skolems(TheOne, RN, -1, Support2, [a], World, mtt, Index, Thor),
		fail
	).
modus_tollens(_):-!.


all_false(_, [], Out, Out1):-
	sort(Out, Out1),!.
all_false(World, [H|R], In, Out):-
	f(H,HN,-1,_,_,X,_),											% store number of already pos fact on Support list
	(X == 0 ; X > 0, X == World),
	!, all_false(World, R, [HN|In], Out).

	
all_but_one_proven(_, [], Out, Out1, Support, Support1):-		% i,i,i,o,i,o
	sort(Out, Out1),
	sort(Support, Support1).
all_but_one_proven(World, [H|R], In, Out, Sin, Sout):-
	f(H,HN,0,0,_,X,_),											% store number of already pos fact on Support list
	(X == 0 ; X > 0, X == World),								% no cut!
	all_but_one_proven(World, R, In, Out, [HN|Sin], Sout).
all_but_one_proven(World, [H|_], _,_,_,_):-
	f(H,_,-1,0,_,X,_),											% proven neg fact amongst premisses makes rule not to be used 
	(X == 0 ; X > 0, X == World),
	!,fail.
all_but_one_proven(World, [H|R], In, Out, Sin, Sout):-			% not yet (dis)proven fact is candidate for being negative
	!,all_but_one_proven(World, R, [H|In], Out, Sin, Sout).


sure_ors(World, When):-
	(	World == 0, When\==end
		->	writeln("modus tollendo ponens ...")
	;	true),
	(	When == main
		->	retract(todo(mtp,F,World))
	;	true),
	f(Fact, F, 0, Thor, _, World,_),	% (Thor\==0,trace;true),		% pick fact on top of list
	(	inconsistent(_,_,World,_)
		-> true
	;
		pick_then_or_rule(Fact, [Fact, kow(if(Conds),then_or(Alts)), RN, Sk, Index]),	% pick a then_or rule with the fact in antecedents
%(Index == "BFOCE-bmi-03" -> trace; true),
		sure_or(Fact, F, World, [Fact, kow(if(Conds),then_or(Alts)), RN], [], NewFacts, [], Out2),		% fails if ...
		(	[NewFact] = NewFacts,											% success if only one alternative left
			% ground(NewFact),
			skolem_cycle(RN,Index,NewFact,Go),									% if no skolem cycle results from it
			Go==1
			->	check_skolems(NewFact, RN, 0, Out2, Sk, World, mtp, Index, Thor),	% check skolem level
				(	thor(RN, _, Alts, _, _)									% remove the rule from the candidates for alternative worlds
					-> retract(thor(RN, _, Alts, _, _))
				;	true )
		;	( % ground(NewFacts),				/*20231113*/			% if the list of facts proven is ground
			\+length(NewFacts,1),										%	and not contains only one element
			\+one_proven(NewFacts, World),								%	and none of them is positive
				(	thor(RN, NewFacts, Alts, _, _)
					-> true
				;	thor(RN, OldFacts, Alts, _, _),			% such rules can work on different fact sets, so check !
					subset(NewFacts, OldFacts),
					retract(thor(RN, OldFacts, Alts, _, _)), 
					assertz_once(thor(RN, NewFacts, Alts, Out2, Index)),
					true
				;	assertz_once(thor(RN, NewFacts, Alts, Out2, Index)),
					true
				) 
			;	true )
		),
		fail
	).
sure_ors(_,_):-!.

% i,i,i
% first stop conditions: if premisses and alternatives are all processed, then sure_or succeeds and
%	out2 contains all the numbers of the facts that satisfy the premisses or dissatisfy an alternative
%	out contains all the facts which are not yet proven pos or neg in the global and possible world under scrutiny
% sure_or fails 
%	if an alternative is proven,
%	if not all conditions are satisfied.
sure_or(_, _, _, [_, kow(if([]),then_or([])),_], Out, Out11, Out2, Out22):-
	sort(Out2,Out22),
	sort(Out,Out11),!.																	% Succeed if all Conds proven and only one Alt left.
% process all conditions
sure_or(Fact, F, World, [Fact, kow(if([Fact|R]),then_or(Alts)),RN], In, Out, In2, Out2):-		% If Fact is a Cond, remove it from Conds
	!, sure_or(Fact, F, World, [Fact, kow(if(R),then_or(Alts)),RN], In, Out, [F|In2], Out2).	%    	and add the fact's index to fact list that fires the rule 
sure_or(Fact, F, World, [Fact, kow(if([H|R]),then_or(Alts)),RN], In, Out, In2, Out2):-			% Pick the first Cond
	(	f(H,HI,0,0,_,0,_)																	% If it corresponds to a fact
		-> true																			%	proceed
	;	World > 0, f(H,HI,0,0,_,World,_)
		-> true
	; !,fail),																			%	otherwise stop
	!, sure_or(Fact, F, World, [Fact, kow(if(R),then_or(Alts)),RN], In, Out, [HI|In2], Out2).	%   remove that Cond and add fact index to firing facts list

% then alternatives; if() list is now empty
sure_or(Fact, F, World, [Fact, kow(if([]),then_or([H|R])),RN], In, Out, In2, Out2):-		% Pick first alternative
	f(H,HI,-1,0,_,0,_),																		% If it corresponds to a negative fact
	!, sure_or(Fact, F, World, [Fact, kow(if([]),then_or(R)),RN], In, Out, [HI|In2], Out2).		%		remove it from the alternatives and put it on fire list
sure_or(Fact, F, World, [Fact, kow(if([]),then_or([H|R])),RN], In, Out, In2, Out2):-		% Pick first alternative
	World > 0, 
	f(H,HI,-1,0,_,World,_),																		% If it corresponds to a negative fact
	!, sure_or(Fact, F, World, [Fact, kow(if([]),then_or(R)),RN], In, Out, [HI|In2], Out2).		%		remove it from the alternatives and put it on fire list
sure_or(Fact, F, World, [Fact, kow(if([]),then_or([H|R])),RN], In, Out, In2, Out2):-			
	(	f(H,_,0,0,_,0,_)				% if there is a positive in the alternatives, then the rule cannot be used
		-> !,fail
	;	f(H,_,0,0,_,World,_)
		-> !,fail
	; true),
	!, sure_or(Fact, F, World, [Fact, kow(if([]),then_or(R)),RN], [H|In], Out, In2, Out2).		%		remove it from the alternatives and put it on fire list

	
pick_then_or_rule(Fact, [Fact, Rule, RN, Sk, Index]):-
	rilr(Fact, RN, _, N, Sk, _, Index), %%(Index == "BFO-cop-1",trace;true),
	N>1,
	r(RN, _, Sk, _, Index, Rule).
	
one_proven([H|_], _):-f(H,_,0,0,_,0,_),!.
one_proven([H|_], World):-f(H,_,0,0,_,World,_),!.
one_proven([_|R], World):-!,one_proven(R, World).



then_ors_with_cds:-
	writeln(""),
	writeln("Computing undeniables from remaining alternatives ..."),
	findall([RN,PossList,AllAlts, SupportFacts, Index], thor(RN, PossList, AllAlts, SupportFacts, Index),AltBag),
	length(AltBag,L),
	(	L==0, 									% if nothing can be derived in modes used thus far
		writeln("   no open alternatives available ..."),
		sure_ors(0, end),						% then try reductio ad absurdum on remaining alternatives
		counter(facts(0),Nb),
		write("Total facts: "),writeln(Nb),
		findall(X, (thor(_, PossList, _, _, _),member(X,PossList)), Xs),
		length(Xs,LXs),
		(	LXs > 0,
			writeln(""),writeln("reductio ad absurdum ..."),
			sort(Xs,Xs2),
			length(Xs2,LXs2),
			assume(Xs2, 1, LXs2),
			writeln("")
		; true)
	;	process_altbag(AltBag,L)
	),
	retractall(thor(_,_,_,_,_)),
	counter(facts(0),N),
	write("Total facts: "),writeln(N),!.


assume([],_,_):-!.
assume([Assumption|R], TestWorld, L):-
	skolem_level(SKL),						% obtain the maximum skolem depth as set in the init-file
	SKL > 2,								/* try to use max depth generated */
	\+within_depth(Assumption, _, SKL),		% if the skolem depth of the candidate fact is not within the maximum 
	write(L),write(", "),flush_output,
	plus(L,-1,L2),
	!,assume(R,TestWorld, L2).
assume([Assumption|R], TestWorld, L):-
	write(L),write(", "),flush_output,
	increment(abp, _),					% increment assumption based proof index
	skolem_level(SKL),					% obtain the maximum skolem depth as set in the init-file
	(	inc_ass(Assumption, TestWorld, -1),
		check_skolems(Assumption, -40, 0, [], [], 0, rana, rana,0)
	; 	(	SKL < 3 ;								/* try to use max depth generated */
			within_depth(Assumption, _, SKL)		% if the skolem depth of the candidate fact is not within the maximum 
		),	increment(abp, _),
			inc_ass(Assumption, TestWorld, 0),
			check_skolems(Assumption, -41, -1, [], [], 0, rapa, rapa,0)
	;	true
	),
	plus(L,-1,L2),
	!,assume(R,TestWorld, L2).

% i,i,i
inc_ass(Fact, TestWorld, TFA):-
	check_skolems(Fact, -4, TFA, [], [], TestWorld, assumed, assumed,0),		% do not prevent deeper skolem
	process(_, TestWorld, 1),
	inconsistent(_,_,TestWorld,_),
	retract_world(TestWorld),!.
inc_ass(_, TestWorld, _):-
	inconsistent(_,_,TestWorld,_),
	retract_world(TestWorld),!.
inc_ass(_, TestWorld, _):-
	retract_world(TestWorld),!,fail.


% Takes all instantiated then_or-rules of which all premisses are proven, but all or some consequences not yet
% Each rule is processed one by one, independent of the others
% Each possible consequence of the rule under scrutiny is assumed to be true in its own possible world and further inferences
%	are made using proven facts from the base world and the specific possible world, but not from any other possible world.
% Processing in a possible world stops when either
%	1) an inconsistency is derived, which makes the assumed alternative false in the base world
%	2) no further facts can be derived 
% When all possible worlds for the rule are evaluated, the following scenarios are possible:
% 	1) all possible worlds lead to an inconsistency: then either the set of axioms is inconsistent or the inputted facts are
%	2) all but one possible worlds leads to an inconsistency: then the orginal assumption for that one world 
%		is true in the base world as well as all derivations made
%	3) at least two possible worlds, including all, do not lead to an inconsistency: then only the derivations which are 
%		exactly similar in all of these worlds are true in the base world. The original assumptions for these worlds are
%		then NOT proven. 
% i,i  Arg1= , Arg2=length(Arg1)
process_altbag([],_):-writeln(""),!.
process_altbag([[RN,PossList,AllAlts,SupportFacts, Index]|R],Len):-
	write(Len),write(":"),write(RN),flush_output, 		% display process evolution on screen
	increment(abp, _),					% increment assumption based proof index
	alternative_worlds(posa, RN, PossList, SupportFacts, Index, 0, 
						[], Undeniables, 	% collect facts true in all alternatives otbo positive assumption (posa)
						[], IncAlt, 		% collect posa alternatives that led to inconsistency
						[], Blocked,		% collect posa alternatives where derivations were blocked
						[], Whys),			% collect whys for Undeniables
	length(PossList,L),
	length(IncAlt,L2),
	length(Blocked, LB),
	(	L2 == L				% all pw are inconsistent despite all premisses of the rule are proven
		->	getFactsThroughFactno(SupportFacts,[],Out),
			assert_inconcistency(Out, [RN, [], Out], 0, Index),
			!,fail
	;	LB > 0	->	true	% if execution is blocked in any alternative, no conclusion can be drawn
	;	plus(L2,1,L)		% only one pw is consistent
			->	getFactsThroughFactno(IncAlt,[],IncAltFacts),
				subtract(PossList, IncAltFacts, [OneTrueAssumption]),
				union(SupportFacts, IncAlt, S),
				check_skolems(OneTrueAssumption, RN, 0, S, [], 0, mtpa, Index, 0)		% do not prevent deeper skolem
	;	% now find which alternatives are already in World 0, and which needs marking AOPn
		Undeniables\==[]									% it is now a list of common facts in all worlds
			-> 	subtract(AllAlts,PossList,Proven),			% obtain already proven consequences
				findall( ProvenN, 							% obtain the unique numbers for these proven consequences
						 (	member(X,Proven), 
							f(X,ProvenN,0,_,_,0,_)	),
							ProvNs),
				union(SupportFacts,ProvNs,AllSupport),		% add them as support to the already existing support fact numbers
				decrement(or,OR),
				store_undeniables(Undeniables,L,Whys,OR,RN,AllSupport,Index),	% Undeniables are usable
				show_ff(OR, Undeniables),
				retractall(ff(_,_,_,_,_,_)),
				retractall(ffx(_)),
				findall(Fnum, (f(_,Fnum,_,Thor,_,0,_), Thor \== 0), Fnums),
				retract_thorfacts(Fnums),
				length(Fnums,LFN),
				LFND is 0 - LFN,
				increase_by(facts(0),LFND,_)
%,trace
	;	true
	),
	retract_alt_worlds(L),
	increase_by(abp, L, _),
	alternative_worlds(nega, RN, PossList, SupportFacts, Index, 0, [], _, [], _, [], _, [], _),
	write(", "),flush_output,
	retract_alt_worlds(L),
	plus(Len,-1,Len1), 
	increase_by(abp, L, _),
	!, process_altbag(R,Len1).
process_altbag([[_,PossList,_, _,_]|R],Len):-
	length(PossList,L),
	retract_alt_worlds(L),
	plus(Len,-1,Len1),
	!, process_altbag(R,Len1).


retract_thorfacts([]):-!.
retract_thorfacts([F|T]):-
	retract(f(_,F,_,_,_,_,_)),
	!,retract_thorfacts(T).


store_undeniables([],_,_,_,_,_,_):-!.
store_undeniables([[F,TFA]|R],L,Whys,ORn,RN,S,Index):-
	f(F,_,TFA,_,_,0,_),										% when known already in base world
	!,store_undeniables(R,L,Whys,ORn,RN,S,Index).
store_undeniables([[F,TFA]|R],L,Whys,ORn,RN,S,Index):-
	build_or_proof(F,TFA),								% build proof for one common consequence for all worlds
	!, store_undeniables(R,L,Whys,ORn,RN,S,Index).
store_undeniables([_|R],L,Whys,ORn,RN,S,Index):-		% if check_skolems fails
	!, store_undeniables(R,L,Whys,ORn,RN,S,Index).


% i,i
build_or_proof(F,TFA):-							% process one common consequence of all worlds
	findall(RW,									% find in each world the rule, mode and facts that led to the common consequence
			(	f(F,FactNo,TFA,_,_,W,_),
				W>0,
				why_rule_fired(FactNo,W,RW)	),
			RWs),
			sort(RWs,RWs2),
	f_forms(F,TFA,RWs2),!.


show_ff(OR, _):-
	ff(F,TFA,Rn,Ax,posa,_,Base),
	store_fact(F, Rn, TFA, Base, 0, mppa, Ax, OR),
	fail.
show_ff(OR, Undeniables):-
	ff(F,TFA,Rn,Ax,Mod,SF,Base),
	Mod \== posa,
	(	memberchk([F,TFA],Undeniables),
		fail
	;	reason_by_f(SF,Base,NewBase),
		store_fact(F, Rn, TFA, NewBase, 0, Mod, Ax, OR)
	), fail.
show_ff(OR, Undeniables):-
	ff(F,TFA,Rn,Ax,Mod,SF,Base),
	Mod \== posa,
	memberchk([F,TFA],Undeniables),
	findall([SF1,Base1],ff(F,TFA,_,_,_,SF1,Base1), Xs),
	length(Xs,XsL),
	XsL == 1,
	reason_by_f(SF,Base,NewBase),
	store_fact(F, Rn, TFA, NewBase, 0, Mod, Ax, OR),
	fail.
show_ff(_, Undeniables):-
	ff(F,TFA,_,_,Mod,_,_),
	Mod \== posa,
	memberchk([F,TFA],Undeniables),
	findall([SF1,Base1],ff(F,TFA,_,_,_,SF1,Base1), Xs),
	length(Xs,XsL),
	XsL > 1, %trace,
	allpos(Xs,[],Support),
	ff(_,_,Rn2,Ax2,posa,_,_),
	store_fact(F, Rn2, TFA, Support, 0, ffaa, Ax2, 0),
	fail.
show_ff(_, _):-!.


allpos([],In,In):-!.
allpos([[SF,Base]|T],In,Out):-
	reason_by_f(SF,Base,NewBase),
	union(In,NewBase,NewIn),
	allpos(T,NewIn,Out).



f_forms(_,_,[]):-!.
f_forms(F,TFA,[[Rn|[Ax|[Mod|Sups]]]|Rest]):-
	\+ffx(p(F,TFA,[[Rn|[Ax|[Mod|Sups]]]|Rest])),
	asserta(ffx(p(F,TFA,[[Rn|[Ax|[Mod|Sups]]]|Rest]))),
	fact_forms(Sups,[],SF,[],Base),				% extract supporting facts from the fact numbers separate from baseworld sups  
	% do here recursive for all supports of current support until all supports are either the assumptions or baseworld facts
	build_or_proofs(SF),
	% here for next support relative to current support
	f_forms(F,TFA,Rest),
	assertz_once(ff(F,TFA,Rn,Ax,Mod,SF,Base)).


% i,i,o
reason_by_f([],BaseNew,BaseNew):-!.
reason_by_f([[F,TFA]|T],Bin,Bout):-
	f(F,FN,TFA,_,_,0,_),
	!,reason_by_f(T,[FN|Bin],Bout).


% i
build_or_proofs([]):-!.
build_or_proofs([[F,TFA]|R]):-
	build_or_proof(F,TFA),
	build_or_proofs(R).
build_or_proofs([[_,_]|R]):-
	build_or_proofs(R).


% i,i,o,i,o
fact_forms([],SFi,SFo,Bin,Bin):-
	sort(SFi,SFo),!.
fact_forms([S|R],In,SF,Bin,Bout):-
	( f(_,S,_,_,_,0,_)
		-> fact_forms(R,In,SF,[S|Bin],Bout)
	; f(SFf,S,TFA,_,_,_,_),
	  (	memberchk([SFf,TFA],In)
			-> fact_forms(R,In,SF,Bin,Bout)
		;  fact_forms(R,[[SFf,TFA]|In],SF,Bin,Bout))
	; fact_forms(R,In,SF,Bin,Bout)  
	).

% i,i,i,i,i,i,i,o,i,o,i,o,o
% Processes one then_or rule with at least 2 thus far unresolved alternative consequences 
% Each recursion on arg3=[H|R] processes the next unresolved alternative
alternative_worlds(_,_, [], _, _, _, [], [], IncAlt, IncAlt, Blocked, Blocked,Whys,Whys):-!.				
alternative_worlds(_,_, [], _, _, _, Out, Undeniables, IncAlt, IncAlt, Blocked, Blocked,Whys,Whys):-				
	all_intersect(Out, Undeniables),
	!.
alternative_worlds(	Mod, RN, [H|R], SupportFacts, Index, PreviousWorld, 
					In ,Out, 
					IncIn, IncOut, 
					BlockIn, BlockOut,
					WhysIn,WhysOut):-
	plus(PreviousWorld, 1, NewWorld),
	(	Mod == posa -> TF = 0 ; TF = -1),
	check_skolems(H, RN, TF, SupportFacts, [], NewWorld, Mod, Index,0),		% do not prevent deeper skolem,  
	process(1, NewWorld, 1),		% this fails in case of inconcistency
	(	blocked(NewWorld)
		-> 	retractall(blocked(NewWorld)),
			increment(rule_block(RN,Mod,Index),_),	
			!, alternative_worlds(	Mod, RN, R, SupportFacts, Index, NewWorld, In ,Out, 
									IncIn, IncOut, [NewWorld|BlockIn], BlockOut,WhysIn,WhysOut)
	;	findall(	[F,TFA], f(F,_,TFA,_,_,NewWorld,_), ThisWorldsFacts),
		findall(	[F,FN,FactWhys], 
					(	f(F,FN,TFA,_,_,NewWorld,_),
						d(F,_,_,FactWhys,FN,NewWorld)	),
					ThisWorldsWhys),
		union(ThisWorldsWhys,WhysIn,NewWhys),
		!, alternative_worlds(	Mod, RN, R, SupportFacts, Index, NewWorld, [ThisWorldsFacts|In] ,Out, 
								IncIn, IncOut, BlockIn, BlockOut, NewWhys,WhysOut)
	;	writeln("Should not fail!")
	).
alternative_worlds(	Mod, RN, [H|R], SupportFacts, Index, PreviousWorld, 
					In ,Out, IncIn, IncOut, BlockIn, BlockOut,WhysIn,WhysOut):-	
% when inconsistency in that world
/* implemented here: inconsistency in some world means alternative assumption for that world invalid. 
   Inconsistency in all worlds implies the premisses must be false. */
	plus(PreviousWorld, 1, NewWorld),
	(	Mod == posa
		->	check_skolems(H, RN, -1, SupportFacts, [], 0, rapa, Index, 0),	% do not prevent deeper skolem,  
			f(H,FN,-1,_,_,0,_)												% obtain the fact number
	;	check_skolems(H, RN, 0, SupportFacts, [], 0, rana, Index, 0),	% do not prevent deeper skolem,  
			f(H,FN,0,_,_,0,_)
	; writeln("oops"),writeln(Mod),true),
	retract_world(NewWorld),
	!, alternative_worlds(	Mod, RN, R, SupportFacts, Index, PreviousWorld, In ,Out, 
							[FN|IncIn], IncOut, BlockIn, BlockOut,WhysIn,WhysOut).
%alternative_worlds(_, _, _, _, _, _, In ,Out, IncIn, IncOut, BlockIn, BlockOut,WhysIn,WhysOut):-
%	write("fail "), 
%	!, alternative_worlds(_,_, [], _, _, _, In ,Out, IncIn, IncOut, BlockIn, BlockOut, WhysIn, WhysOut).				


retract_alt_worlds(0):-!.
retract_alt_worlds(N):-
	retract_world(N),
	plus(N,-1,M),
	!, retract_alt_worlds(M).

retract_world(N):-
	retractall(blocked(N)),
	retractall(lbl(_,N)),
	retractall(lif(_,_,N)),
	retractall(counter(facts(N),_)),
	retractall(counter(pfacts(N),_)),
	retractall(counter(nfacts(N),_)),
	retractall(counter(mfacts(N),_)),
	retractall(pf(_,_,_,_,_,N,_)),
	retractall(f(_,_,_,_,_,N,_)),
	retractall(d(_,_,_,_,_,N)),
	retractall(inconsistent(_,_,N,_)),
	retractall(idem(_,_,_,N)),
	retractall(todo(_,_,N)),!.


assert_inconcistency(A,B,World,Index):-
	asserta_once(inconsistent(A, B, World, Index)),
	logfile(Stream),
	write_term(Stream,inconsistent(A, B, World, Index),[back_quotes(string),nl(true),fullstop(true)]),!.
	

% -------------------
write_inconsistency_proof(Name,Facts):-
   string_concat(Name,"-inconsistency-proof.csv",File),
   write("Saving inconsistency proof to "), writeln(File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       write_inc_proof(Out,Facts),
       close(Out)),!.

write_inc_proof(_, []):-!.
write_inc_proof(Out, [FactNo|T]):-
	pf(Fact, FactNo, TF, Thor, _, 0,_),
	print_fact_data(Row, Fact, FactNo, TF, Thor),
	writeln(Out, Row),
	!,write_inc_proof(Out, T).


saveData(Name, MSP) :-			% i		% save file. Program will fail if a file with that name is open!!!	
   string_concat(Name,"-table.csv",File),
   write("Saving generated facts to "), writeln(File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       forall(writeOut(X,MSP),
              writeln(Out, X)),
       close(Out)),!.

writeOut(Out,_):-								% o		% prepare output line per fact
	pf(Fact, FactNo, TF, Thor, _, 0,_),					% take fact from top of fact stack
	print_fact_data(Out, Fact, FactNo, TF,Thor).
writeOut("",_):-!.

print_fact_data(Out, Fact, FactNo, TF, Thor):-
	(	f(_,FactNo,_,_,_,_,_)
			->	FPF = pf
	;	FPF = nf),
	conditional(Thor,THOR),
	why_rule_fired(FactNo,0,[RuleLine|Why]),
	evidence(TF,Evidence),
%	mostSpecFact(Fact,MSP),							% display only most specific type
	spacer(Fact,Spacer),							% determine number of columns in output csv file to skip
	reverse([FPF,FactNo,THOR,Evidence|Fact], L),	% reverse the list and add the fact's unique fact-number and f/pf status
	relToString(L, [], S),							% transform the list into a list of strings
	atomics_to_string(S,T),							% turn it all into one string
	string_concat(T,Spacer,T1),						% add the spacer
	atomic_list_concat([RuleLine|Why], ', ', T2),	% turn the source code line number of the used rule and the responsible facts into a string
	string_concat(T1,T2,Out),!.						% add it to the output

evidence(0,"TRUE"):-!.
evidence(-1,"FALSE"):-!.
evidence(-2,"ERROR"):-!.

conditional(0,"CRT"):-!.
conditional(N,Ns):-
	N < -10,
	plus(N,10,N2),
	atom_concat('OR',N2,N3),
	atom_string(N3,Ns),!.


spacer(Fact, Spacer):-
	length(Fact,FL),
	pl(PL),
	plus(XL,FL,PL),
	length(CommaList,XL),
	maplist(=(","),CommaList),
	flatten([CommaList|["<--,"]],SpaceList),
	atomics_to_string(SpaceList,Spacer),!.

	
relToString([], S, S).
relToString([H|T],A,R):-							% pick first in the list
	term_string(H,H1),
	!, relToString(T,[H1,","|A],R).					% keep as is, and move to next one in the list
relToString([H|T],A,R):-							% pick first in the list when not compound
	atomics_to_string([H,","], Str),
	!, relToString(T,[Str|A],R).					% keep as is, and move to next one in the list


print_skolems(Name):-
   string_concat(Name,"-main_skolems.txt",File),
   findall([I,B], ( skolem(A,B), 
					f(_,FN,_,_,_,_,_),
					pf(F,FN,_,_,_,_,_), 
					memberchk(A,F),
					atom_concat(sk,Is,A),
					atom_number(Is,I)
				  ), SKS),
   sort(SKS,SKS2),
   assertz(skolems_used(SKS2)),
   write("Writing skolem constants to "), writeln(File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       forall( ( member([I,B], SKS2), atom_concat(sk,I,A) ),
               write_pair(Out, [A, B])),
       close(Out)),
   string_concat(Name,"-all_skolems.txt",File2),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File2, write, Out2),
       forall( skolem(A,B),
               write_pair(Out2, [A, B])),
       close(Out2)),!.
	   
write_pair(Out, [A, B]):-
	write(Out, A),
	put_code(Out, 9),
	writeln(Out, B).




print_rules_used(Name):-
   writeln("Calculating rule use statistics ..."),
   setof([X,Y],ru(X,Y),Bag),			% returns false if no rules used
   sort(2,@>=,Bag,SortedBag),
   string_concat(Name,"-rules-used.txt",File),
   write("Writing rules statistics to "), writeln(File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       write_rules_used(Out, SortedBag),
       close(Out)),!.
print_rules_used(_):-!.

write_rules_used(_, []):-!.
write_rules_used(Out, [H|R]):-
	write_pair(Out, H),
	!, write_rules_used(Out, R).

print_counters(Name):-
   string_concat(Name,"-counters.txt",File),
   write("Writing counter statistics to "), writeln(File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       write_counters(Out),
       close(Out)),!.

write_counters(Out):-
	findall([A,B], (counter(A,B), A\=na(_,_)), COUNTERS),
    sort(1,@=<,COUNTERS,SCOUNTERS),
	forall(member(X, SCOUNTERS),writeln(Out, X)),!.


print_possibilia(Name):-
   string_concat(Name,"-alternatives.txt",File),
   write("Writing remaining undecidable altenative consequences to "), writeln(File),
   reject_thors,
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       write_poss(Out),
       close(Out)),!.


reject_thors:-
	skolems_used(SKS),
	findall(S,member([_,S],SKS), Ss),
	thor(_,H,_,_,_),
	(	keep_thor(H,Ss) -> true
	;	retract(thor(_,H,_,_,_))
	), fail.
reject_thors:-!.


% i,i
keep_thor([],_):-!.
keep_thor([F|_],Ss):-
	member(X,F),
	(	X = [e, _, _],
		\+member(X,Ss),
		!,fail
	;	fail
	).
keep_thor([_|RF],Ss):-!,keep_thor(RF,Ss).	


write_poss(Out):-
	findall([X,Y],thor(X,Y,_,_,_),THORS),
    sort(1,@>=,THORS,STHORS),
	write_poss2(Out, STHORS, 0),!.


write_poss2(_,[],_):-!.
write_poss2(Out,[[R,Alts]|T],N):-
	plus(N,1,N1),
	write_poss3(R, Alts, N1, Out),
	!, write_poss2(Out, T, N1).


write_poss3(R,[H],N1,Out):-
	write(Out, N1),
	put_code(Out, 9),
	write(Out, R),
	put_code(Out, 9),
	write(Out, R),
	put_code(Out, 9),
	write(Out, H),
	writeln(Out,""),!.
write_poss3(R, [H|T], N1, Out):-
	write(Out, N1),
	put_code(Out, 9),
	write(Out, R),
	put_code(Out, 9),
	put_code(Out, 9),
	write(Out, H),
	writeln(Out,""),
	!, write_poss3(R, T, N1, Out).

print_not_added(Name):-
   writeln("Calculating skolem generation conflict rules statistics ..."),
  % pair occurrence
   setof([na(R1,R2),Count],counter(na(R1,R2),Count),Bag1),
   sort(2,@>=,Bag1,SortedBag1),
  % prevented rules tallies
   findall([R1,Count],counter(na(R1,_),Count),Bag2t),
   sort(0,@>=,Bag2t,Bag2t1),
   sortsumif(Bag2t1, [], SortedBag2),
  % preventing rules tallies
   findall([R1, Count],counter(na(_,R1),Count),Bag3t),
   sort(0,@>=,Bag3t,Bag3t1),
   sortsumif(Bag3t1, [], SortedBag3),
   string_concat(Name,"-skolem-conflict-rules.txt",File),
   write("Writing skolem conflict rules to "), writeln(File),
   setup_call_cleanup(					% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
       write_nas(Out, SortedBag1, SortedBag2, SortedBag3),
       close(Out)),!.
print_not_added(_):-!.

write_nas(Out, SortedBag1, SortedBag2, SortedBag3):-
	writeln(Out, "Count/Prevented rule/preventing rule"),
	write_nas1(Out,SortedBag1),
	writeln(""),
	writeln(Out, "Prevented rule/Count"),
	maplist(write_pair(Out), SortedBag2),
	writeln(""),
	writeln(Out, "Preventing rule/Count"),
	maplist(write_pair(Out), SortedBag3),
	!.

write_nas1(_, []):-!.
write_nas1(Out, [[na(R1,R2),Count]|R]):-
	write(Out,Count),
	put_code(Out, 9),
	write_pair(Out, [R1, R2]),
	!, write_nas1(Out, R).

	
	
% ------------
% UTILITIES		
% ------------
asserta_once(A):-call(A),!.
asserta_once(A):-asserta(A),!.

assertz_once(A):-call(A),!.
assertz_once(A):-assertz(A),!.

get_string_input(PossibleValues,MessageParts,Response):-
	stringlist_to_screen(MessageParts,false),
	read_line_to_string(user_input,X),
	(	(	X == "" ; not(memberchk(X,PossibleValues))	),
		writeln(""),
		!,get_string_input(PossibleValues,MessageParts,Response)
	;	Response = X) ,!.

stringlist_to_screen(SL, Newline):-		% i,id	
	atomics_to_string(SL, Message),
	( 	Newline == false,
		write(Message), write(" ")
	;	writeln(Message)
	),!.


increment(C,Y):-					% i,o	% increment the counter identified by C
	counterValue(C,X),						% retrieve the value of counter C
	retract(counter(C,X)),					% delete counter C and its value
	plus(X,1,Y),							% add 1 to the value of what was counter C
	asserta(counter(C,Y)),!.				% recreate the counter with the new value

decrement(C,Y):-					% i,o	% decrement the counter identified by C
	counterValue(C,X),						% retrieve the value of counter C
	retract(counter(C,X)),					% delete counter C and its value
	plus(X,-1,Y),							% substract 1 from the value of what was counter C
	asserta(counter(C,Y)),!.				% recreate the counter with the new value

% i,o  -  deterministic
counterValue(C, Value):-			% i,o	% retrieves the value of a counter			
	counter(C,Value),!.						% if the counter exist, take the value
counterValue(C, 0):-						% if the counter does not yet exist, return zero
	asserta(counter(C,0)),!.					% after creating the counter


increase_by(C,N,Y):-				% i,i,o	% increment counter C by N resulting in the new value being Y
	counterValue(C,X),
	plus(X,N,Y),
	retract(counter(C,X)),
	assert(counter(C,Y)),!.


replace_nth0(List, Index, OldElem, NewElem, NewList) :-
   % predicate works forward: Index,List -> OldElem, Transfer
   nth0(Index,List,OldElem,Transfer),
   % predicate works backwards: Index,NewElem,Transfer -> NewList
   nth0(Index,NewList,NewElem,Transfer).

% i,o,i
within_depth([],1,_).
within_depth([H|T],R, M):-
	\+is_list(H),
	!,within_depth(T,R,M).
within_depth([H|T],R,M):- 
	within_depth(H,R1,M), 
	within_depth(T,R2,M), 
	R2 =< M,
	R3 is R1+1,
	R3 =< M,
	max_list([R3,R2],R).


% i,o
list_depth([],1).
list_depth([H|T],R):-
	\+is_list(H),
	!,list_depth(T,R).
list_depth([H|T],R):- 
	list_depth(H,R1), 
	list_depth(T,R2), 
	R3 is R1+1,
	max_list([R3,R2],R).


sortsumif([X],In, Out):-
   sort(2,@>=,[X|In],Out),!.
sortsumif([[A,C1]|[[A,C2]|R]],In, Out):-
	plus(C1,C2,Sum),
	!, sortsumif([[A,Sum]|R], In, Out).
sortsumif([[A,C1]|[[B,C2]|R]],In, Out):-
	A \== B,
	!, sortsumif([[B,C2]|R], [[A,C1]|In], Out).

% i,o,i,o
all_intersect([Out],Out):-!.
all_intersect([A|[B|R]],Out):-
	intersection(A,B,C),
	!,all_intersect([C|R],Out).
	
memberNestList(H,[H|_]).
memberNestList(X,[H|_]):-memberNestList(X,H).
memberNestList(X,[_|T]):-memberNestList(X,T).

%-----------
list_crossproduct(Xs, []) :-
   member([], Xs).
list_crossproduct(Xs, Ess) :-
   Ess = [E0|_],
   same_length(E0, Xs),
   maplist(maybelonger_than(Ess), Xs),
   list_comb(Xs, Ess).

maybelonger_than(Xs, Ys) :-
   maybeshorter_than(Ys, Xs).

maybeshorter_than([], _).
maybeshorter_than([_|Xs], [_|Ys]) :-
   maybeshorter_than(Xs, Ys).
   
list_comb([], [[]]).
list_comb([Xs|Xss], Ess) :-
   Xs = [_|_],
   list_comb(Xss, Ess0),
   maplist(aux_x_comb(Ess0), Xs, Esss1),
   append(Esss1, Ess).

aux_x_comb(Ess0, X, Ess1) :-
   maplist(head_tail_list(X), Ess0, Ess1).

head_tail_list(X, Xs, [X|Xs]).
%---------------------

list_comb2( LL, Ess):-
    is_list( LL),
    maplist( is_list, LL),
    findall( Es, maplist( member, Es, LL), Ess).
	

replace2([], []).
replace2([H|T], [Ht|Tt]) :-
  (  oldNew(H, Ht)
  -> true
  ;  is_list(H)
  -> replace2(H, Ht)
  ;  H = Ht
  ),
  replace2(T, Tt).

  
