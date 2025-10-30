/* History
2025-01-14: improvement: identification of constants used both as individual and relation
2024-12-31: bug-fix: taut/4 was not declared
2024-01-24: bug-fix: prevented negated axiom file generator to run when parser found errors
2024-01-05: generates predicate use data in Kowalski file for improved axiom selection in reasoner
2023-12-28:
	1) generation (on demand) of negated axiom file '...-nsat.txt' in clausal form
	2) reformatting of '...-cf.txt' (on demand) file in the same format as nsat 
2023-12-22: 
	1) tautology detection leading to elimination of useless Kowalski rules
	2) generates sk_use data in Kowalski file for improved skolem function use in reasoner
*/
:- use_module(library(dcg/basics)).
:- use_module(library(pure_input)).
:-dynamic outdiscourses/1,		%% stores per CLIF file processed the used predicates
		  error/2,				%% stores errors found during processing (not all error types can be tagged)
								%	arg1=error type
								%	arg2=info(...)
		  warning/2,			%% stores warnings suggestive for mistakes
		  fol/7,				%% stores for each FOL axiom in input the Conjunctive Normal Form
								%%	1) axiom comment as 'q(STRING)'
								%%	2) unique incremental identifier over all axiom files
								%%	3) axiom in CNF with grounded unique variables per axiom
								%%	4) name of axiom file in which axiom is found
								%%	5) unique incremental identifier within the axiom file. Starts at 1 for each file.
								%%	6) axiom index as provided between [...], or "unmarked"
								%%	7) comment without the [...]
		  tpex/7,				%% same as fol/7 but arg3 is original implication-free axiom with Prolog variables
		  counter/2,			%% keeps track of global counters
								%	arg1=counter name
								%	arg2=counter
								%  counter names in use:
								%	fol:	unique numerical, incremental index of axiom over all axiom files
								%	files:	number of CL files parsed
								%	rkow:	unique finally retained kowalski rule
		  quantvar/1, 			%% collects symbols used as quantified variables in the FOL axioms
		  nonquant/2,			%% stores the CL terms which are not quantified in an axiom (note: check for 'not always' or 'never')
		  constant/4,			%% stores where constants are found
								%	arg1=nonquant term
								%	arg2=filename
								%	arg3=axiom numeric index in file
								%	arg4=global axiom index			
		  predname/1,			%% stores the terms used as predicates in the axioms		
		  folres/1,				%% stores the reserved words for FOL
		  pred_v/1,				%% stores predicates in []-form with 'v(...)' replaced by 'v', leaving nonquants untouched
		  pred_vnq/1,			%% stores predicates in []-form with 'v(...)' replaced by 'v', and non-quantified terms by 'nq'
		  pvnqloc/4,			%% stores location of predicates with specific argument pattern
		  p_in/4,				%% use of predicate name in axiom and rules
								%	arg1=predicate name
								%	arg2=c/no-variables in rule or v/has variables
								%	arg3=rule number
								%	arg4=axiom ID
		  pax/3,				%% predicate use in axiom
								%	arg1=Predicate name
								%	arg2=count of axioms used in
								%	arg3=axiom list
		  axs/5,				%% axiom content
								%	arg1=Axiom ID
								%	arg2=number of rules in axiom
								%	arg3=count of predicates used containing variables
								%	arg4=predicate list with variables
								%	arg5=pred list with only constants
		  predicate/5,			%% stores the full predicate where found
								%	arg1=filename
								%	arg2=axiom numeric index in file
								%	arg3=global axiom index
								%	arg4=the predicate
								%	arg5=number of arguments in predicate
		  taut/4,				%% stores tautologies
								%	arg1=unique axiom identifier over all axiom files (=arg2 in fol/7)
								%	arg2=predicate appearing both as true and false in clause
								%	arg3=conditional part of clause
								%	arg4=consequence part of clause
		  scopedEvar/2,			%% stores skolem functions replacing existentially quantified variables
		  mappedEvar/2,
		  fol_kow/4,				%% 
		  fol_sat/2,				%% 
		  fol_rule/2,
		  rule/3,
		  seen/3,
		  skolems/1,			%% to generate doms for skolems for satchmo
		  sk_use/4,				%% for each skolem function and axiom stores use lists
								%	arg1=skolem function number, i.e. the 'N' in [e,N,...]
								%	arg2=axiom index
								%	arg3=list of rules in which the function is used in antecedents
								%	arg4=list of rules in which the function is used in consequents
		  redundant_axioms/1,	%% list of unique axiom identifiers to be removed because occurring more than once in all axiom files
		  ont/2,				%% files belonging to specific ontology
		  ous/2,				%% dependency between ontologies
%% for the following series, see init.txt
		  ontology/2,			%% [Abbreviation / files]
		  ont_uses/2,
		  skolem_mode/1,
		  variable_mode/1,
		  outputfile/1,
		  projectname/1,
		  progress_notification/1,
		  minimum_constant_length/1,
		  typo_detection/1,
		  non_typo_display/1,
		  fixed_args/1,
		  odd_pred_struc/1,
		  rare_term_use/1,
		  missing_pred_percent/1.			

:-writeln("BFO2020 Style CLIF parser, Version January 27, 2024").
:-writeln("Copyright: Werner Ceusters. All rights reserved.").
:-writeln("Type 'run' to start parser unless autorun specified in init-file.").

:- include("CLIFparserinit.txt").			%% contains input- and output parameters

%% ------------
%% Main process
%% ------------

run:-time(runit),
	get_single_char(_),halt,!.

runit:-start_conditions_ok(H),								% check start-conditions and collect files to parse in 'H'
	 assertz(folres([s(exists),s(forall),s(and),			% store FOL reserved words
					 s(or),s(not),s('='),s(identical)])),
	 asserta_once(predname(s(identical))),
	 parsefiles(H),										% parse each file
	 nonquants_unused,										% error when there are constants that are not used in any predicate
	 run2,													% afterthought for generating 'single consequence inference' rules 
	 get_projectname(Name),
	 saveData(Name),
	 ( \+error(_,_),
		outputfile(nsat)
			-> process_nsat(Name)
	 ; true ),
	 writeln("Press any character key to finish."),!.
runit:-!.

get_projectname(N):-
	( projectname(N) ; N = "ANONYMOUS"), !.


%% ---------------------------------------------------
%% Apply, and where needed, correct init file settings
%% ---------------------------------------------------


start_conditions_ok(H):-
	!,ref_ontologies,
	findall(File,ont(_,File),Files),
	sort(Files,H),
		( H = [],
		  write("Specified input file(s) do not exist. Check CLIFparserinit.txt for the 'inputfiles(\"...\")' parameter."),
		  !,fail
		; 
		  ( skolem_par_ok(1),
			(variable_par_ok(1),
			   findall(F,outputfile(F),Outputs),
				( Outputs \== [],
				  check_outputs(Outputs, [], Errors),
				  ( Errors \== [],
					write("Invalid output filetype(s) specified in first argument of 'outputfile(\"...\")': "),
					writeln(Errors),
				    write("Options are for each parameter one of: sci, rules_per_axiom, kowalski, satchmo, cnf, cf, vocabulary, nnf, nsat."),
					!, fail
				  ; !, true
				  )
				; writeln("No outputfile specified. Check init.txt for the 'outputfile(\"...\")' parameter(s)."),
				  write("Options are for each parameter one of: sci, rules_per_axiom, kowalski, satchmo, cnf, cf, vocabulary, nnf, nsat."),
			      !,fail
				)
			; variable_par_ok(2),
			  writeln("Incorrect variable mode specified. Check init.txt for the 'variable_mode(\"...\")' parameter."),
		      write("Options are one of: unbound, ground."),
			  !,fail
			; variable_par_ok(3),
			  writeln("More than one variable mode specified. Check init.txt for the 'variable_mode(\"...\")' parameter."),
		      write("Options are one of: unbound, ground."),
			  !,fail
		    ; write("Variable mode parameter missing. Check init.txt for the 'variable_mode(\"...\")' parameter."),
			!,fail
			)
		  ; skolem_par_ok(2),
			writeln("Incorrect processing mode for skolemization specified. Correct in init.txt the 'skolem_mode(\"...\")' parameter."),
			writeln("Options are one of: scoped, mapped."),
			!,fail
		  ; skolem_par_ok(3),
			writeln("More than one processing mode for skolemization specified. Check init.txt for the 'skolem_mode(\"...\")' parameter."),
		    write("Options are one of: scoped, mapped."),
			!,fail
		  ; write("Skolemization parameter missing. Check init.txt for the 'skolem_mode(\"...\")' parameter."),
			!,fail
		  )
		),
	( progress_notification(PN),
		( 	PN==minimal
		;	PN==verbose
		;	retract(progress_notification(_)),
			asserta(progress_notification(minimal))
		)
	;asserta(progress_notification(minimal))
	),	
	( minimum_constant_length(MCL),
		( 	integer(MCL)
		;	retract(minimum_constant_length(_)),
			asserta(minimum_constant_length(2))
		)
	;asserta(minimum_constant_length(2))
	),
	( typo_detection(Typo),
		( 	number(Typo),
			Typo > 0,
			Typo < 1
		;	retract(typo_detection(_)),
			asserta(typo_detection(0.95))
		)
	;	asserta(typo_detection(0.95))
	),
	( fixed_args(FixArg),
		( 	(FixArg == yes ; FixArg == no	)
		;	retract(fixed_args(_)),
			asserta(fixed_args(yes))
		)
	;	asserta(fixed_args(yes))
	),
	( non_typo_display(TypoDis),
		( 	number(TypoDis)
		;	retract(non_typo_display(_)),
			asserta(non_typo_display(3))
		)
	;	asserta(non_typo_display(3))
	),
	( odd_pred_struc(OCU),
		( 	number(OCU)
		;	retract(odd_pred_struc(_)),
			asserta(odd_pred_struc(5))
		)
	;	asserta(odd_pred_struc(5))
	),
	( rare_term_use(RTU),
		( 	number(RTU)
		;	retract(rare_term_use(_)),
			asserta(rare_term_use(2))
		)
	;	asserta(rare_term_use(2))
	),
	( missing_pred_percent(MPP),
		( 	number(MPP),
			MPP >= 0,
			MPP =< 1
		;	retract(missing_pred_percent(_)),
			asserta(missing_pred_percent(80))
		)
	;	asserta(missing_pred_percent(80))
	),
	!,check_ont_uses,
	!.

skolem_par_ok(1):-
	setof(X,skolem_mode(X),Xs),
	length(Xs,1),
	(skolem_mode(scoped) ; skolem_mode(mapped) ),!.
skolem_par_ok(2):-
	setof(X,skolem_mode(X),Xs),
	length(Xs,1),
	not(skolem_mode(scoped)),
	not(skolem_mode(mapped)),!.
skolem_par_ok(3):-
	setof(X,skolem_mode(X),Xs),
	length(Xs,N),
	length(Xs,N),N>1,!.

variable_par_ok(1):-
	setof(X,variable_mode(X),Xs),
	length(Xs,1),
	(variable_mode(unbound); variable_mode(ground) ),!.
variable_par_ok(2):-
	setof(X,variable_mode(X),Xs),
	length(Xs,1),
	not(variable_mode(unbound)),
	not(variable_mode(ground)),!.
variable_par_ok(3):-
	setof(X,variable_mode(X),Xs),
	length(Xs,N),N>1,!.


check_outputs([], In, In):-!.
check_outputs([H|R], In, Out):-
	member(H,[sci, rules_per_axiom, kowalski, satchmo, cnf, cf, vocabulary, nnf, nsat]),
	!,check_outputs(R,In,Out).
check_outputs([H|R], In, Out):-
	!,check_outputs(R,[H|In],Out).


ref_ontologies:-
	\+ontology(_,_),
	write("Check init-file! 'ontology(string, stringlist)' statement(s) missing !"),
	!,fail.
ref_ontologies:-
	ontology(A,B),
	(	\+string(A),
		write("Check init-file! First argument of "),write_canonical(ontology(A,B)),writeln(" must be a string within double quotes!"),
		!,fail
	;	\+maplist(string, B),
		write("Check init-file! Second argument of "),write_canonical(ontology(A,B)),writeln(" must be a list of strings each string within double quotes!"),
		!,fail
	),fail.
ref_ontologies:-
	forall(ontology(ID,Files),
		forall(member(X,Files),
			(	expand_file_name(X, Xs),
				forall(member(Y,Xs),
					asserta_once(ont(ID,Y)))
			)
		   )
		  ),!.

check_ont_uses:-
	ont_uses(A,B),
	(	\+string(A),
		write("Check init-file! First argument of "),write_canonical(ont_uses(A,B)),writeln(" must be a string within double quotes!"),
		!,fail
	;	\+maplist(string, B),
		write("Check init-file! Second argument of "),write_canonical(ont_uses(A,B)),writeln(" must be a list of strings each string within double quotes!"),
		!,fail
	),fail.
check_ont_uses:-
	forall(ont_uses(Dependent,Sup),
		forall(member(X,Sup),
				asserta_once(ous(Dependent,X)))
			),!.



%% --------------------- END INIT PROCESSING



%% --------------------------------------------------------------------------------------
%% DCG parser for BFO2020 - CLIF style axiomatization (Not full CLIF, e.g. no sequences!)
%% --------------------------------------------------------------------------------------

parsefiles([]):-!.
parsefiles([F|Fs]):-
	asserta(counter(F,0)),
	increment(files,N),
	asserta(fileparsed(N,F)),
	write("Processing "),write(F),writeln(" ..."),
	( progress_notification(minimal), 
		phrase_from_file(expressions(_), F)
	; phrase_from_file(v_expressions(_), F)
	),
	retract(outdiscourses(_)),
	!,parsefiles(Fs).

%% for progress_notification(minimal)
expressions([E|Es]) -->
    ws, expression(E), ws, 
    !, %% single solution: longest input match
    expressions(Es).
expressions([]) --> [].

expression(s(A))         --> symbol(Cs), { atom_chars(A, Cs) }.
expression(n(N))         --> number(N).
expression(RList)        --> "(", expressions(List), {inSyntax(List,RList)}, ")".
expression(q(Q))		 --> quote(Cs), { string_codes(Q,Cs) }.
%------------------------

%% for progress_notification(verbose)
v_expressions([E|Es]) -->
    ws, v_expression(E), ws, {writeln(E)},
    !, %% single solution: longest input match
    v_expressions(Es).
v_expressions([]) --> [].

v_expression(s(A))         --> symbol(Cs), { atom_chars(A, Cs) }.
v_expression(n(N))         --> number(N).
v_expression(RList)        --> "(", v_expressions(List), {inSyntax(List,RList)}, ")".
v_expression(q(Q))		   --> quote(Cs), { string_codes(Q,Cs) }.
%-------------------------


ws --> [W], { char_type(W, white) }, ws.
ws --> [W], { char_type(W, newline) }, ws.
ws --> [].

quote(Qs) --> [34], 
			 string_without([34], Qs), 
			 [34].
quote(Qs) --> [39], 
			 string_without([39], Qs), 
			 [39].

symbol([A|As]) -->
    [A],
    { (string_codes("#+/>*<-:._=", S), memberchk(A, S)) ; char_type(A, alpha) },
    symbolr(As).
symbolr([A|As]) -->
    [A],
    { (string_codes("+*>*<-:._", S), memberchk(A, S)) ; char_type(A, alnum) },
    symbolr(As).
symbolr([]) --> [].

%% Partial restructuring of input and error checking

inSyntax(In,Out):-isCLIF(In,Out),!.
inSyntax(In,Out):-isFol(In,Out),!.
inSyntax(In,In):-!.

isCLIF([s('cl:comment'),_,[s('cl:text')|_]],[s('cl:comment'),_,[s('cl:text')|_]]):-!.
isCLIF([s('cl:outdiscourse')|Preds],[s('cl:outdiscourse')|Preds]):-
	asserta(outdiscourses(Preds)), 
	list_assert_once(a, predname, Preds),!.


isFol([s('and')],_):-
	isFolLengthError('and'),!.
isFol([s('or')],_):-
	isFolLengthError('or'),!.
isFol([s('not')|R],_):-length(R,X),X\==1,
	isFolLengthError('not'),!.
isFol([s('not'),[s('not'),R]],R):-!.
isFol([s('=')|R],_):-length(R,X),X\==2,
	isFolLengthError('='),!.
isFol([s('=')|R],[s('identical')|R]):-!.
isFol([s('iff')|R],_):-length(R,X),X\==2,
	isFolLengthError('iff'),!.
isFol([s('iff'),IF,THEN],[s('and'),X,Y]):-isFol([s('if'),IF,THEN],X),isFol([s('if'),THEN,IF],Y),!.
isFol([s('if')|R],_):-length(R,X),X\==2,
	isFolLengthError('if'),!.
isFol([s('if'),[s('not'),R],THEN],[s('or'),R, THEN]):-!.
isFol([s('if'),IF,THEN],[s('or'),[s('not'),IF],THEN]):-!.
isFol([s('forall'),Args,R],[s('forall'),Args,R]):-
	list_assert_once(a, quantvar, Args),!.
isFol([s('forall')|_],_):-
	isFolLengthError('forall'),!.
isFol([s('exists'),Args,R],[s('exists'),Args,R]):-
	list_assert_once(a, quantvar, Args),!.
isFol([s('exists')|_],_):-
	isFolLengthError('exists'),!.
isFol([s('cl:comment'),C,FOL],[s('cl:comment'),C,FOL]):-
	% once here, 'FOL' contains the Prolog list-representation of a single axiom with implications disjuncted
	fileparsed(_,F),
	increment(F,FLine),
	checkForError(C,FOL,F,FLine),
	(	outputfile(nsat)
			->  increment(nsat,NSAT),
				assertz(nsat(C,NSAT,[s(not),FOL],F,FLine))
	;	true
	),!.


% check for certain errors in single axiom
% i,i,i,i
% 	axiom comment 
%	raw axiom in Prolog list representation, implications replaced by disjunctions
%	filename in which axiom
%	n'th axiom in file 
checkForError(_,_,F,FLine):-error(_,info(F,FLine,_)),!.
checkForError(_,FOL,F,FLine):-
	findall(X,(isExtQuantified(X, FOL);isUniQuantified(X, FOL)),Vars),
	sort(Vars,SVars),
	forall(member(s(Y),SVars),
			(	occurrences_of_term(s(Y),FOL,Occ),
				(	Occ==1,
					assertz(warning(-8, info(F,FLine,Y)))
				;	true)
			)
		  ),
	fail.
checkForError(q(C),FOL,F,FLine):-
	increment(fol,FolInd),
	standardizeAllVars(FOL,FOL1), 
	(	quantvar(Q),				% check for remaining non-standardized variable in transformed axiom.
		memberNestList(Q,FOL1),
		assertz(error(1,info(F, FLine, Q)))
	; true),
	preds_saved(FOL1, F, FLine, FolInd),
	nots_moved_inwards(FOL1,FOL2),
	multiply_scoped_vars_renamed(FOL2, FOL3),
	varclauses(FOL3,TpEx),		% create axioms with standardized variables as Prolog structures with variables
	skolemize(FOL3,FOL4),
	removeQuantifiers(FOL4,FOL5),
	disAndInOr(FOL5,Out),
	between("[", "]", C, AxiomIndex, "unmarked", StringWithout),	% extract the axiom index (if any) from the comment 
	ont(OID,F),														% get the ontology ID associated with the inputfile
	atomic_list_concat([OID,"-",AxiomIndex],AXID),
	assertz(fol(q(C),FolInd,Out,F,FLine,AXID,StringWithout)),		% fully skolemized axioms
	replace(TpEx,TpNoS),
	assertz(tpex(q(C),FolInd,TpNoS,F,FLine,AXID,StringWithout)),	% original axioms with Prolog variables
	put_in_clausal_form(FolInd,Out),
	!.


isFolLengthError(X):-
	fileparsed(_,F),
	counter(F,FLine),plus(FLine,1,E),
	assertz(error(4, info(F, E, X))),
	!.



%% --------------------- END PARSER

% check whether there are constants that are not used in any predicate, if so, error5
nonquants_unused:-
	nonquant(NQ, N),
	findall(Pred,term_in_predicate(NQ,Pred),Bag),
	length(Bag,L),
	L\==0,
	retract(nonquant(NQ,N)),
	asserta(nonquant(NQ,L)),
	fail.
nonquants_unused:-
	nonquant(NQ,0),
	fol(_,_,FOL1,F,FLine,_,_),
	memberNestList(NQ,FOL1),
	assertz(error(5, info(F, FLine, NQ))),!.
nonquants_unused:-!.


skolem_categorization:-
	fol(_,AxiomFolInd,_,_,_,AxID,_),										% get axiom text ID
	findall(X,(fol_kow(AxiomFolInd,C,A,_),(member(X,C);member(X,A))),Xs),	% find all skolem function indexes in axiom
	sort(Xs,Xss),
	forall(	member(Sk,Xss),
				( findall( R1,
						   ( sk_in_clause(AxiomFolInd,AxID,R1,SK,SK2),
							 member(Sk, SK)
						   ),
						   Rs1	
						 ),
				  sort(Rs1,Rs1s),
				  findall( R2,
						   ( sk_in_clause(AxiomFolInd,AxID,R2,SK,SK2),
							 member(Sk, SK2)
						   ),
						   Rs2	
						 ),
				  sort(Rs2,Rs2s),
				  atomics_to_string([AxID],AxIDs),
				  assertz(sk_use(Sk, AxIDs, Rs2s, Rs1s))
				)
		  ),fail.
skolem_categorization:-!.

% i: init-file provided name of project
saveData(Name):-
	skolem_mode(mapped),
	string_concat(Name,"-skolem-map.txt",FE),
	save_skmap(FE),fail.
saveData(Name):-
	global_checking,				% Perform some error checking once all axioms processed
	string_concat(Name,"-comments.txt",FE),
	(	error(_,_) ->
		writeln(""),
		write("ERRORS FOUND! Only comment file generated!"),
		writeln(""),
		writeln("")
	;	redundant_axioms(RAs),			% Get them
		forall(member(UID,RAs),			% Use them to remove the redundant fol/7 constructs
			(retract(fol(_,UID,_,_,_,_,_)),
			 retract(tpex(_,UID,_,_,_,_,_)))),
		outputfile(X),
		filename_data(Name, X, FileName),
		(X \== nsat
			-> saveData(X,FileName)
		;	true),
		fail
	; 	(	outputfile(kowalski),
			skolem_categorization,								% analyse skolem function use per axiom
			filename_data(Name, kowalski, FileName),
			print_skolem_use(FileName),
			print_pred_use(FileName)
		;	true
		)
	),
	save_comments(FE),
	!.
saveData(_):-!.


process_nsat(Name):-
	writeln(""),
	writeln("Processing negated axioms for satisfiability testing ..."),
	retractall(fol(_,_,_,_,_,_,_)),
	retractall(tpex(_,_,_,_,_,_,_)),
	retractall(fol_cnf(_,_)),
	retractall(counter(qvar,_)),
	retractall(counter(function,_)),
	(	nsat(q(AxCom),GlobId,NegAx,NameOfFile,NbrAxInFile),
		standardizeAllVars(NegAx,NegAx1), 
		nots_moved_inwards(NegAx1,NegAx2),
		multiply_scoped_vars_renamed(NegAx2, NegAx3),
		skolemize(NegAx3,NegAx4),
		removeQuantifiers(NegAx4,NegAx5),
		disAndInOr(NegAx5,NegAx6),
		between("[", "]", AxCom, AxiomIndex, "unmarked", StringWithout),	% extract the axiom index (if any) from the comment 
		ont(OID,NameOfFile),														% get the ontology ID associated with the inputfile
		atomic_list_concat([OID,"-",AxiomIndex],AXID),
		assertz(fol(q(AxCom),GlobId,NegAx6,NameOfFile,NbrAxInFile,AXID,StringWithout)),		% fully skolemized axioms
		put_in_clausal_form(GlobId,NegAx6),
		fail
	;	filename_data(Name, nsat, FileName),
		saveData(nsat, FileName),
		true
	),!.



% i,i,o
filename_data(ProjectName, FileType, FileName):-
	string_concat(ProjectName,"-",F1),
	string_concat(F1,FileType,F2),
	string_concat(F2,".txt",FileName),!.


print_skolem_use(File):-
   setup_call_cleanup(				
       open(File, append, Out),
	   print_sk_use(Out),
	   close(Out)),!.

print_sk_use(Out):-
	writeln(Out, ""),
	writeln(Out, "% Skolem use information"),
	writeln(Out, "% Function ID, Axiom ID, function in antecedents of rule, function in consequents"),
	sk_use(A,B,C,D),
	write_canonical(Out, sk_use(A,B,C,D)),
	writeln(Out, "."),
	fail.
print_sk_use(_):-!.


print_pred_use(File):-
   setup_call_cleanup(				
       open(File, append, Out),
	   print_p_use(Out),
	   close(Out)),!.

print_p_use(Out):-
	writeln(Out, ""),
	writeln(Out, "% Predicate use information"),
	writeln(Out, "% Predicate name, v(ariables amongst arguments) or c(onstants only), rule ID, Axiom ID"),
	p_in(P, V, RID, AxID),
	(	\+axs(AxID,_,_,_,_)
			->	findall(X, p_in(X,v,_,AxID), Xvs),
				sort(Xvs,Xvss),
				findall(X, p_in(X,c,_,AxID), Xcs),
				sort(Xcs,Xcss),
				findall(R, p_in(_,_,R,AxID), Rs),
				sort(Rs,Rss),
				length(Rss,LRss),
				length(Xvss,LXvss),
				assertz(axs(AxID,LRss,LXvss,Xvss,Xcss))
	;	true),
	(	\+pax(P,_,_)
			->	findall(A, p_in(P,_,_,A), As),
				sort(As,Ass),
				length(Ass,LAss),
				assertz(pax(P,LAss,Ass))
	;	true),
	write_canonical(Out, p_in(P, V, RID, AxID)),
	writeln(Out, "."),
	fail.
print_p_use(Out):-
	writeln(Out, "% Predicate name, count of axioms used in, axiom list"),
	pax(P, L, A),
	write_canonical(Out, pax(P, L, A)),
	writeln(Out, "."),
	fail.
print_p_use(Out):-
	writeln(Out, "% Axiom ID, N rules in axiom, N predicate names containing variables used, variable predicate list, constant pred list"),
	axs(A, L, R, P, Q),
	write_canonical(Out, axs(A, L, R, P, Q)),
	writeln(Out, "."),
	fail.
print_p_use(_):-!.


%% ---------------- End main process


%% ---------------
%% Global checking
%% ---------------

global_checking:-
	ambiguous_constants,						% check for constants used both as predicate name and individual
	typo_check,									% check for possible typo's
	pred_with_variable_arg_number,				% check for outdiscourse terms with variable argument structure
	pred_with_structure_diffs,					% check for distributional oddities in predicate structures
	rare_terms,									% identification of rarely used terms

	% compare use of constants in predicate types internally for each declared ontology 
	findall(X,ontology(X,_),Xs), 				% collect in Xs all declared ontologies
	maplist(const_nu_pred,Xs,Xs),				% compare for each one of them there constant use relative to themselves

	% compare use of constants in predicate types in depending ontologies relative to such use in ontologies they depend on 
	findall(X1,ous(X1,_),Deps), 				% collect in Deps all ontologies declared to depend on at least one other ontology
	findall([Y,Z],(member(Y,Deps),ous(Y,Z)),O),
	sort(O,O1),
	forall(member([DO,IDO],O1),
		const_nu_pred(DO,IDO)),					% compare to ontologies declared to be used
	find_dupl_axioms,							% find axiom duplications, multiply axiom index use, ...
	!.


ambiguous_constants:-
	findall(X, predname(X), Xs),
	sort(Xs, Preds),
	findall(X, (predicate(_,_,_,[_|Z],_), member(X, Z), \+X=v(_)), Cs),
	sort(Cs, Css),
	ord_intersection(Preds, Css, Ds),
	findall(info(FileName, Index, X, relation), 
			( member(s(X),Ds), 
			  predicate(FileName,Index,_,[s(X)|_],_) ),
			PredP),
	length(PredP,PWL),
	findall(info(FileName2, Index2, X, individual), 
			( member(s(X),Ds), 
			  predicate(FileName2,Index2,_,[_|Args],_),
			  member(s(X), Args) ),
			PredC),
	length(PredC,PCL),
	( PWL >= PCL
		-> forall(member(Error, PredC), assertz(error(10,Error)))
	; PCL > PWL
		-> forall(member(Error, PredP), assertz(error(10,Error)))
	),!.

	

%% Checking for possible typos
typo_check:-
	typo_detection(TDO),
	findall([A,B],
			(nonquant(s(A),_),nonquant(s(B),_),not(A==B),isub(A,B,X,[]),X>TDO),
			Sims),
	de_duplicated(Sims,[],Sims1),
	non_typo_display(NTD),
	forall(member([M1,M2],Sims1),
			(	counter(s(M1),M1U),
				counter(s(M2),M2U),
				(	M1U > M2U,
					(	M1U =< NTD,
						findnsols(NTD,[File,Ind],constant(s(M1),File,Ind,_),Sols)
					;	Sols=[]),
					findall([File2,Ind2],constant(s(M2),File2,Ind2,_),Sols2),
					assertz(warning(0,info(M1,M1U,Sols,M2,M2U,Sols2)))
				;	(	M2U =< NTD,
						findnsols(NTD,[File2,Ind2],constant(s(M2),File2,Ind2,_),Sols2)
					;	Sols2=[]),
					findall([File1,Ind1],constant(s(M1),File1,Ind1,_),Sols1),
					assertz(warning(0,info(M2,M2U,Sols2,M1,M1U,Sols1)))
				))),!.


de_duplicated([],Out,Out):-!.
de_duplicated([[A,B]|R],In,Out):-
	memberchk([B,A],R),
	!,de_duplicated(R,In,Out).
de_duplicated([[A,B]|R],In,Out):-
	!,de_duplicated(R,[[A,B]|In],Out).

%% checking for outdiscourse terms with variability in number of arguments
pred_with_variable_arg_number:-
	predname(PName),								% backtrack over each predicate name
	setof(ArgSig, pred_v([PName|ArgSig]),ArgSigs),	% collect in ArgSigs the various argument structures found for that name
	arg_sig_diff(PName,ArgSigs,[],ArgSigDiffs),		% collect in ArgSigDiffs the numbers of times these argument structures are used
	length(ArgSigDiffs,LASD),						% retrieve in LASD the number of distinct structures
	LASD>1,											% when more than one
	(	fixed_args(yes),							% 	if no variation allowed per init-file: create error
		assertz_once(error(6, info()))
	;	true),
	assertz(warning(-1,info(PName,ArgSigDiffs))),	% 	create warning
	fail.
pred_with_variable_arg_number:-!.

% 
arg_sig_diff(_,[],Out,Out1):-
	sort(1,@>=,Out,Out1),!.							% sort occurrence list descending
arg_sig_diff(PName,[AS|Rest],In,Out):-
	length(AS,LAS),
	member(X,Rest),
	length(X,LAS),
	!,arg_sig_diff(PName,Rest,In,Out).
arg_sig_diff(PName,[AS|Rest],In,Out):-
	length(AS,PLAS),
	counter(p(PName,PLAS),Occ),
	!,arg_sig_diff(PName,Rest,[[Occ,PLAS]|In],Out).


%% checking for outdiscourse terms with variability in argument types
pred_with_structure_diffs:-
	findall(A,(pred_vnq([A|AR]),pred_vnq([A|BR]),not(AR==BR),not(A==s(identical))),As),
	sort(As,Out),
	(	not(Out==[]), 
		odd_pred_struc(OCU),
		forall(member(X,Out),
				(	findall([ArgS,Count],counter(pred_vnq([X|ArgS]),Count),ArgSS),
					sort(2,@>=,ArgSS,RP1),
					sort(1,@>=,RP1,[[Pattern,PatCount]|RestPat]),
					length(Pattern,MPL),
					findall(PatL,(member([PatL,PLC],RestPat),length(PatL,MPL),PLC=<OCU),KeepPats),
					(	KeepPats\==[],
						assertz(warning(-2,info(X,Pattern,PatCount,KeepPats)))
					;	true)
				)
			  )
	;	true),!.	
	
%% identifying rarely used terms
rare_terms:-
	rare_term_use(RTU),
	counter(s(X),Y),
	Y=<RTU,
	findall([B,C], constant(s(X),B,C,_), Sets),
	assertz(warning(-3,info(X,Sets))),
	fail.
rare_terms:-!.


%% identify constants which are not arguments of predicates in which most other constants are arguments
const_nu_pred(Ont,COnt):-
	findall(X,(predicate(FOnt,_,_,[X|_],_),ont(COnt,FOnt)),Xs),	% collect in Xs all predicate relations used in the ontology to compare to
	sort(Xs,Xs1),												% sort and remove doubles
	findall(CC, (constant(s(CC),FOnt,_,_),ont(COnt,FOnt)),CCs),	% collect in CCs all constants from the ontology to be compared
	sort(CCs,CCs1),
	length(CCs1,LCC),
	missing_pred_percent(MPP),
	c_u_nu(MPP,LCC,COnt,Xs1,[],PNA),							% collect in PNA for each such term all constants used as arguments in them
	findall(NC, (constant(s(NC),FOnt,_,_),ont(Ont,FOnt)),NCs),	% collect in NCs all constants from the ontology to be compared
	sort(NCs,NCs1),
	outlier_constants(NCs1,PNA,[],Outliers),
/* requires checking; does not work for terms not in ontology depending from */
	findall([Pred,Percent],(member(mp(_,Pred,Percent),Outliers),Percent<100),Preds),
	sort(Preds,PredsOut),
	missing_preds(PredsOut,Outliers,[],ToReport),
	(	\+ToReport==[],
		assertz(warning(-4,info(Ont,COnt,ToReport)))
	;	true),
	!.

% i,i,i,i,i,o
c_u_nu(_,_,_,[],In,In):-!.
c_u_nu(MPP,LCC,COnt,[s(A)|R],In,Out):-
	findall(C,(predicate(FOnt,_,_,[s(A)|T],_),
			ont(COnt,FOnt),member(s(C),T)),Ps),	% collect in Ps all constants used as argument in any predicate with relation s(A)
	sort(Ps,Ps1),								% sort and remove doubles; Ps1 contains all constants used as arguments in COnt
	Ps1\==[],									% if the list is not empty
	length(Ps1,L),								% store number of elements in L
	P is round(100*(L/LCC)),
	P >= MPP,
	!,c_u_nu(MPP,LCC,COnt,R,[rp(A,P,Ps1)|In],Out).	% save in rp(...) the predicate name, the number of constants and the list of constants
c_u_nu(MPP,LCC,COnt,[_|R],In,Out):-
	!,c_u_nu(MPP,LCC,COnt,R,In,Out).

outlier_constants([],_,In,In1):-
	flatten(In,In1),!.
outlier_constants([NC|RestNC],PNA,In,Out):-
	outlier_c2(NC,PNA,[],NCs),
	\+NCs==[],
	!,outlier_constants(RestNC,PNA,[NCs|In],Out).
outlier_constants([_|RestNC],PNA,In,Out):-
	!,outlier_constants(RestNC,PNA,In,Out).

outlier_c2(_,[],In,In):-!.
outlier_c2(NC,[rp(_,_,Cs)|RestPNA],In,Out):-
	member(NC,Cs),
	!,outlier_c2(NC,RestPNA,In,Out).
outlier_c2(NC,[rp(P,L,LA)|RestPNA],In,Out):-
	\+member(rp(P,L,LA),In),
	!,outlier_c2(NC,RestPNA,[mp(NC,P,L)|In],Out).
outlier_c2(NC,[_|RestPNA],In,Out):-
	!,outlier_c2(NC,RestPNA,In,Out).

missing_preds([],_,In,In):-!.
missing_preds([[A,B]|Rest],Outliers,In,Out):-
	findall(M,member(mp(M,A,B),Outliers),Ms),
	!,missing_preds(Rest,Outliers,[mps(A,B,Ms)|In],Out).


%% ---------------
%% Output routines
%% ---------------

save_skmap(F):-						%% Output only available in skolem_mode "mapped"
    setup_call_cleanup(					
       open(F, write, Out),
	   print_skmap(Out),
	   close(Out)),!.
save_skmap(_):-!.

print_skmap(Out):-
	mappedEvar(A,B),
	writeln(Out,mappedEvar(A,B)),
	fail.
print_skmap(_):-!.

save_comments(F):-
    setup_call_cleanup(					%% ... it will overwrite the file with the same name when it is closed.
       open(F, write, Out),
	   print_comments(Out),
	   close(Out)),!.
save_comments(_):-!.


print_comments(Out):-
	print_errors(Out),
	print_warnings(Out),!.
	
print_errors(Out):-
	error(_,_),								% if at least one error present
	writeln(Out,"% ERRORS"),
	print_standard_error(Out, 1),
	print_standard_error(Out, 2),
	print_standard_error(Out, 3),
	findall(X4, error(4,X4),Xs4),
	(	Xs4\==[],
		writeln(Out, "%  Illegal number of expressions after:"),
		forall(member(info(F,FLine,Q),Xs4),
				(	write(Out, "%    \""),write(Out,Q),write(Out,"\" in axiom number "), write(Out,FLine), 
					write(Out," in file "), writeln(Out, F)
				)
			  )
	;	true),
	findall(X10, error(10,X10),Xs10),
	(	Xs10\==[],
		writeln(Out, "%  Constant used both as relation and individual:"),
		forall(member(info(F,FLine,Q,Use),Xs10),
				(	atomics_to_string(["%    \"", Q, "\" used as ", Use, " in axiom number ", FLine, " in file "], E10S), 
					write(Out, E10S),
					writeln(Out, F)
				)
			  )
	;	true),
	print_standard_error(Out, 5),
	(	error(6,_),
		writeln(Out, "%  Outdiscourse terms with variable number of arguments found. See warnings for details !")
	;	true),
	print_standard_error(Out, 7),
	writeln(Out,""),!.
print_errors(_):-!.


print_standard_error(Out, ErrorNum):-
	findall(X, error(ErrorNum,X),Xs),
	(	ErrorNum==1,
			Text="Remaining non-standardized variables in transformed axiom:"
	;	ErrorNum==2,
			Text="Constants with length smaller than the minimum_constant_length specified in the init-file:"
	;	ErrorNum==3,
			Text="Constants used as predicate name but not declared in (cl:outdiscourse ...):"
	;	ErrorNum==5,
			Text="Constants not used in any predicate:"
	; true
	),
	(	Xs\==[],
		write(Out, "%  "),writeln(Out, Text),
		forall(member(info(F,FLine,Q),Xs),
				(	fol(_,_,_,F,FLine,AIndex,_),
					write(Out, "%    \""),write(Out,Q),write(Out,"\" in axiom number "), write(Out,FLine), 
					write(Out, " ["),write(Out,AIndex),write(Out,"]"),
					write(Out," in file "), writeln(Out, F)
				)
			  )
	;	true),!.
	

/* rewrite print_warnings without the fail mechanism */
print_warnings(Out):-
	writeln(Out, ""),
	writeln(Out,"% WARNINGS"),
	warning(A,W),
	fol(q(Q),A,_,_,_,_,_),
	write(Out, "%  "), writeln(Out, Q),
	write(Out, "%    "), writeln(Out,W),
	writeln(Out, ""),
	fail.
print_warnings(Out):-
    setof(W,warning(0,W),Typos),
	writeln(Out,""),writeln(Out,""),
	writeln(Out, "%  Possible orthographic errors assumed from lexical similarity:"), 
	forall(member(info(W1,W1U,Sols1,W2,W2U,Sols2),Typos),
			 (	write(Out, "%    \""),write(Out,W1),write(Out, "\" (times used = "),write(Out, W1U),write(Out,")  /"),
				write(Out, "  \""),write(Out,W2),write(Out, "\" (times used = "),write(Out, W2U),writeln(Out,")"),
				(	Sols1==[],
						true
				;	write(Out, "%        "), write(Out, W1), writeln(Out, ":"),
					forall(member([File1,Find1],Sols1),
						(	fol(_,_,_,File1,Find1,AIndex,_),
							write(Out,"%           axiom number "), write(Out,Find1), 
							write(Out, " ["),write(Out,AIndex),write(Out,"]"),
							write(Out," in file "), writeln(Out, File1)
						)
						  )
				),
				write(Out, "%        "), write(Out, W2), writeln(Out, ":"),
				forall(member([File2,Find2],Sols2),
						(	fol(_,_,_,File2,Find2,AIndex2,_),
							write(Out,"%           axiom number "), write(Out,Find2), 
							write(Out, " ["),write(Out,AIndex2),write(Out,"]"),
							write(Out," in file "), writeln(Out, File2)
						)
					  )
			 )
		   ),
	fail.
print_warnings(Out):-
    setof(W,warning(-1,W),Varvar),
	writeln(Out,""),writeln(Out,""),
	writeln(Out, "%  Predicates with variable numbers of arguments:"), 
	forall(member(info(s(PName),[[MaxArg,OutArg]|Outliers]),Varvar),
		(	write(Out, "%    "),write(Out,PName), write(Out,": "), write(Out, MaxArg), write(Out, " times used with "), 
					write(Out,OutArg), writeln(Out, " arguments."),
			forall(member([_,NMarg],Outliers),
					(	setof([File,Find],predicate(File,Find,_,[s(PName)|_],NMarg),Preds),
						forall(member([S,T],Preds),
							    (	fol(_,_,_,S,T,AIndex,_),
									write(Out,"%       "),write(Out,"has "), write(Out, NMarg),
									write(Out," arguments in axiom number "), write(Out,T), 
									write(Out, " ["),write(Out,AIndex),write(Out,"]"),
									write(Out," in file "), writeln(Out, S)
							    )
							  ) 
					)
				  )
		)
	  ),
	fail. 
print_warnings(Out):-
    setof(W,warning(-2,W),OddPatterns),
	writeln(Out,""),writeln(Out,""),
	writeln(Out, "%  Predicates with uncommon placement of variables (v) or constants (s):"), 
	forall(member(info(s(Pred),CommonPattern,CountCP,DiffPats),OddPatterns),
		(	write(Out, "%    \""),write(Out,Pred),write(Out, "\" most often ("),write(Out,CountCP),write(Out, ") used with arguments "),
			write(Out, CommonPattern),writeln(Out, ". Exceptions are: "),
			forall(member(DPat,DiffPats),
					(	setof([File,Find,FPred],pvnqloc([s(Pred)|DPat],File,Find,FPred),Places),
						forall(member([PFIL,PFIN,PFPR],Places),
								(	fol(_,_,_,PFIL,PFIN,AIndex,_),
									strip_sv(PFPR,StrippedPFPR),
									write(Out,"%       \""),write(Out, StrippedPFPR),write(Out,"\" in axiom "),write(Out,PFIN),
									write(Out," ["),write(Out,AIndex),write(Out,"]"),
									write(Out," in file "), writeln(Out, PFIL)
								)
							  )
					)
				  )
		)
	   ),
	fail.
print_warnings(Out):-
    setof(W,warning(-3,W),OddUses),
	writeln(Out,""),writeln(Out,""),
	writeln(Out, "%  Terms used less or equal than set in rare_term_use() in init-file:"), 
	forall(member(info(Term,Where),OddUses),
		(	write(Out, "%    \""),write(Out,Term),writeln(Out, "\" used in:"),
			forall(member([File,Ind],Where),
					(	fol(_,_,_,File,Ind,AIndex,_),
						write(Out,"%       axiom "),write(Out,Ind),
						write(Out," ["),write(Out,AIndex),write(Out,"]"),
						write(Out," in file "), writeln(Out, File)
					)
				  )
		)
	   ),
	writeln(Out, ""),
	fail.
print_warnings(Out):-
    setof(W,warning(-4,W),OntUses),
	writeln(Out,""),writeln(Out,""),
	missing_pred_percent(MPP),
	write(Out, "%  Terms not used in some relation which "), write(Out, MPP), writeln(Out, "% of terms do have. See missing_pred_percent() setting in init-file:"), 
	forall(member(info(Ont,Cont,PredOccs),OntUses),
			(	write(Out, "%    Comparing term/predicate occurrences "),
				(	Ont==Cont,
					write(Out, "internally in "), write(Out, Ont), writeln(Out, ":") 
				;	write(Out, "in "), write(Out, Ont), write(Out, " relative to "), write(Out, Cont), writeln(Out, ".")
				),
				forall(member(mps(Rel, Perc, Terms),PredOccs),
						(	write(Out, "%      Terms in "),write(Out,Ont),write(Out, " missing the relation \""),write(Out,Rel),
							write(Out, "\" while "),write(Out,Perc),write(Out,"% of terms in "),write(Out,Cont),writeln(Out," have it:"),
							sort(Terms,Terms1),
							forall(member(Term,Terms1),
									(	setof(File,constant(s(Term),File,_,_),Files),
										write(Out,"%          "),write(Out, Term),
										write(Out," in "), write_canonical(Out,Files),writeln(Out,"")
									)
								  )
						)
					  )
			)
		  ),
	   writeln(Out, ""),
	   fail.
print_warnings(Out):-
    setof(W,warning(-8,W),Ws),
	writeln(Out,""),writeln(Out,""),
	writeln(Out, "%  Variables not used in any predicate:"),
	forall(member(info(F,FLine,Q),Ws),
			(	fol(_,_,_,F,FLine,AIndex,_),
				write(Out, "%    \""),write(Out,Q),write(Out,"\" in axiom number "), write(Out,FLine), 
				write(Out, " ["),write(Out,AIndex),write(Out,"]"),
				write(Out," in file "), writeln(Out, F)
			)
		  ),
	fail.
print_warnings(Out):-
	findall([File,Q], (fol(q(Q),_,_,File,_,AID,_),string_concat(_,"unmarked",AID)),IFs),
	length(IFs,L),
	L>0,
	sort(1,@=<,IFs,IFs1),
	writeln(Out,""),writeln(Out,""),
	writeln(Out,"%  Axioms without index:"),
	fileparsed(_,X),
	memberchk([X,_],IFs1),
	write(Out,"%   "),
	writeln(Out, X),
	forall(member([X,Y],IFs1),
			(	write(Out,"%    "),
				writeln(Out, Y)
			)),
	fail.
print_warnings(Out):-
	setof(W, warning(-6,W), Tauters),
	length(Tauters,LT),
	counter(fol,NFol),
	writeln(Out,""),writeln(Out,""),
	write(Out, "%  "), write(Out, LT), write(Out, " out of "), write(Out, NFol),
	write(Out, " axioms generated clauses with trivial 'P and not(P)' disjunctions:"),writeln(Out, ""),
	writeln(Out, "%   <Axiom ID> / Comment"),
	writeln(Out, "%    <Axiom with implications replaced by disjunctions>"),
	forall(	member(info(FolNum, Index, Comment, SKfols, RetainedClauses, Tauts, TautClauses), Tauters),
			( 	writeln(Out, ""),
				write(Out, "%   "), write(Out, Index), write(Out, " / "), writeln(Out, Comment),
				tpex(_,FolNum,Clause,_,_,_,_),
				write(Out, "%    "), write_term(Out, Clause, [numbervars(true),quoted(true)]), writeln(Out, ""),
				plus(RetainedClauses, TautClauses, Total),
				write(Out, "%     "), write(Out, RetainedClauses), write(Out, " retained clauses out of "),
				write(Out, Total), writeln(Out, ""),
				forall(	member([_,_,E],SKfols),					% for each clause of the axiom
						(	E = kow(true,_),
								write(Out,"%      "),write_term(Out, E, [numbervars(true),quoted(true)]),writeln(Out,"")
						;	E = kow(if(IF),_),
								write(Out,"%      "),write_term(Out, E, [numbervars(true),quoted(true)]),writeln(Out,"")
						)
					  ),
				write(Out, "%     "), write(Out, TautClauses), write(Out, " removed clauses out of "),
				write(Out, Total), writeln(Out, ""),
				forall(	member([Taut,IF,THEN], Tauts),
						(	write(Out, "%      "), write(Out, Taut), write(Out, " -- in: "),
							write(Out,IF), write(Out, " --> "),writeln(Out, THEN))
					  )
			)
		  ),
	fail.
print_warnings(Out):-
	findall([AID,Q], (fol(q(Q),_,_,_,_,AID,_),\+string_concat(_,"unmarked",AID)),IFs),
	findall(X, fol(_,_,_,_,_,X,_),Xs),
	sort(Xs,Xs1),
	collate(Xs1,IFs,[],Doubles),
	length(Doubles,LD),
	LD>0,
	forall(	member([Axiom,QF],Doubles), 
		( sort(QF,QF1),length(QF1,L),
		  (	L>1,
			writeln(Out,""),writeln(Out,""),
			writeln(Out,"%  Axiom indices used in distinct axiom comments:"),
			write(Out,"%   "),
			write(Out, Axiom),
			writeln(Out, ": "),
			member(QC, QF1),
			fol(q(QC),_,_,File,_,Axiom,_),
			write(Out,"%     "),
			write(Out, File),
			write(Out, ": "),
			writeln(Out, QC),
			fail
		 ;	true)
		)),
	fail.
print_warnings(Out):-
	warning(-7,Doubles),
	writeln(Out,""),writeln(Out,""),
	writeln(Out,"%  Axiom indices occurring in multiple axiom files:"),
	forall(	member([Axiom,Files],Doubles), 
			( 	write(Out,"%   "),
				write(Out, Axiom),
				write(Out, ": "),
				writeln(Out, Files)
			)),
	fail.
print_warnings(Out):-
    findall(W,warning(-5,info(W)),DuplexAxioms),
	DuplexAxioms \== [],
	writeln(Out,""),writeln(Out,""),
	writeln(Out, "%  Axioms more than once included:"),
	writeln(Out, "%   <Axiom with implications replaced by disjunctions>"),
	writeln(Out, "%     <Axiom ID> / <Unique ID>"),
	forall(member(Info,DuplexAxioms),
			 ( 	(	is_list(Info)
						->	write(Out, "%   "),
							write_term(Out, Info, [numbervars(true),quoted(true)]),
							writeln(Out,"")
				;	writeln(Out,Info))
		     )
		   ),
	fail.	
print_warnings(Out):-
	writeln(Out,""),writeln(Out,""),
	writeln(Out,"% PROCESSING INFORMATION"),
	writeln(Out,"%  Files Processed:"),
	writeln(Out,"%  <Unique ID>/<Order in axiom file>/<Comment>:"),
	findall([N,X],fileparsed(N,X),Files),
	sort(1,@=<,Files,SFiles),
	forall(member([Num,Name],SFiles),
		(	writeln(Out, ""),
			write(Out,"%   "),
			write(Out, Num),
			write(Out, ". "),
			writeln(Out,Name),
			findall([Ind, FInd, Q],fol(q(Q),Ind,_,Name,FInd,_,_),Bag),
			sort(1, @=<, Bag, BagO),
			forall(member([P,S,T], BagO), 
			(	write(Out,"%      "),
				write(Out,P),
				write(Out, " / "),
				write(Out,S),
				write(Out, " / "),
				writeln(Out, T)
			))
		)),
	fail.
print_warnings(_):-!.
	

saveData(nnf, File) :-			%% i		%% save file. Program will fail if a file with that name is open!!!	
   setup_call_cleanup(					%% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
	   print_struct(Out),
	   close(Out)),!.
saveData(rules_per_axiom, File) :-			%% i		%% save file. Program will fail if a file with that name is open!!!	
   setup_call_cleanup(					%% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
	   printrules(Out),
	   close(Out)),!.
saveData(vocabulary, File) :-	
	findall(X,nonquant(X,_),Xs),
	sort(Xs,Constants),
	findall(Y,predname(Y),Ys),
	sort(Ys,Prednames),
    setup_call_cleanup(					%% ... it will overwrite the file with the same name when it is closed.
       open(File, write, Out),
	   print_vocab(Out,Constants,Prednames),
	   close(Out)),!.
saveData(cf, File) :-			
   setup_call_cleanup(					
       open(File, write, Out),
	   printcf(Out),
	   close(Out)),!.
saveData(nsat, File) :-			
   setup_call_cleanup(					
       open(File, write, Out),
	   print_nsat(Out),
	   close(Out)),!.
saveData(kowalski, File) :-			
   setup_call_cleanup(					
       open(File, write, Out),
	   print_kowalski(Out),
	   close(Out)),!.
saveData(satchmo, File) :-			
   setup_call_cleanup(					
       open(File, write, Out),
	   print_satchmo(Out),
	   close(Out)),!.
saveData(cnf, File) :-			
   setup_call_cleanup(					
       open(File, write, Out),
	   printcnf(Out),
	   close(Out)),!.

print_struct(Out):-
	tpex(_,Ind,Axiom,_,_,ID,_),
	(	Axiom = [and |ANDS]
			->	write_qfs(Out,ANDS,ID,Ind)
	;	write_qf(Out,ID,Ind,Axiom)
	), fail.
print_struct(_):-!.


write_qfs(_,[],_,_):-!.
write_qfs(Out,[Axiom|T],ID,Ind):-
	write_qf(Out,ID,Ind,Axiom),
	!, write_qfs(Out,T,ID,Ind).

write_qf(Out,ID,Ind,Axiom):-
	write(Out, "nnf(\""),
	write(Out, ID),
	write(Out, "\","),
	write(Out, Ind),
	write(Out, ","),
	write(Out, Axiom),
	writeln(Out, ")."),
	!.
	

printcf(Out):-
	writeln(Out,"% Clausal form: each separate clause is a list of disjunctions."),
	writeln(Out,""),
	fol(q(Q),A,_, _, _,AxID,_),
	writeln(Out,""),
	write(Out, "% "),
    writeln(Out, Q),
	fol_cnf(A,CNF),
	replace_cf(CNF,CNF2),
	sort(CNF2,CNF3),
	list_depth(CNF3, LD),
	plus(LD, -2, LDS),
	increment(posax,N),
	atomics_to_string(["posax(",N,",",LDS,","],Lead),
	write(Out, Lead),
	write(Out, "\""), write(Out, AxID), write(Out, "\","),
	write_term(Out, CNF3, [numbervars(true),quoted(true)]),
	writeln(Out,")."),
	fail.
printcf(_):-!.

print_nsat(Out):-
	writeln(Out,"% Clausal form of negated axioms: each separate clause is a list of disjunctions."),
	writeln(Out,""),
	fol(q(Q),A,_, _, _,AxID,_),
	writeln(Out,""),
	write(Out, "% "),
    writeln(Out, Q),
	fol_cnf(A,CNF),
	replace_cf(CNF,CNF2),
	sort(CNF2,CNF3),
	increment(negax,N),
	atomics_to_string(["negax(",N,","],Lead),
	write(Out, Lead),
	write(Out, "\""), write(Out, AxID), write(Out, "\","),
	write_term(Out, CNF3, [numbervars(true),quoted(true)]),
	writeln(Out,")."),
	fail.
print_nsat(_):-!.


printrules(Out):-
       fol(q(Q),A,_, F, _,_,_),
	   writeln(Out,""),
	   write(Out, "% "),
       writeln(Out, Q),
	   fol_rule(A,Rule),
	   p_fol_rule(Q,Rule,F,Out),
	   fail.
printrules(_):-!.

printcnf(Out):-
       fol(q(Q),_,B, _, _, _, _),
	   writeln(Out,""),
	   write(Out, "% "),
       writeln(Out, Q),
	   writeln(Out, B),
	   fail.
printcnf(_):-!.


print_kowalski(Out):-
       findall([X,Y,Z],fol(q(Z),X, _, _, _, Y,_),Kfols),				% select all axioms
	   forall(member([A,Between,Q],Kfols),								% for each axiom ...
				(	writeln(Out,""),
					write(Out, "% "),
					writeln(Out, Q),
					findall([Taut,IF,THEN], taut(A,Taut,IF,THEN), Tauts),
					findall([SK,SK2,E],fol_kow(A,SK,SK2,E),SKfols),		% select all clauses for axiom under scrutiny
					length(SKfols, RetainedClauses),
					forall(member([SK,SK2,E],SKfols),					% for each clause of the axiom
							(	increment(rkow,R),						% generate clause number
								(	E = kow(true, _),
									atomics_to_string(["r(",R,",",0,","],S),write(Out,S),write(Out,SK),write(Out,","),write(Out,SK2),
									write(Out,",\""),write(Out, Between),
									write(Out,"\","),write_term(Out, E, [numbervars(true),quoted(true)]),writeln(Out,").")
								;	E = kow(if(IF),_),
									length(IF,L),
									atomics_to_string(["r(",R,",",L,","],S),write(Out,S),write(Out,SK),write(Out,","),write(Out,SK2),
									write(Out,",\""),write(Out, Between),
									write(Out,"\","),write_term(Out, E, [numbervars(true),quoted(true)]),writeln(Out,").")
								),
								pred_use(A,R,Between,E),
								assertz(sk_in_clause(A,Between,R,SK,SK2))
								/* create rr() for removing function number from skolems */
							)
						  ),
					(	Tauts \== []
							-> 	length(Tauts, TautClauses),
								writeln(Out, "% Removed trivial tautological disjunctions for 'P and not(P)':"),
								forall(	member([Taut,IF,THEN], Tauts),
										(	increment(rkow,R),
											write(Out,"% P = -- "), write(Out, Taut), write(Out, " -- in: "),
											write(Out,IF), write(Out, " --> "),writeln(Out, THEN))
									  ),
								assertz(warning(-6,info(A, Between, Q, SKfols, RetainedClauses, Tauts, TautClauses)))
					;	true)
				)
			),!.


pred_use(FolInd,KowID,AxID,Rule):-
	sub_term(ST,Rule),
	predname(s(ST)),
	fol(_,FolInd,Axiom,_,_,_,_),
	(	memberNestList([s(ST)|Args],Axiom),
		member(v(_),Args)
			-> G = v ; G = c	),
	atom_string(AxID,Axs),
	assertz_once(p_in(ST,G,KowID,Axs)),
	fail.
pred_use(_,_,_,_).

print_satchmo(Out):-
	nonquant(A,_),
	write(Out,"true--->dom("),
	write_term(Out,A,[quoted(true)]),
	writeln(Out,")."),fail.
print_satchmo(Out):-			%% according to the 1987 Satchmo paper which is different from 1988
	skolems(A),
	A=..[_|L],
	domize(Out,L),
	write(Out,"--->dom("),
	write_term(Out,A,[numbervars(true),quoted(true)]),
	writeln(Out,")."),fail.
print_satchmo(Out):-
	fol_sat(A,kow(if(IF),false)),
	print_sat_comment(Out, A),
	print_sat_atoms(Out, ",", IF),
	writeln(Out,"--->false."),fail.
print_satchmo(Out):-
	fol_sat(A,kow(true,then(THEN))),
	print_sat_comment(Out, A),
	write(Out,"true--->"),
	print_sat_atoms(Out, _, THEN),
	writeln(Out, "."),fail.
print_satchmo(Out):-
	fol_sat(A,kow(true,then_or(THEN))),       
	print_sat_comment(Out, A),
	write(Out,"true--->"),
	print_sat_atoms(Out, ";", THEN),
	writeln(Out, "."),fail.
print_satchmo(Out):-
	fol_sat(A,kow(if(IF),then(THEN))),
	print_sat_comment(Out, A),
	print_sat_atoms(Out, ",", IF),
	write(Out,"--->"),
	print_sat_atoms(Out, _, THEN),
	writeln(Out, "."),fail.
print_satchmo(Out):-
	fol_sat(A,kow(if(IF),then_or(THEN))),
	print_sat_comment(Out, A),
	print_sat_atoms(Out, ",", IF),
	write(Out,"--->"),
	print_sat_atoms(Out, ";", THEN),
	writeln(Out, "."),fail.
print_satchmo(_):-!.

domize(_,[]):-!.
domize(Out,[H|T]):-
	write_term(Out,dom(H),[numbervars(true),quoted(true)]),
	(	T\==[],
		write(Out,",")
	; true ),
	!,domize(Out,T).

print_sat_comment(Out, A):-
	fol(q(Q),A, _, _, _, _,_),
	writeln(Out,""),
	write(Out, "% "),
    writeln(Out, Q),!.

print_sat_atoms(_,_, []):-!.
print_sat_atoms(Out, Delim, [[s(P)|A]|T]):-
	(	P=='=',
		Term=..[identical|A]
	;	Term=..[P|A]
	),
	write_term(Out,Term,[numbervars(true),quoted(true)]),
	(	T\==[],
		write(Out,Delim)
	; true ),
	!, print_sat_atoms(Out, Delim, T).
print_sat_atoms(Out, _, [s(P)|A]):-
	(	P=='=',
		Term=..[identical|A]
	;	Term=..[P|A]
	),
	write_term(Out,Term,[numbervars(true),quoted(true)]),!.



print_vocab(Out,Constants,Prednames):-
	   writeln(Out, "% CONSTANTS USED:"),
	   print_uses(Out,Constants,"ot"),			%% ontology-terms
	   writeln(Out,""),
	   writeln(Out,""),
	   writeln(Out, "% PREDICATES USED:"),
	   print_uses(Out,Prednames,"pr"),			%% predicate names
	   writeln(Out,""),
	   writeln(Out,""),
	   writeln(Out, "% VARIABLES USED:"),
	   print_vars(Out),
	   !.

print_uses(_,[],_):-!.
print_uses(Out,[H|R],F):-
	write(Out,F),write(Out,"("),write(Out,H),writeln(Out,")."),		%% print in loadable format
	findall(X,term_in_predicate(H,X),Preds),
	sort(Preds,Predicates),
	print_preds(Out,Predicates),
	!, print_uses(Out,R, F).

print_preds(_,[]):-!.
print_preds(Out,[H|R]):-
	write(Out,"   % "),
	writeln(Out,H),
	!,print_preds(Out,R).

print_vars(Out):-
	quantvar(X),
	write(Out,"  % "),
	writeln(Out,X),
	fail.
print_Vars(_):-!.


% Called after each axiom parse, thus without global information about all axioms
% i,i,i,i
%	axiom in Prolog list representation, implications replaced by disjunctions, variables standardized
%	filename in which axiom
%	n'th axiom in file 
%	unique index of axiom over all axiom files
preds_saved(Axiom, F1, FLine, FolInd):-
	folres(F),								% F is the list of reserved FOL words
	outdiscourses(O),						% O is the list of declared outdiscourse terms
	isListComp(X,Axiom),					% backtrack over each member of all lists at all depths of the axiom
	( \+is_list(X), 						% if such member is not a list
		\+member(X,F),						%	and not a reserved FOL word
		\+member(X,[s(identical)|O]),		%	and not 's(identical)', neither any of the outdiscourse terms
		X\=v(_),							%	and not a standaridzed variable
		asserta_once(nonquant(X,0)),		% then register the member as a not-quantified term
		asserta_once(constant(X,F1,FLine,FolInd)),
		ont(Ont,F1),
		increment(X,_),
		increment(c(Ont,X),_),
		X=s(Constant),
		minimum_constant_length(MCL),		%	and check whether its length is greater than the minimum length specified in the init-file
		write_length(Constant, WL, []),
		(	WL < MCL
			-> 	assertz_once(error(2, info(F1, FLine, Constant)))
		; true)
	; X=[H|R],								% If the member is a list
		\+member(H,[s(identical)|O]),		%	but the first member of that list is neither 's(identical)' or an oudiscourse term
		\+member(H,F),						%	and not a reserved FOL word
		H\=v(_),							%	and not a standardized variable
		H=s(S),
		assertz_once(error(3,info(F1,FLine,S))),
		pred_template_v(X,VX1), 				%	save as v-template
		pred_template_vnq(X,VX1,F1,FLine),		%	save as vnq-template
		length(R,LR),
		asserta_once(predicate(F1,FLine,FolInd,[H|R],LR))
	; X=[H|R],								% If the member is a list
		member(H,[s(identical)|O]),			%	check whether the first member of that list is either 's(identical)' or an oudiscourse term
		pred_template_v(X,VX2), 				%	save as v-template
		pred_template_vnq(X,VX2,F1,FLine), 		%	save as vnq-template
		length(R,LR),
		asserta_once(predicate(F1,FLine,FolInd,[H|R],LR))
	),
	fail.
preds_saved(_,_,_,_):-!.


% i,o
pred_template_v([H|R],Out):-
	setof(v(X),member(v(X),R), L),		% collect the asserted variables in L
	length(L,N),						% determine L's length
	length(P,N),						% create a new list P of length L with Prolog variables
	maplist(=(v),P),					% replace all Prolog variables in P with 'v'
	replace2(L,P,[H|R],Out),			% replace all elements in [H|R] which are in L with what is in the same position in P 
	asserta_once(pred_v(Out)),			% save the v-template
	length([H|R],LHR),					% determine the number of arguments of the predicate
	plus(LHR,-1,ArgNum),
	increment(p(H,ArgNum),_),!.			% increase the number of times the predicate's name is used with that number of arguments
pred_template_v([H|R],[H|R]):-			% if there are no v(...) arguments, store as such
	length([H|R],LHR),
	plus(LHR,-1,ArgNum),
	increment(p(H,ArgNum),_),
	asserta_once(pred_v([H|R])),!.

% i,i,i
pred_template_vnq(Pred,[H|R],F1,FLine):- 				%	save as vnq-template
	setof(s(X),member(s(X),R), L),
	length(L,N),
	length(P,N),
	maplist(=(c),P),
	replace2(L,P,[H|R],Out),
	increment(pred_vnq(Out),_),
	asserta_once(pvnqloc(Out,F1,FLine,Pred)),
	asserta_once(pred_vnq(Out)),!.
pred_template_vnq(Pred,[H|R],F1,FLine):-
	increment(pred_vnq([H|R]),_),
	asserta_once(pvnqloc([H|R],F1,FLine,Pred)),
	asserta_once(pred_vnq([H|R])),!.


term_in_predicate(Term,Pred):-
	pred_v(Pred),
	member(Term,Pred).
	
strip_sv(In,Out):-
	strip_sv2(In,[],Out,0),!.
	
strip_sv2([],In,Out,_):-
	reverse(In,Out),!.
strip_sv2([s(X)|T],In,Out,Var):-
	!,strip_sv2(T,[X|In],Out,Var).
strip_sv2([v(_)|T],In,Out,Var):-
	plus(Var,1,NewVar),
	atomic_list_concat([v,NewVar],OutVar),
	!,strip_sv2(T,[OutVar|In],Out,Var).
strip_sv2([A|T],In,Out,Var):-
	!,strip_sv2(T,[A|In],Out,Var).


	
%% --------------

nots_moved_inwards(In, Out):-
	isListComp([s(not),[s(and)|ANDS]],In),
	nots_list(ANDS,[],Or_Nots),
	replace2([[s(not),[s(and)|ANDS]]],[[s(or)|Or_Nots]],In,Out1),
	!,nots_moved_inwards(Out1, Out).
nots_moved_inwards(In, Out):-
	isListComp([s(not),[s(or)|ORS]],In),
	nots_list(ORS,[],And_Nots),
	replace2([[s(not),[s(or)|ORS]]],[[s(and)|And_Nots]],In,Out1),
	!,nots_moved_inwards(Out1, Out).
nots_moved_inwards(In, Out):-
	isListComp([s(not),[s(not), NOT]],In),
	replace2([[s(not),[s(not),NOT]]],[NOT],In,Out1),
	!,nots_moved_inwards(Out1, Out).
nots_moved_inwards(In, Out):-
	isListComp([s(not),[s(forall), VARS, SCOPE]],In),
	replace2([[s(not),[s(forall), VARS, SCOPE]]],[[s(exists),VARS, [s(not),SCOPE]]],In,Out1),
	!,nots_moved_inwards(Out1, Out).
nots_moved_inwards(In, Out):-
	isListComp([s(not),[s(exists), VARS, SCOPE]],In),
	replace2([[s(not),[s(exists), VARS, SCOPE]]],[[s(forall),VARS, [s(not),SCOPE]]],In,Out1),
	!,nots_moved_inwards(Out1, Out).
%% the following two are not not-movers, but take in the same sweep care of or/and lists with only one element.
nots_moved_inwards(In, Out):-
	isListComp([s(and),X],In),
	replace2([[s(and),X]],[X],In,Out1),
	!,nots_moved_inwards(Out1, Out).
nots_moved_inwards(In, Out):-
	isListComp([s(or),X],In),
	replace2([[s(or),X]],[X],In,Out1),
	!,nots_moved_inwards(Out1, Out).
nots_moved_inwards(In, In):-!.


nots_list([],In,In):-!.
nots_list([H|R],In,Out):-
	!,nots_list(R,[[s(not),H]|In],Out).
	
	
multiply_scoped_vars_renamed(In, Out):-
	setof(X, isExtQuantified(X, In), ExtVars),
	setof(Y, isUniQuantified(Y, In), UniVars),
	intersection(ExtVars,UniVars,Vars),
	resolveVars(Vars,In,Out),!.
multiply_scoped_vars_renamed(In, In):-!.	%% because setof does not return empty lists.


resolveVars([],In,In):-!.
resolveVars(A,In,In):-			%% NEED TO WRITE SECOND STANDARDIZATION BUT THERE ARE NO EXAMPLES IN BFO2020 FOR IT
		writeln(A),!.


skolemize(FormulaIn, FormulaOut):-
	setof([X,Y], isInScope(FormulaIn,X,Y), ScopedEvars),			%% ScopedEvars: all ex.quant vars under the scope of u.quant vars
	setof(X1, isListComp([s(exists),X1,_],FormulaIn), AllEvars1),
	flatten(AllEvars1, AllEvars),  	%% AllEvars: all ex,quant vars
	scopeOfEvars(ScopedEvars),
	findall(Evar,scopedEvar(Evar,_),Evars),
	nonscopedEvars(AllEvars,Evars,NonScopedEvars,SkolemConstants),
	findall(Function,scopedEvar(_,Function),SkolemFunctions),
	( skolem_mode(scoped),
		retractall(scopedEvar(_,_)),
		replace2(Evars,SkolemFunctions,FormulaIn,FormulaOut1),
		( NonScopedEvars \== [],
			replace2(NonScopedEvars,SkolemConstants,FormulaOut1,FormulaOut)
		; FormulaOut = FormulaOut1)
	; skolem_mode(mapped),
		FormulaOut=FormulaIn
	),
	!.
skolemize(FormulaIn, FormulaOut):-
	setof(X1, isListComp([s(exists),X1,_],FormulaIn), AllEvars1), 	%% AllEvars: all ex,quant vars
	flatten(AllEvars1, AllEvars), 
	nonscopedEvars(AllEvars,[],NonScopedEvars,SkolemConstants),		
	( skolem_mode(scoped),
		NonScopedEvars \== [],
		replace2(NonScopedEvars,SkolemConstants,FormulaIn,FormulaOut)
	; skolem_mode(mapped),
		FormulaOut=FormulaIn
	),
	!.
skolemize(FormulaIn, FormulaIn):-!.

isInScope(Formula,Evars,Uvars):-
	isListComp([s(forall),Uvars,Uscope],Formula),
	isListComp([s(exists),Evars,_],Uscope).

nonscopedEvars([],_,[],[]):-!.
nonscopedEvars(AllEvars,ScopedEvars,NonScopedEvars,Constants):-
	skolemconsts(AllEvars,ScopedEvars,[],NonScopedEvars,[],Constants),!.

skolemconsts([],_,In1,In1,In2,In2):-!.
skolemconsts([H|R],ScopedEvars,In1,Out1,In2,Out2):-
	( \+memberchk(H,ScopedEvars),
	  increment(function,F),
	  !, skolemconsts(R,ScopedEvars,[H|In1],Out1,[[e,F,[]]|In2],Out2)
	;!,skolemconsts(R,ScopedEvars,In1,Out1,In2,Out2)).


scopeOfEvars([]):-!.
scopeOfEvars([[Evars,Uvars]|R]):-
	scopeOfEvars2(Evars,Uvars),!,
	scopeOfEvars(R).

scopeOfEvars2([],_):-!.
scopeOfEvars2([H|R],Uvars):-
	scopedEvar(H,[e,F,U]),
	retract(scopedEvar(H,[e,F,U])),
	flatten([U|Uvars],Out),
	list_to_set(Out,Out1),
	assert(scopedEvar(H,[e,F,Out1])),!,
	scopeOfEvars2(R,Uvars).
scopeOfEvars2([H|R],Uvars):-
	increment(function,F),
	assert(scopedEvar(H,[e,F,Uvars])),!,
	scopeOfEvars2(R,Uvars).

removeQuantifiers(In, Out):-
	isListComp([s(forall),Vars, Scope],In),
	replace2([[s(forall),Vars, Scope]],[Scope],In,Out1),
	!,removeQuantifiers(Out1, Out).
removeQuantifiers(In, Out):-
	isListComp([s(exists),Vars, Scope],In),
	replace2([[s(exists),Vars, Scope]],[Scope],In,Out1),
	!,removeQuantifiers(Out1, Out).
%% for the two below: remove in same sweep 'ors of ors' and 'ands of ands' after quantifier removal
removeQuantifiers(In, Out):-
	isListComp([s(and)|Ands],In),
	member([s(and)|Ands1],Ands),
	replace2([[s(and)|Ands1]],[[]],[s(and)|Ands],FL),
	remove_element([],FL,[],FL2),
	append(FL2,Ands1,FL3),
	remove_element(s(and),FL3,[],FL4),
	replace2([[s(and)|Ands]],[[s(and)|FL4]],In,Out1),
	!,removeQuantifiers(Out1, Out).
removeQuantifiers(In, Out):-
	isListComp([s(or)|Ands],In),
	member([s(or)|Ands1],Ands),
	replace2([[s(or)|Ands1]],[[]],[s(or)|Ands],FL),
	remove_element([],FL,[],FL2),
	append(FL2,Ands1,FL3),
	remove_element(s(or),FL3,[],FL4),
	replace2([[s(or)|Ands]],[[s(or)|FL4]],In,Out1),
	!,removeQuantifiers(Out1, Out).
removeQuantifiers(In, In):-!.

	
disAndInOr(Formula,Out):-
	isListComp([s(or)|OrList],Formula),
	member([s(and)|AndList],OrList),
	remove_element([s(and)|AndList],OrList,[],FL),
	disAndInOr2(FL,AndList,[],Dist),
	replace2([[s(or)|OrList]],[Dist],Formula,Out1),
	removeQuantifiers(Out1,Out2),
	!,disAndInOr(Out2,Out).
disAndInOr(Formula,Formula):-!.


disAndInOr2(_,[],In,[s(and)|In]):-!.
disAndInOr2(Or,[And|R],In,Out):-
	append([s(or),And],Or,Ored),!,
	disAndInOr2(Or,R,[Ored|In],Out).


put_in_clausal_form(Ind,[s(or)|R]):-
	store_cf_forms2(Ind, R),!.
put_in_clausal_form(Ind,[s(and)|R]):-
	put_in_clauses(Ind,R),!.
put_in_clausal_form(Ind,R):-
	put_in_clauses(Ind,R),!.

put_in_clauses(_,[]):-!.
put_in_clauses(Ind,[[s(or)|H]|R]):-		%% when there is an and-list of or-ed clauses
	store_cf_forms2(Ind,H),!,
	put_in_clauses(Ind,R).
put_in_clauses(Ind,[H|R]):-				%% when there is only an and-list of clauses
	is_list(H),							%% test whether it is a clause, if not, go next
	store_cf_forms1(Ind, H),!,
	put_in_clauses(Ind,R).
put_in_clauses(Ind,[H|R]):-				%% for individual clauses
	store_cf_forms1(Ind,[H|R])
	,!.


store_cf_forms1(Ind,Clause):-
	variable_mode(ground),
		re_standardize_vars(Clause,Hout),
		store_cnf(Ind,[Hout]),
		store_kowalski(ground,Ind,[Hout]),
		fail.
store_cf_forms1(Ind,Clause):-
	variable_mode(unbound),
		varclauses(Clause,Hout2),
		store_cnf(Ind,[Hout2]),
		store_kowalski(unbound,Ind,[Hout2]),
		fail.
store_cf_forms1(Ind,Clause):-
	outputfile(satchmo),					%% note switching of ground/unbound consequences as for satchmo both are needed
	(	variable_mode(ground),
		varclauses(Clause,Hout2),
		store_kowalski(satchmo,Ind,[Hout2])
	;	variable_mode(unbound),
		re_standardize_vars(Clause,Hout),
		store_kowalski(satchmo,Ind,[Hout])
	),!. 
store_cf_forms1(_,_):-!.

store_cf_forms2(Ind,Clause):-
	variable_mode(ground),
		re_standardize_vars(Clause,Hout),
		store_cnf(Ind,Hout),
		store_kowalski(ground,Ind,Hout),		%% note difference in 'Hout' rather than '[Hout]'
		fail.
store_cf_forms2(Ind,Clause):-
	variable_mode(unbound),
		varclauses(Clause,Hout2),
		store_cnf(Ind,Hout2),
		store_kowalski(unbound,Ind,Hout2),
		fail.
store_cf_forms2(Ind,Clause):-
	outputfile(satchmo),					%% note switching of ground/unbound consequences as for satchmo both are needed
	(	variable_mode(ground),
		varclauses(Clause,Hout2),
		store_kowalski(satchmo,Ind,Hout2)
	;	variable_mode(unbound),
		re_standardize_vars(Clause,Hout),
		store_kowalski(satchmo,Ind,Hout)		%% note difference in 'Hout' rather than '[Hout]'
	),!. 
store_cf_forms2(_,_):-!.


% i,i,i
% processes only one clause after clausification
store_kowalski(UGS, Ind, List):-	% List contains both ground and unground representation for variables
	increment(kow,K),
	orphaned_func(Ind,List),
%	replace_eFunc(List,List1),
%	partition(is_neg,List1,Neg,Pos),
	partition(is_neg,List,Neg,Pos),
	sort_pos(Pos,Pos1),
	sort_neg(Neg,[],Neg1),	
	(	tautology(Neg,Pos,Both) 					/* don't use clause if a neg one is also pos one */
			->	(	variable_mode(UGS)
					->	replace(Neg1,NegT),
						replace(Pos1,PosT),
						replace(Both,BT),
						assertz(taut(Ind,BT,NegT,PosT))
				;	true)
		;	range_restricted(f1(Neg1,Pos1),Neg1),
			( outputfile(rules_per_axiom),
			variable_mode(UGS),
			store_rules(Ind, K, Neg1, Pos1)
			; true ),
			( (outputfile(kowalski) ; outputfile(satchmo)),
				findall(X,sub_term([e,X,_],Pos1),Xs),						% collect in Xs the indexes of the skolems
				sort(Xs, Xys),				% remove duplicates and sort
				( Neg1 \== [],
					(	variable_mode(UGS),   
						findall(XX,sub_term([e,XX,_],Neg1),XXs),						% collect in Xs the indexes of the skolems
						sort(XXs, XXys),												% remove duplicates and sort
						replace(kow(if(Neg1),Pos1),E1),
						assertz(fol_kow(Ind,Xys,XXys,E1)),
						assertz(fol_sat(Ind,kow(if(Neg1),Pos1)))
					; true),
					(	UGS == satchmo,
						assertz(fol_sat(Ind,kow(if(Neg1),Pos1)))
					; true)
				;	(	variable_mode(UGS),   
						replace(kow(true,Pos1),E2),
						assertz(fol_kow(Ind,Xys,[],E2)),
						assertz(fol_sat(Ind,kow(true,Pos1)))
					; true),
					(	UGS == satchmo,
						assertz(fol_sat(Ind,kow(true,Pos1)))
					; true)
				)
			; true 
			)
	),!.

% i,i,o
tautology(N,P,A):-
	member([s(not),A], N), 
	member(A, P),!. 
	

range_restricted(_,B):-ground(B),!.		%% only first clause executable. Work in progress.
range_restricted(A,B):-
	term_variables(B,VarList),
	length(VarList,L),
	length(List,L),
	maplist(=(a), List),
	VarList=List,writeln(A).

store_rules(Ind, K, [], then_or(THEN)):-
	store_ors(Ind, K, [], THEN),!.
store_rules(Ind, _, [], then(THEN)):-
	store_facts(Ind, [THEN]),!.
store_rules(Ind, K, IF, false):-
	store_falses(Ind,K, IF,[],Out),
	( Out = [R],
	  assertz(fol_rule(Ind, rule(R,"\"-->\"",[por(inconsistent,_,_,_)])))
	; assertz(fol_rule(Ind, rule(por(inconsistent,_,_,_),"\"<--\"",Out)))
	),!.
store_rules(Ind, K, IF, then([Pred,A1,A2,A3])):-
	store_horn(Ind, K, IF,[],Out),
	( Out = [R],
	  assertz(fol_rule(Ind, rule(R, "\"-->\"",[por(true,A1,Pred,A2,at,A3)])))
	; assertz(fol_rule(Ind, rule(por(true,A1,Pred,A2,at,A3),"\"<--\"",Out)))
	),!.
store_rules(Ind, K, IF, then([Pred,A1,A2])):-
	store_horn(Ind,K, IF,[],Out),
	( Out = [R],
	  assertz(fol_rule(Ind, rule(R, "\"-->\"",[por(true,A1,Pred,A2)])))
	; assertz(fol_rule(Ind, rule(por(true,A1,Pred,A2),"\"<--\"",Out)))
	),!.
store_rules(Ind, K, IF, then([Pred|[A1|A]])):-
	store_horn(Ind,K, IF,[],Out),
	T=..[por|[true|[A1|[Pred|A]]]],
	( Out = [R],
		assertz(fol_rule(Ind, rule(R,"\"-->\"",[T])))
	; assertz(fol_rule(Ind, rule(T,"\"<--\"",Out)))
	),!.
store_rules(Ind, K, IF, then_or(Preds)):-
	store_ors(Ind, K, IF, Preds),!.
store_rules(_, _, IF, Preds):-
	writeln("Not processed: "),
	write("   "),writeln(IF),	
	write("   "),writeln(Preds),!.	


store_facts(_,[]):-!.
store_facts(Ind, [[Pred,A1,A2,A3]|R]):-
	assertz(fol_rule(Ind,rule(por(true,A1,Pred,A2,at,A3),"\"<--\"",[por(_,_,_,_)]))),
	!,store_facts(Ind, R).
store_facts(Ind, [[Pred,A1,A2]|R]):-
	assertz(fol_rule(Ind, rule(por(true,A1,Pred,A2),"\"<--\"",[por(_,_,_,_)]))),
	!,store_facts(Ind, R).
store_facts(Ind, [[Pred|[A1|A]]|R]):-
	T=..[por|[true|[A1|[Pred|A]]]],
	assertz(fol_rule(Ind, rule(T,"\"<--\"",[por(_,_,_,_)]))),
	!,store_facts(Ind, R).

store_falses(_,_,[],In,In):-!.
store_falses(Ind,K,[[Pred,A1,A2,A3]|R],In,Out):-!,
	store_falses(Ind,K,R,[por(true,A1,Pred,A2,at,A3)|In],Out).
store_falses(Ind,K,[[Pred,A1,A2]|R],In,Out):-!,
	store_falses(Ind,K,R,[por(true,A1,Pred,A2)|In],Out).
store_falses(Ind, K, [[Pred|[A1|A]]|R], In, Out):-
	T=..[por|[true|[A1|[Pred|A]]]],
	!,store_falses(Ind, K, R, [T|In], Out).


store_ors(_,_,_,[]):-!.
store_ors(Ind, K, IF, [[Pred,A1,A2,A3]|R]):-
	atomics_to_string([maybe,":",K],S),
	store_horn(Ind,K, IF, [], Out),
	( Out \= [], Out1 = Out ; Out1 = [por(_,_,_,_)]),
	assertz(fol_rule(Ind, rule(por(S,A1,Pred,A2,at,A3),"\"<--\"",Out1))),
	!,store_ors(Ind, K, IF, R).
store_ors(Ind, K, IF, [[Pred,A1,A2]|R]):-
	atomics_to_string([maybe,":",K],S),
	store_horn(Ind,K, IF, [], Out),
	( Out \= [], Out1 = Out ; Out1 = [por(_,_,_,_)]),
	assertz(fol_rule(Ind, rule(por(S,A1,Pred,A2),"\"<--\"",Out1))),
	!,store_ors(Ind, K, IF, R).
store_ors(Ind, K, IF, [[Pred|[A1|A]]|R]):-
	atomics_to_string([maybe,":",K],S),
	store_horn(Ind,K, IF, [], Out),
	T=..[por|[S|[A1|[Pred|A]]]],
	( Out \= [], Out1 = Out ; Out1 = [por(_,_,_,_)]),
	assertz(fol_rule(Ind, rule(T,"\"<--\"",Out1))),
	!,store_ors(Ind, K, IF, R).


store_horn(_,_,[],In,In):-!.
store_horn(Ind,K,[[Pred,A1,A2,A3]|R],In,Out):-!,
	store_horn(Ind,K,R,[por(true,A1,Pred,A2,at,A3)|In],Out).
store_horn(Ind,K,[[Pred,A1,A2]|R],In,Out):-!,
	store_horn(Ind,K,R,[por(true,A1,Pred,A2)|In],Out).
store_horn(Ind, K, [[Pred|[A1|A]]|R], In, Out):-
	T=..[por|[true|[A1|[Pred|A]]]],
	!,store_horn(Ind, K, R, [T|In], Out).


store_cnf(Ind,List):-
	replace_eFunc(List,List1),
	assertz(fol_cnf(Ind,List1)),!.

orphaned_func(Ind,List):-
	setof([e,N,L],sub_term([e,N,L],List),EFuncs),
	setof(L1,sub_term(L1,EFuncs),VarList),
	flatten(VarList,FlatVars),
	setof(X,member(u(X),FlatVars),Unumbers),
	findall(X,sub_term(u(X),List),ListVars),
	unique_funcs(ListVars,Unumbers,[],Uniques),
	Uniques\=[],
	assertz(warning(Ind,["Unique variables ",Uniques])),!.
orphaned_func(_,_):-!.

unique_funcs(_,[],Uniques,Uniques):-!.
unique_funcs(ListVars,[H|R],In,Out):-
	unique(H,ListVars),
	!,unique_funcs(ListVars,R,[H|In],Out).
unique_funcs(ListVars,[_|R],In,Out):-
	!,unique_funcs(ListVars,R,In,Out).
	

replace_eFunc(ListIn,ListOut):-
	setof([e,N,L],sub_term([e,N,L],ListIn),EFuncs),
	maplist(eFunc,EFuncs,Out),
	replace2(EFuncs,Out,ListIn,ListOut),!.
replace_eFunc(ListIn,ListIn):-!.

% Transforms skolem terms from '[e, N, ...]' into function syntax 'eN(...)'
eFunc([e,N,L],Term):-
	atomics_to_string([e,N],F),
	atom_string(A,F),
	flatten([A,L],Out),
	Term=..Out,
	(	outputfile(satchmo),
		sub_term(u(_), L),
%		length(L,Len),
%		length(NL,Len),
%		flatten([A,NL],Nout),
%		Term2=..Nout,
		asserta_once(skolems(Term))
	;	true)
	,!.
	
is_neg([s(not),_]).

sort_neg([],In,Out):-sort(In,Out),!.
sort_neg([[s(not),P]|R],In,Out):-
	!,sort_neg(R,[P|In],Out).

sort_pos([],false):-!.
sort_pos([R|[]],then(R)):-!.
sort_pos(R, then_or(R1)):-sort(R,R1),!.

% renames 'v(n)' variables to 'u(n)' variables 
re_standardize_vars(In,Out):-
	setof(X,sub_term(v(X),In),Vars),
	numberedVars(clausevar,u,Vars,[],Nvars),
	reverse(Nvars, NumVars),
	maplist(rsv2,Vars,VarsOrg),
	replace2(VarsOrg,NumVars,In,Out),
	mapUvars(VarsOrg,NumVars),!.
re_standardize_vars(In,In):-!.

rsv2(In,v(In)):-!.

mapUvars(Vs,Us):-
	skolem_mode(mapped),
	scopedEvar(E,[e,N,Ss]),
	nth1(I,Vs,E),
	nth1(I,Us,E1),
	replace2(Vs,Us,Ss,Ss1),
	assertz(mappedEvar(E1,[e,N,Ss1])),!.
mapUvars(_,_):-!.	

varclauses(In,Out):-
	setof(X,sub_term(v(X),In),Vars),
	maplist(rsv2,Vars,VarsOrg),
	length(VarsOrg,L),
	length(Ovars,L),
	numbervars(Ovars),
	replace2(VarsOrg,Ovars,In,Out),
	mapUvars(VarsOrg,Ovars),!.
varclauses(In,In):-!.	


find_dupl_axioms:-
	% Axiom = implication free axiom with Prolog variables, AxID = index in [...], FolInd = unique axiom number generated
	% It is assumed that the same axiom might have been given a different AxID, and might appear in different files

	% First find axioms occuring more than once
	findall([Axiom,[AxID,FolInd]], tpex(_,FolInd,Axiom,_,_,AxID,_),Bag),	% for each axiom, get Index and unique number
	findall(Axiom,tpex(_,_,Axiom,_,_,_,_),TPs),								% get just each axiom, list might contain doubles
	sort(TPs, TPs1),						% remove the doubles in the second list
	collate(TPs1,Bag,[],Doubles),			% collect in Doubles for each axiom the list of unique IDs
	length(Doubles,LD),
	LD>0,
	store_doubles(Doubles,[],Elim),
	asserta_once(redundant_axioms(Elim)),

	% Then find axiom indices occuring more than once
	findall([I, File], (fol(_,_,_,File,_,I,_),\+string_concat(_,"unmarked",I)),IFs),
	findall(X, (fol(_,_,_,_,_,X,_),\+string_concat(_,"unmarked",X)),Xs),
	sort(Xs,Xs1),
	collate(Xs1,IFs,[],DoubleFiles),
	findall([ID,F], (member([ID,F],DoubleFiles),length(F,LF),LF>1),Fs),
	\+Fs==[],
	assert(warning(-7,Fs)),!.
find_dupl_axioms:-!.


% i,i,i,o
collate([],_,In,In):-!.
collate([Axiom|Rest],IFs,In,Out):-
	findall(File, member([Axiom,File],IFs), Files),
	!,collate(Rest,IFs,[[Axiom,Files]|In],Out).


store_doubles([],Out,Out):-!.
store_doubles([[A,[F|FR]]|R],In,Out):-
	length([F|FR],FL),
	(	FL>1 ->
		assertz(warning(-5, info(A))),
		setof(X,member([_,X],FR),Eliminate),
		elim_doubles([F|FR]),
		flatten([Eliminate|In],In1),
		!, store_doubles(R, In1, Out)
	; !, store_doubles(R, In, Out))
	,!.	

elim_doubles([]):-!.
elim_doubles([[A2,F2]|R]):-
	atomic_list_concat(["%     ", A2, " / ", F2], Text),
	assertz(warning(-5, info(Text))),
	!, elim_doubles(R).



%% ---------------------
%% utilities
%% ---------------------

run2:-outputfile(sci),
	findall(X,fol_rule(_,rule(X,"\"-->\"",_)),Xs),
	sort(Xs,Xs2),
	allcons(Xs2,[],Bag),
	get_projectname(Name),
	string_concat(Name,"-sci.txt",FE),
	setup_call_cleanup(					%% ... it will overwrite the file with the same name when it is closed.
       open(FE, write, Out),
	   run3(Out,Bag),
	   close(Out)),!.
run2:-!.

allcons([],In,In):-!.
allcons([X|R],In,Out):-
	findall(Y,fol_rule(_,rule(X,"\"-->\"",Y)),Ys),
	flatten(Ys,Ys2),
	sort(Ys2,Ys3),
	as_pred(X,Xp),
	as_preds(Ys3,[], Yp),
	!,allcons(R,[[Xp,Yp]|In],Out).

as_preds([],In,In):-!.
as_preds([H|R],In,Out):-
	as_pred(H,HT),!,
	as_preds(R,[HT|In],Out).

as_pred(por(_,A1,Pred,A2,at,A3),p(Predt,A1t,A2t,A3t)):-
	astext(A1,A1t),
	astext(Pred,Predt),
	astext(A2,A2t),
	astext(A3,A3t),!.
as_pred(por(_,A1,Pred,A2),p(Predt,A1t,A2t)):-
	astext(A1,A1t),
	astext(Pred,Predt),
	astext(A2,A2t),!.
as_pred(por(_,A1,Pred),p(Predt,A1t)):-
	astext(A1,A1t),
	astext(Pred,Predt),!.

astext(s(X),X):-!.
astext(X,X):-!.


run3(_,[]):-!.
run3(Out,[[A,B]|R]):-
	write(Out,A),
	write(Out,"-->"),writeln(Out,B),
	!,run3(Out,R).
	
testcond(X,Y,Z):-
	fol_rule(_,rule(X,"\"-->\"",Y)),
	fol_rule(_,rule(X,"\"-->\"",Z)).

p_fol_rule(_,Rule,_,Out):-
	seen(Rule,Q1,F1),
	write(Out, "%1: "),
	write(Out, F1),
	write(Out, " "),
	writeln(Out, Q1),
	write(Out, "%1: "),
	write(Out, Rule),
	writeln(Out,"."),!.
p_fol_rule(Q,Rule,F,Out):-
    write(Out,Rule),
	writeln(Out,"."),
	asserta(seen(Rule,Q,F)),!.

increments(C,N,Y):-
	increm(C,N,[],Y),!.

increm(_,0,In,In):-!.
increm(C,N,In, Out):-
	N>0,
	increment(C,Y),
	plus(N,-1,N1),!,
	increm(C,N1,[Y|In],Out).
increm(C,N,In, Out):-
	N<0,
	decrement(C,Y),
	plus(N,1,N1),!,
	increm(C,N1,[Y|In],Out).

increment(C,Y):-					%% i, o	%% increment the counter identified by C
	counterValue(C,X),						%% retrieve the value of counter C
	retract(counter(C,X)),					%% delete counter C and its value
	plus(X,1,Y),							%% add 1 to the value of what was counter C
	asserta(counter(C,Y)),!.				%% recreate the counter with the new value

decrement(C,Y):-					%% i, o	%% decrement the counter identified by C
	counterValue(C,X),						%% retrieve the value of counter C
	retract(counter(C,X)),					%% delete counter C and its value
	plus(X,-1,Y),							%% substract 1 from the value of what was counter C
	asserta(counter(C,Y)),!.				%% recreate the counter with the new value

counterValue(C, Value):-			%% i,o	%% retrieves the value of a counter			
	counter(C,Value),!.						%% if the counter exist, take the value
counterValue(C, 0):-						%% if the counter does not yet exist, return zero
	asserta(counter(C,0)),!.					%% after creating the counter


asserta_once(A):-call(A),!.
asserta_once(A):-asserta(A),!.
	
assertz_once(A):-call(A),!.
assertz_once(A):-assertz(A),!.

leafs([E|L], R) :- !, (leafs(E, R) ; leafs(L, R)).
leafs(E, E) :- E \= [].

isListComp(X,X).
isListComp(X,Y):-memberNestList(X,Y).

isExtQuantified(X, In):-isListComp([s(exists),Z,_],In),member(X,Z).

isUniQuantified(X, In):-isListComp([s(forall),Z,_],In),member(X,Z).

isQuantifiedInByAs(Y,X,Z,[s(forall),Z,Y]):-isListComp([s(forall),Z,Y],X).
isQuantifiedInByAs(Y,X,Z,[s(exists),Z,Y]):-isListComp([s(exists),Z,Y],X).

isNotFurtherQuantifiedInByAs(Y,X,B,A):-
	isQuantifiedInByAs(Y,X,B,A), 
	\+isNotFurtherQuantifiedInByAs(_,Y,_,_),
	\+member(v(_),B).


memberNestList(H,[H|_]).
memberNestList(X,[H|_]):-memberNestList(X,H).
memberNestList(X,[_|T]):-memberNestList(X,T).


standardizeAllVars(In,Out):-	%% still issue with two deapest levels at same depth?
	setof([VarList,This],isNotFurtherQuantifiedInByAs(_,In,VarList,This),ToReplace),
%	ToReplace\=[],
	standardizeDeepestVars(ToReplace,[],Replaced),
	replaceDeepestVars(Replaced,In,Out1),
	!,
	standardizeAllVars(Out1,Out).
standardizeAllVars(In,In):-!.



standardizeDeepestVars([],In,In):-!.
standardizeDeepestVars([[H,_]|_],In,In):-
	allVvars(H),!,fail.
standardizeDeepestVars([[H,F]|R],In,Out):-
	numberedVars(qvar, v, H, [], Numbered),
	reverse(Numbered, NumVars),
	replace2(H,NumVars,F,Out1),!,
	standardizeDeepestVars(R,[[F,Out1]|In],Out).

allVvars([]):-!.
allVvars([v(_)|T]):-!,allVvars(T).


replaceDeepestVars([],In,In):-!.
replaceDeepestVars([[What,With]|R],In,Out):-
	asserta(oldNew([What],[With])),
	replace3(In,Out1),
	!,
	replaceDeepestVars(R,Out1,Out).


numberedVars(_,_,[],In,In):-!.
numberedVars(VarName,VarSymbol,[_|R],In,Out):-
	increment(VarName,N),
	T=..[VarSymbol,N],!,
	numberedVars(VarName,VarSymbol,R,[T|In],Out).



replace2(_, _, [], []):-!.
replace2([This], [With], This, With) :-!.	%% takes care of formulas starting with quantifier.
replace2(This, With, [H|T], [Ht|Tt]) :-
  ( nth1(Index, This, H), 	
	nth1(Index, With, Ht)
  -> true
  ;  is_list(H)
  -> replace2(This, With, H, Ht)
  ;  H = Ht
  ),
  replace2(This, With, T, Tt).


%% replace once an element in a nested list which is of any sort as determined in oldNew()
replace3([], []):-!.
replace3(What, With) :-
	oldNew([What],[With]),
	retractall(oldNew(_,_)),
	!.	%% takes care of formulas starting with quantifier.
replace3([H|T], [Ht|Tt]) :-
	oldNew(What,With),
	nth1(Index, What, H), 	
	nth1(Index, With, Ht),
	retractall(oldNew(_,_)),!,
	replace3(T,Tt).
replace3([H|T], [Ht|Tt]) :-
   (is_list(H)
  -> replace3(H, Ht)
  ;  H = Ht
  ),!,
  replace3(T, Tt).


list_assert_once(_, _, []):-!.
list_assert_once(AZ, Name, [H|R]):-
	X =..[Name,H],
	( AZ == a,
	  asserta_once(X)
	  ;
	  assertz_once(X) ),!,
	list_assert_once(AZ,Name,R).
	
remove_element(_,[],In,In):-!.
remove_element(E,[E|R],In,Out):-!,
	remove_element(E,R,In,Out).
remove_element(E,[H|R],In,Out):-!,
	remove_element(E,R,[H|In],Out).
	
unique(X, L) :-
    nth0(_, L, X, R),
    \+ member(X, R).


replace(V, V) :-
    % pass vars through 
    var(V), !.     
replace(A, A) :- 
    % pass atoms through 
    atomic(A), !.
replace([], []) :- 
    % pass empty lists through
    !.
replace([X|Xs], [Y|Ys]) :-
    % recursively enter non-empty lists
    !, 
    replace(X, Y),
    replace(Xs, Ys).
replace(s(X), NX) :-
    !, 
    replace(X, NX).
replace(T, NT) :-
    % finally, recursively enter any as yet unmatched compound term
    T =.. [F|AL],
    replace(AL, NAL),
    NT =.. [F|NAL].


replace_cf([s(not),[Y|Yr]],[-1|[Ys|Yrs]]) :-
	predname(Y),
	!,
	replace_cf(Y, Ys),
    replace_cf(Yr, Yrs).
replace_cf([X|Xs], [0|[Y|Ys]]) :-
	predname(X),
    !, 
    replace_cf(X, Y),
    replace_cf(Xs, Ys).
replace_cf(V, V) :-
    % pass vars through 
    var(V), !.     
replace_cf(A, A) :- 
    % pass atoms through 
    atomic(A), !.
replace_cf([], []) :- 
    % pass empty lists through
    !.
replace_cf([X|Xs], [Y|Ys]) :-
    % recursively enter non-empty lists
    !, 
    replace_cf(X, Y),
    replace_cf(Xs, Ys).
replace_cf(s(X), NX) :-
    !, 
    replace_cf(X, NX).
replace_cf(e(N), sk(N)) :-
	!.
replace_cf(T, NT) :-
    % finally, recursively enter any as yet unmatched compound term
    T =.. [F|AL],
	(	atom_concat(e,Na,F)
			->  replace_cf(AL,NAL),
				atom_number(Na,N),
%				NT =.. [sk|[N|NAL]]
%				NT = [sk|[N|[NAL]]]
%				NT = [[sk,N],[NAL]]
				atom_concat(sk,N,SkN),
				NT = [SkN | NAL]
	;	replace_cf(AL, NAL),
		NT =.. [F|NAL]
	).

% Returns what is between the first occurrence in 'String' of 'Left' and 'Right' as 'Between' and 
% what remains of 'String' when 'Left', 'Between' and 'Right' are removed as 'Removed'.
between(Left, Right, String, Between, NoBetween, Removed):- 					% i,i,i,o,i,o
	sub_string(String,BeforeLeft,LengthLeft,_,Left),
	sub_string(String,_,LengthRight,AfterRight,Right),
	plus(BeforeLeft,LengthLeft,BeforeBetween),
	plus(AfterRight,LengthRight,AfterBetween),
	sub_string(String,BeforeBetween,_,AfterBetween,BetweenTry),
	(	BetweenTry=="",
		Between=NoBetween,
		Removed=String
	;	Between=BetweenTry,
		sub_string(String, 0, BeforeLeft, _, WithoutBefore),
		sub_string(String, _, AfterRight, 0, WithoutAfter),
		string_concat(WithoutBefore,WithoutAfter,Removed)
	),
	!.
between(_,_,String,NoBetween,NoBetween,String):-!.


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
