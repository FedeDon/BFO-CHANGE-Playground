# DOCUMENTATION 

## PARSING

### PARSER FILE
Parser created by Werner to Transform the CLIF file into Kowalski Rules (Horn Clauses readable by SWI-Prolog), and the kow()  predicate is everywhere. The kow() transforms FOL into propositional logic sentences. 
The parser checks the syntax only. It is enough to check if there are tautologies or not , plus more

The parser is a .pl file that is just invoked and automatically gets the BFO2020.cl file and the change.cl file as inputs. The output is generated within the BCHANGE-comments.txt file, the BCHANGE-cf.txt file and some others.
There might be Error and Warning errors. For example: all these CLIF rules are then translated by the parser into Kowalski rules, and the tautologies are listed in the Warning messages. 

The parser considers within the scope of an individual axiom all symbols that are used as arguments in a predicate within that axiom and that are not quantified, to be constants. That behavior has not changed. 

Prolog is fragile to encodings , so watch out for invisible character in your editor or copy pasting from other note editors.
Prolog suggested version  9.2.9/1    
Unique name assumption. Prolog assumes that different constant names refer to different entities, UNLIKE OWL or CLIF. You can still  unify constants in Prolog ex: =(john , jim). this is dues to the fact that  Closed World Assumption implies Unique name assumption  (Prolog has CWA). 


### KOWALSKI FILE
The BCHANGE-kowalski.txt results when all the axioms are read by the parser and translated into Kowalski rules that then the reasoner can work on. "The are actually easy to interpret". The initial big predicate `r()` wraps an entire rule or axiom. For example:
`r(1,1,[],[],"BFOCE-ett-01",kow(if([['exists-throughout',A,B]]),then([particular,A]))).`
The first part `1,1,[],[]` can be ignored, it is just some indexing that increase the efficiency of the reasoner. Then we have a string with the ontology name and the axiom ID. Then the actual rule inside the `kow()` predicate, which is a conditional statement composed of prolog lists, that can be understood as sentences with predicates and arguments, like `['exists-throughout',A,B]` stands for the CLIF phrasing `(exists-throughout A B)`.
IN the Kowalski rules there is no IFF connective, so an original CLIF axioms is split into two sentences IF and ONLY-IF connectives. 
Inside some of these conditionals which are inside the `kow()` predicates there are consequents that are disjuncts, and this is indicated with 
`kow(if([[list]]), then-or([[list]]))`
This terms like `if()` and `then-or()` are not part of the Prolog vocabulary, but something construed ad hoc as a Prolog predicate. 
What the kow() predicates d is to convert predicate logic sentences in propositional logic sentences. There is a nuance with existentially quantified sentences, since skolemization must be done there. In this translation done by the parser "the semantics changes a little bit", and not all is completely valid overall, but the advantage is that if there is an inconsistency in the automatically translated axiom outputted by the parser, then there is also an inconsistency in the original axiom in CLIF.
A certain rule in this format ends with a `false`, since it is a negation inside a universal quantifier. It signals that the conditions in the formula cannot be all satified at the same time. For example, this rule says that spatial regions cannot change, since you cannot both be a spatial region and also change:
`r(18,2,[],[],"BFOCE-cha-02",kow(if([['happens-to',A,B,C],['instance-of',B,'spatial-region',C]]),false)).`
After some hundreds of line of translated rules, we get to lines like
```lisp
sk_use(206,"BFO-cop-1",[],[714,715,716,717,718,719,720,721,722,723,724,725]).
p_in('exists-throughout',v,1,"BFOCE-ett-01").
```
That can be ignored, since it is just information used by the reasoner, like Skolem constants and other details. 

For decidability reasons, the CLIF axioms are transformed via Skolemization, which does not guarantee logical equivalence with the original axioms.
`[e,1, [A,B]]`  is a  syntax with Prolog lists that exemplifies a Skolemization, where a CLIF axiom was transformed in a readable way for SWI-Prolog. Where the CLIF axiom had existentially quantified variables, those are substituted with special functions.
Ex:   sk176  `[e,166,[a,[e,156,[r1,t1]],t1]`
Here `e` is the function, and the occurrences of `e` are not the same function. In fact, "e" is used a placeholder for a precise names of various Skolem functions.




### PARSER INIT FILE
The CLIFParserinit.txt is a file read as input by the parser and we can write our particular scenarios here, so we can test the axioms we wrote in the .cl file. This file is quite heavily documented with comments. At the beginning we specify which ontology we are working on, and so which axioms will be tested with the particular scenarios. It is a way of importing ontologies, so to speak:
```lisp
ontology("BFOCE",["*.clc"]).	% Declare all filenames with extention 'clc' as belonging to BFOCE
ontology("BFO",["*.cl"]).
```
All the .cl files must be in the same directory to be run. The .cl  and .clc   file extensions "have no meaning", and they are not universally recognized standard. Nonetheless, the extension must be specified for the parser to pick the right files, so do not change that without changing the call of the files.
Importantly, a following line says which ontology is using which ontology, so what axioms refer to other axioms. There is a special Prolog predicate for that, whse second argument is a list of the ontologies that are used, which can be many. In this case, the bfo:Change axioms use the BFO202 axioms:
`ont_uses("BFOCE", ["BFO"]).`
After this, there are lines specifying how much output do we want, and this can be adjusted to the computer we are using, if fast or not.
Cool thing: this parser can statistically try to tell you if you misspelled something, or f there are some novel and strange occurrences compared to the rest of he file. An Editing distance algorithms is used, among others. This is very handy for debugging. For example: no name of universal in BFO has less than four characters, so a warning is fired when you use a shorter name.
Showcase of various functions of the parser and how fast they MUST be: typo detection (0.95 sec),  minimum constant length (1sec) , rar term use (2sec)  etc...
If you use a relationship, it must be in the cl:outdiscourse, as an implemented requirement, and we just used "happen-throughout" instead of "happens-throughout".
Do not touch these predicates and formulas, as the comment in the file says . 




The parameter

              minimum_constant_length(n)

where ‘n’ is an integer does not change that behavior, but functions as an indicator to suggest that some symbols used might have meant to be variables, but were forgotten to be quantified.

 The error is now marked as ‘Symbol used both as quantified variable and as constant in the same axiom’, including what symbol it pertains to, e.g. ‘s(t)’, meaning: the symbol t is used both as quantified variable and as constant.

The arguments of predicates asserted in the scenario-input provided to the reasoner via the files referenced in the inputdata-parameter were, and still are, interpreted as being all constants, independent of their length. When scenario-input is provided through CLIF, then the interpretation of the parser is used, i.e. as specified in the first paragraph of this section.



### VOCABULARY FILE
The BCHANGEvocabulary.txt is an output file file gives you a list of all the constant used in the other files. For example, we find lines like
`[s(instance-of),v,s(change),v]`  
Where `v` is for a variable , while `s(...)` says that there is a specific entity referred inside the parentheses, like the relation instance-of or the universal Change. There is also a long list of variables used, like
```lisp
s(fill)
s(t3)
s(end)
s(start)
```


 
### REASONER FILE
The file with the reasoner is another Prolog file, called BFO2020style-CLIFreasoner - Working20250415.pl. The reasoner can modify some of its parameters, like the Skolem Cycles, with a `"CLIFreasonerinit.txt"` file, that is used to tell which files to open, like other "init" files particular scenarios, and files that have name `"*-kowalski.txt"`, that for us are the axioms transformed by the parse . If you give it something that is consistent, nothing will happen for a long time (until it hits a threshold).
Now we open a `mytest-input.txt` file, where particular scenarios are already written. By default, they are all commented out, and deleting the Prolog comment symbols will make them actionable by the reasoner. 
To start the reasoner, we just click on it, and SWI-Prolog begins to run. The Output of the reasoner is an excel file, "CLIFreasoner-inconsistency-proof.csv", that is self explanatory, and lists all the facts in this model, or antimodel, that were inputted or deduced as existing, numbering them in column B with an ID. It is easier to read this file from bottom up, where the input facts are used, while inconsistencies, if any, are on the top.
As an example, check the above-mentioned ready-made bad fact that will cause an inconsistency and an excel file with the inconsistency is generated, as expected:  input rows are for the premises used and the lines in which they live is reported in a column; facts 7 and 10 are inconsistent with one another, as column M states with the value "inc",and column E states "inconsistency". On the same column M you see "mpp" is for Arrow-elimination rule, "modus ponendo ponens". The prover can make assumptions too. The index "21", seen in column K, is for the rule used to generate the inconsistency, and of course it is a rule within the `posax()` predicate in the BCHANGE-cf.txt file.
<img width="1666" height="356" alt="Screenshot 2025-10-29 192611" src="https://github.com/user-attachments/assets/6bfbb43f-ec78-4562-a4db-53fb8470a619" />


If no inconsistency is found, NO inconsistency csv file is generated. In another way, the reasoner will create a smaller model just for the input. We presently do not know if the reasoner is powerful enough to generate a complete model, or just some model that satisfy the input and axioms. 
The methodology is this: we write axioms, we create particular scenarios and we hypothesize whether they will fail or not. Then the reasoner will give the answer, and we can mark the result on a comment line, like "should fail and does...". Then we backtrack what we modeled and see why our expectations were not met, maybe modifying the axioms in question. 
If an excel file that was outputted is of interest to you, change its name, otherwise at the next run the reasoner will overwrite it!  
"sk1" are the individuals generated in the reasoner for the assumptions. There is a separate file that tells you all the "sk-" . There is a specific CLIFreasoner-main_skolems.txt file for all the Skolem functions generated in the reasoning, and usually just a fraction of them is used in the proof of the inconsistency excel file. This depends on the Skolem cycles, which can be set prior to the reasoning.
The Reasoner tries to use as fewer variables as possible. 



