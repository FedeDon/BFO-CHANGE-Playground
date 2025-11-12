
@echo off
set INPUT=C:\Users\Federico\Code-Projects\FedeDon-Github-Repos\Ontology-Tradecraft\myinput.txt

echo Starting Parser and Reasoner execution...
echo Using input file: %INPUT%

:: Kill any lingering SWI-Prolog processes
taskkill /IM swipl.exe /F >nul 2>&1

:: Run parser with forced inputdata override
echo Running parser.pl...
echo. | swipl -s "BFO2020style-CLIFparser.pl" -g "retractall(inputdata(_)), asserta(inputdata('%INPUT%')), run, halt"

:: Run reasoner with forced inputdata override
echo Running reasoner.pl...
echo. | swipl -s "BFO2020style-CLIFreasoner - Working20250415.pl" -g "retractall(inputdata(_)), asserta(inputdata('%INPUT%')), run, halt"

echo Batch execution completed!
pause